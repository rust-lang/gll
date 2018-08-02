use ordermap::OrderMap;
use std::cell::RefCell;
use std::char;
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fmt;
use std::fmt::Write as FmtWrite;
use std::io::Write;
use std::mem;
use std::ops::{Add, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};
use std::rc::Rc;
use ParseLabelKind;

pub struct Grammar<Pat> {
    rules: OrderMap<String, RuleWithNamedFields<Pat>>,
}

impl<Pat> Grammar<Pat> {
    pub fn new() -> Self {
        Grammar {
            rules: OrderMap::new(),
        }
    }
    pub fn add_rule(&mut self, name: &str, rule: RuleWithNamedFields<Pat>) {
        self.rules.insert(name.to_string(), rule);
    }
}

pub struct RuleWithNamedFields<Pat> {
    rule: Rc<Rule<Pat>>,
    fields: OrderMap<String, Vec<usize>>,
}

impl<Pat: PartialEq> RuleWithNamedFields<Pat> {
    pub fn empty() -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::Empty),
            fields: OrderMap::new(),
        }
    }
    pub fn match_(pat: Pat) -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::Match(pat)),
            fields: OrderMap::new(),
        }
    }
    pub fn not_match(pat: Pat) -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::NotMatch(pat)),
            fields: OrderMap::new(),
        }
    }
    pub fn call(call: String) -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::Call(call)),
            fields: OrderMap::new(),
        }
    }
    pub fn or(rules: Vec<Self>) -> Self {
        let mut fields = OrderMap::new();
        let rules = rules
            .into_iter()
            .enumerate()
            .map(|(i, mut rule)| {
                for (name, path) in &mut rule.fields {
                    assert!(!fields.contains_key(name), "duplicate field {}", name);
                    path.insert(0, i);
                }
                fields.extend(rule.fields);

                rule.rule
            })
            .collect();
        RuleWithNamedFields {
            rule: Rc::new(Rule::Or(rules)),
            fields,
        }
    }
    pub fn with_field_name(mut self, name: &str) -> Self {
        match &*self.rule {
            Rule::RepeatMany(rule) => match **rule {
                Rule::Match(_) | Rule::Call(_) => {}
                _ => unimplemented!(),
            },
            Rule::Match(_) | Rule::Call(_) => {}
            _ => unimplemented!(),
        }
        self.fields.insert(name.to_string(), vec![]);
        self
    }
    pub fn then(mut self, mut other: Self) -> Self {
        if *self.rule == Rule::Empty && self.fields.is_empty() {
            return other;
        }
        if *other.rule == Rule::Empty && other.fields.is_empty() {
            return self;
        }
        for path in self.fields.values_mut() {
            path.insert(0, 0);
        }
        for (name, path) in &mut other.fields {
            assert!(!self.fields.contains_key(name), "duplicate field {}", name);
            path.insert(0, 1);
        }
        self.fields.extend(other.fields);
        self.rule = Rc::new(Rule::Concat([self.rule, other.rule]));
        self
    }
    pub fn opt(mut self) -> Self {
        for path in self.fields.values_mut() {
            path.insert(0, 0);
        }
        self.rule = Rc::new(Rule::Opt(self.rule));
        self
    }
    pub fn repeat_many(mut self) -> Self {
        for path in self.fields.values_mut() {
            path.insert(0, 0);
        }
        self.rule = Rc::new(Rule::RepeatMany(self.rule));
        self
    }
    pub fn repeat_more(mut self) -> Self {
        for path in self.fields.values_mut() {
            path.insert(0, 0);
        }
        self.rule = Rc::new(Rule::RepeatMore(self.rule));
        self
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rule<Pat> {
    Empty,
    Match(Pat),
    NotMatch(Pat),
    Call(String),

    Concat([Rc<Rule<Pat>>; 2]),
    Or(Vec<Rc<Rule<Pat>>>),

    Opt(Rc<Rule<Pat>>),
    RepeatMany(Rc<Rule<Pat>>),
    RepeatMore(Rc<Rule<Pat>>),
}

impl<Pat: Ord + ToRustSrc> Rule<Pat> {
    fn field_type(&self, path: &[usize]) -> String {
        match self {
            Rule::Empty | Rule::Match(_) | Rule::NotMatch(_) => {
                assert_eq!(path, []);
                "()".to_string()
            }
            Rule::Call(r) => format!("{}<'a, 'b, 'i>", r),
            Rule::Concat(rules) => rules[path[0]].field_type(&path[1..]),
            Rule::Or(rules) => rules[path[0]].field_type(&path[1..]),
            Rule::Opt(rule) => [rule][path[0]].field_type(&path[1..]),
            Rule::RepeatMany(rule) | Rule::RepeatMore(rule) => {
                assert_eq!(path, []);
                format!("[{}]", rule.field_type(&[]))
            }
        }
    }
    fn field_is_refutable(&self, path: &[usize]) -> bool {
        match self {
            Rule::Empty
            | Rule::Match(_)
            | Rule::NotMatch(_)
            | Rule::Call(_)
            | Rule::RepeatMany(_)
            | Rule::RepeatMore(_) => false,
            Rule::Concat(rules) => rules[path[0]].field_is_refutable(&path[1..]),
            Rule::Or(..) | Rule::Opt(_) => true,
        }
    }
    fn parse_label(
        self: &Rc<Self>,
        parse_labels: &RefCell<BTreeMap<Rc<Self>, (ParseLabel, ParseLabelKind<ParseLabel>)>>,
    ) -> ParseLabel {
        if let Some((label, _)) = parse_labels.borrow().get(self) {
            return label.clone();
        }
        let (label, kind) = match &**self {
            Rule::Empty => (ParseLabel("()".to_string()), ParseLabelKind::Opaque),
            Rule::Match(pat) => (ParseLabel(pat.to_rust_src()), ParseLabelKind::Opaque),
            Rule::NotMatch(pat) => (
                ParseLabel(format!("!{}", pat.to_rust_src())),
                ParseLabelKind::Opaque,
            ),
            Rule::Call(r) => return ParseLabel(r.clone()),
            Rule::Concat([left, right]) => {
                let left = left.parse_label(parse_labels);
                let right = right.parse_label(parse_labels);

                (
                    ParseLabel(format!("({} {})", left.0, right.0)),
                    ParseLabelKind::Binary(left, right),
                )
            }
            Rule::Or(rules) => {
                assert!(rules.len() > 1);
                let mut s = String::from("(");
                for (i, rule) in rules.iter().enumerate() {
                    if i > 0 {
                        s.push_str(" | ");
                    }
                    s.push_str(&rule.parse_label(parse_labels).0);
                }
                s.push(')');
                (ParseLabel(s), ParseLabelKind::Choice)
            }
            Rule::Opt(rule) => {
                let label = rule.parse_label(parse_labels);
                (
                    ParseLabel(format!("({}?)", label.0)),
                    ParseLabelKind::Opt {
                        none: Rc::new(Rule::Empty).parse_label(parse_labels),
                        some: label,
                    },
                )
            }
            Rule::RepeatMany(element) | Rule::RepeatMore(element) => {
                let element_label = element.parse_label(parse_labels);
                let label_many = ParseLabel(format!("({}*)", element_label.0));
                let label_more = ParseLabel(format!("({}+)", element_label.0));
                let kind_many = ParseLabelKind::Opt {
                    none: Rc::new(Rule::Empty).parse_label(parse_labels),
                    some: label_more.clone(),
                };
                let kind_more = ParseLabelKind::Binary(element_label, label_many.clone());
                assert!(
                    parse_labels
                        .borrow_mut()
                        .insert(
                            Rc::new(Rule::RepeatMany(element.clone())),
                            (label_many, kind_many)
                        )
                        .is_none()
                );
                assert!(
                    parse_labels
                        .borrow_mut()
                        .insert(
                            Rc::new(Rule::RepeatMore(element.clone())),
                            (label_more, kind_more)
                        )
                        .is_none()
                );
                return self.parse_label(parse_labels);
            }
        };
        assert!(
            parse_labels
                .borrow_mut()
                .insert(self.clone(), (label.clone(), kind))
                .is_none()
        );
        label
    }
}

pub trait ToRustSrc {
    fn to_rust_src(&self) -> String;
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Pat<S, C> {
    String(S),
    Range(C, C),
}

impl<'a> From<&'a str> for Pat<&'a str, char> {
    fn from(s: &'a str) -> Self {
        Pat::String(s)
    }
}

impl<'a> From<RangeInclusive<char>> for Pat<&'a str, char> {
    fn from(range: RangeInclusive<char>) -> Self {
        Pat::Range(*range.start(), *range.end())
    }
}

impl<'a> From<RangeToInclusive<char>> for Pat<&'a str, char> {
    fn from(range: RangeToInclusive<char>) -> Self {
        Self::from('\0'..=range.end)
    }
}

impl<'a> From<Range<char>> for Pat<&'a str, char> {
    fn from(range: Range<char>) -> Self {
        Self::from(range.start..=char::try_from(range.end as u32 - 1).unwrap())
    }
}

impl<'a> From<RangeFrom<char>> for Pat<&'a str, char> {
    fn from(range: RangeFrom<char>) -> Self {
        Self::from(range.start..=char::MAX)
    }
}

impl<'a> From<RangeTo<char>> for Pat<&'a str, char> {
    fn from(range: RangeTo<char>) -> Self {
        Self::from('\0'..range.end)
    }
}

impl<'a> From<RangeFull> for Pat<&'a str, char> {
    fn from(_: RangeFull) -> Self {
        Self::from('\0'..)
    }
}

impl<S: fmt::Debug, C: fmt::Debug> ToRustSrc for Pat<S, C> {
    fn to_rust_src(&self) -> String {
        match self {
            Pat::String(s) => format!("{:?}", s),
            Pat::Range(start, end) => format!("{:?}", start..=end),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ParseLabel(String);

impl fmt::Display for ParseLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "P!({})", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct CodeLabel(String);

impl fmt::Display for CodeLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "_C::{}", self.0)
    }
}

pub macro grammar {
    (@rule_tok { $($rule:tt)* }) => {
        grammar!(@rule [$($rule)*] () [])
    },
    (@rule_tok $rule:ident) => {
        RuleWithNamedFields::call(stringify!($rule).to_string())
    },
    (@rule_tok $pat:expr) => {
        RuleWithNamedFields::match_(Pat::from($pat))
    },
    (@rule [] ($current:expr) []) => { $current },
    (@rule [] ($current:expr) [$($rules:expr)+]) => {
        RuleWithNamedFields::or(vec![$($rules,)+ $current])
    },
    (@rule [$($input:tt)*] () [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] (RuleWithNamedFields::empty()) [$($rules)*])
    },
    (@rule [| $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] () [$($rules)* $current])
    },
    (@rule [! $input0:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            RuleWithNamedFields::not_match(Pat::from($input0))
        )) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt ? $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).with_field_name(stringify!($name)).opt()
        )) [$($rules)*])
    },
    (@rule [$input0:tt ? $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).opt()
        )) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt * $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_many().with_field_name(stringify!($name))
        )) [$($rules)*])
    },
    (@rule [$input0:tt * $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_many()
        )) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt + $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_more().with_field_name(stringify!($name))
        )) [$($rules)*])
    },
    (@rule [$input0:tt + $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_more()
        )) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).with_field_name(stringify!($name))
        )) [$($rules)*])
    },
    (@rule [$input0:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0)
        )) [$($rules)*])
    },
    ($($rule_name:ident = { $($rule:tt)* };)*) => ({
        let mut grammar = Grammar::new();
        $(grammar.add_rule(stringify!($rule_name), grammar!(@rule_tok { $($rule)* }));)*
        grammar
    })
}

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<Pat: Ord + ToRustSrc> Grammar<Pat> {
    pub fn generate(&mut self, out: &mut Write) {
        macro put($($x:expr),*) {{ $(write!(out, "{}", $x).unwrap();)* }}

        let parse_labels = RefCell::new(BTreeMap::new());
        let mut named_parse_labels = vec![];
        let mut code_labels = vec![];

        put!("extern crate gll;

use self::gll::{Call, Continuation, ParseLabel, CodeLabel, ParseLabelKind, ParseNode, Range};
use std::fmt;
use std::marker::PhantomData;

pub type Parser<'a, 'i> = gll::Parser<'i, _P, _C, &'a gll::Str>;

#[derive(Debug)]
pub struct Ambiguity;

pub struct Handle<'a, 'b: 'a, 'i: 'a, T: ?Sized> {
    pub node: ParseNode<'i, _P>,
    pub parser: &'a Parser<'b, 'i>,
    _marker: PhantomData<T>,
}

impl<'a, 'b, 'i, T: ?Sized> Copy for Handle<'a, 'b, 'i, T> {}

impl<'a, 'b, 'i, T: ?Sized> Clone for Handle<'a, 'b, 'i, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, 'b, 'i> fmt::Debug for Handle<'a, 'b, 'i, ()> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            \"{}..{}\",
            self.node.range.start(),
            self.node.range.end()
        )
    }
}

impl<'a, 'b, 'i, T> fmt::Debug for Handle<'a, 'b, 'i, [T]>
    where Handle<'a, 'b, 'i, T>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            \"{}..{} => \",
            self.node.range.start(),
            self.node.range.end()
        )?;
        f.debug_list().entries(*self).finish()
    }
}

impl<'a, 'b, 'i, T> Iterator for Handle<'a, 'b, 'i, [T]> {
    type Item = Result<Handle<'a, 'b, 'i, T>, Ambiguity>;
    fn next(&mut self) -> Option<Self::Item> {
        if let ParseLabelKind::Opt { none, .. } = self.node.l.kind() {
            let mut opt_children = self.parser.sppf.unary_children(self.node);
            let opt_child = opt_children.next().unwrap();
            if opt_children.next().is_some() {
                return Some(Err(Ambiguity));
            }
            if opt_child.l == none {
                return None;
            }
            self.node = opt_child;
        }
        let mut children = self.parser.sppf.binary_children(self.node);
        let (first, rest) = children.next().unwrap();
        if children.next().is_none() {
            self.node = rest;
            Some(Ok(Handle {
                node: first,
                parser: self.parser,
                _marker: PhantomData,
            }))
        } else {
            Some(Err(Ambiguity))
        }
    }
}");
        for (name, rule) in &self.rules {
            put!("

pub struct ", name, "<'a, 'b: 'a, 'i: 'a> {");
            for (field_name, path) in &rule.fields {
                let refutable = rule.rule.field_is_refutable(path);
                put!("
    pub ", field_name, ": ");
                if refutable {
                    put!("Option<");
                }
                put!("Handle<'a, 'b, 'i, ", rule.rule.field_type(path), ">");
                if refutable {
                    put!(">");
                }
                put!(",");
            }
            if rule.fields.is_empty() {
                put!("
    _marker: PhantomData<(&'a (), &'b (), &'i ())>,");
            }
            put!("
}

impl<'a, 'b, 'i> ", name, "<'a, 'b, 'i> {
    pub fn parse(p: &'a mut Parser<'b, 'i>, range: Range<'i>) -> Result<Handle<'a, 'b, 'i, Self>, ()> {
        let call = Call {
            callee: ", CodeLabel(name.clone()), ",
            range,
        };
        if !p.gss.calls.contains_key(&call) {
            p.gss.threads.spawn(
                Continuation {
                    code: call.callee,
                    frame: call,
                    state: 0,
                },
                call.range,
            );
            parse(p);
        }
        if let Some(range) = p.gss.longest_result(call) {
            return Ok(Handle {
                node: ParseNode { l: ", ParseLabel(name.clone()), ", range },
                parser: p,
                _marker: PhantomData,
            });
        }
        Err(())
    }
}

impl<'a, 'b, 'i> fmt::Debug for ", name, "<'a, 'b, 'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut d = f.debug_struct(\"", name,"\");");
            for (field_name, path) in &rule.fields {
                if rule.rule.field_is_refutable(path) {
                    put!("
        if let Some(ref field) = self.", field_name, "{
            d.field(\"", field_name,"\", field);
        }");
                } else {
                put!("
        d.field(\"", field_name,"\", &self.", field_name,");");
                }
            }
            put!("
        d.finish()
    }
}");
            if rule.fields.is_empty() {
                put!("

impl<'a, 'b, 'i> fmt::Debug for Handle<'a, 'b, 'i, ", name, "<'a, 'b, 'i>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, \"{}..{}\", self.node.range.start(), self.node.range.end())
    }
}");
                continue;
            }
            put!("

impl<'a, 'b, 'i> fmt::Debug for Handle<'a, 'b, 'i, ", name, "<'a, 'b, 'i>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            \"{}..{} => \",
            self.node.range.start(),
            self.node.range.end()
        )?;
        for (i, _x) in self.many().enumerate() {
            if i > 0 {
                write!(f, \" | \")?;
            }
            fmt::Debug::fmt(&_x, f)?;
        }
        Ok(())
    }
}

impl<'a, 'b, 'i> Handle<'a, 'b, 'i, ", name, "<'a, 'b, 'i>> {
    pub fn one(self) -> Result<", name, "<'a, 'b, 'i>, Ambiguity> {
        let mut iter = self.many();
        let first = iter.next().unwrap();
        if iter.next().is_none() {
            Ok(first)
        } else {
            Err(Ambiguity)
        }
    }
    pub fn many(self) -> impl Iterator<Item = ", name, "<'a, 'b, 'i>> {
        self.parser.sppf.unary_children(self.node).flat_map(move |node| {
            ", rule.rule.generate_traverse("node", false, &parse_labels), "
        }).map(move |_r| ", name, " {");
            for (field_name, path) in &rule.fields {
                if rule.rule.field_is_refutable(path) {
                    put!("
            ", field_name, ": _r");
                    for p in path {
                        put!(" .", p);
                    }
                    put!(".map(|node| Handle {
                node,
                parser: self.parser,
                _marker: PhantomData,
            }),");
                } else {
                    put!("
            ", field_name, ": Handle {
                node: _r");
                    for p in path {
                        put!(" .", p);
                    }
                    put!(",
                parser: self.parser,
                _marker: PhantomData,
            },");
                }
            }
            if rule.fields.is_empty() {
                put!("
            _marker: PhantomData,");
            }
            put!("
        })
    }
}");
        }
        put!("
fn parse(p: &mut Parser) {
    while let Some(Call { callee: mut c, range: _range }) = p.gss.threads.steal() {
        match c.code {");
        for (name, rule) in &self.rules {
            let parse_labels = if rule.fields.is_empty() {
                None
            } else {
                Some(&parse_labels)
            };
            code_labels.push(CodeLabel(name.clone()));
            let parse_label = ParseLabel(name.clone());
            let kind = if let Some(parse_labels) = parse_labels {
                ParseLabelKind::Alias(rule.rule.parse_label(parse_labels))
            } else {
                ParseLabelKind::Opaque
            };
            named_parse_labels.push((parse_label.clone(), kind));

            put!((
                reify_as(CodeLabel(name.clone())) +
                rule.rule.clone().generate_parse(parse_labels) +
                ret()
            )(Continuation {
                code_labels: &mut code_labels,
                code_label_prefix: name,
                code_label_counter: &mut 0,
                code_label_arms: &mut String::new(),
                code: Code::Inline(String::new()),
                nested_frames: vec![],
            }).code_label_arms);
        }
        put!("
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum _P {");
        for i in 0..named_parse_labels.len() + parse_labels.borrow().len() {
            put!(
                "
    _", i, ",");
        }
        put!("
}

macro P {");
        for (i, (l, _)) in named_parse_labels.iter().chain(parse_labels.borrow().values()).enumerate() {
            if i != 0 {
                put!(",");
            }
            put!("
    (", l.0, ") => (_P::_", i, ")");
        }
        put!("
}

impl fmt::Display for _P {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match *self {");
        for (l, _) in named_parse_labels.iter().chain(parse_labels.borrow().values()) {
            put!("
            ", l, " => \"", l.0.escape_default(), "\",");
        }
        put!("
        };
        write!(f, \"{}\", s)
    }
}

impl ParseLabel for _P {
    fn kind(self) -> ParseLabelKind<Self> {
        match self {");
        for (label, kind) in named_parse_labels.iter().chain(parse_labels.borrow().values()) {
            put!("
                ", label, " => ParseLabelKind::", kind, ",");
        }
        put!("
        }
    }
    fn from_usize(i: usize) -> Self {
        match i {");

        for i in 0..named_parse_labels.len() + parse_labels.into_inner().len() {
            put!("
            ", i, " => _P::_", i, ",");
        }
        put!("
            _ => unreachable!(),
        }
    }
    fn to_usize(self) -> usize {
        self as usize
    }
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum _C {");
        for s in code_labels {
            put!("
    ", s.0, ",");
        }
        put!("
}

impl CodeLabel for _C {}
");
    }
}

#[must_use]
struct Continuation<'a> {
    code_labels: &'a mut Vec<CodeLabel>,
    code_label_prefix: &'a str,
    code_label_counter: &'a mut usize,
    code_label_arms: &'a mut String,
    code: Code,
    nested_frames: Vec<Option<CodeLabel>>,
}

#[derive(Clone)]
enum Code {
    Inline(String),
    Label(CodeLabel),
}

impl<'a> Continuation<'a> {
    fn next_code_label(&mut self) -> CodeLabel {
        *self.code_label_counter += 1;
        let label = CodeLabel(format!(
            "{}__{}",
            self.code_label_prefix, self.code_label_counter
        ));
        self.code_labels.push(label.clone());
        label
    }

    fn clone(&mut self) -> Continuation {
        Continuation {
            code_labels: self.code_labels,
            code_label_prefix: self.code_label_prefix,
            code_label_counter: self.code_label_counter,
            code_label_arms: self.code_label_arms,
            code: self.code.clone(),
            nested_frames: self.nested_frames.clone(),
        }
    }

    fn to_inline(&mut self) -> &mut String {
        match self.code {
            Code::Inline(ref mut code) => code,
            Code::Label(ref label) => {
                self.code = Code::Inline(format!(
                    "
                c.code = {};
                p.gss.threads.spawn(c, _range);",
                    label
                ));
                self.to_inline()
            }
        }
    }

    fn to_label(&mut self) -> &mut CodeLabel {
        match self.code {
            Code::Label(ref mut label) => label,
            Code::Inline(_) => {
                let label = self.next_code_label();
                self.reify_as(label);
                self.to_label()
            }
        }
    }

    #[cfg_attr(rustfmt, rustfmt_skip)]
    fn reify_as(&mut self, label: CodeLabel) {
        let code = format!("
            {} => {{{}
            }}", label, self.to_inline());
        self.code_label_arms.push_str(&code);
        self.code = Code::Label(label);
    }
}

struct Compose<F, G>(F, G);

impl<A, F: FnOnce<A>, G: FnOnce<(F::Output,)>> FnOnce<A> for Compose<F, G> {
    type Output = G::Output;
    extern "rust-call" fn call_once(self, args: A) -> Self::Output {
        self.1(self.0.call_once(args))
    }
}

#[must_use]
struct Thunk<F>(F);

impl<F> Thunk<F> {
    fn new(f: F) -> Self
    where
        F: FnOnce(Continuation) -> Continuation,
    {
        Thunk(f)
    }
}

impl<F, G> Add<Thunk<G>> for Thunk<F> {
    type Output = Thunk<Compose<G, F>>;
    fn add(self, other: Thunk<G>) -> Self::Output {
        Thunk(Compose(other.0, self.0))
    }
}

impl<A, F: FnOnce<A>> FnOnce<A> for Thunk<F> {
    type Output = F::Output;
    extern "rust-call" fn call_once(self, args: A) -> Self::Output {
        self.0.call_once(args)
    }
}

macro thunk($($x:expr),*) {{
    let mut prefix = String::new();
    $(write!(prefix, "{}", $x).unwrap();)*
    Thunk::new(move |mut cont| {
        cont.to_inline().insert_str(0, &prefix);
        cont
    })
}}

fn pop_state<F: FnOnce(Continuation) -> Continuation>(
    f: impl FnOnce(&str) -> Thunk<F>,
) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    f("c.state") + Thunk::new(|mut cont| {
        if let Some(&None) = cont.nested_frames.last() {
            *cont.nested_frames.last_mut().unwrap() = Some(cont.to_label().clone());
            cont.code = Code::Inline(String::new());
            cont = ret()(cont);
        }
        cont.nested_frames.push(None);
        cont
    })
}

fn push_state(state: &str) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    thunk!(
        "
                c.state = ",
        state,
        ";"
    ) + Thunk::new(move |mut cont| {
        if let Some(ret_label) = cont.nested_frames.pop().unwrap() {
            cont = call(mem::replace(cont.to_label(), ret_label))(cont);
        }
        cont
    })
}

fn check<'a>(condition: &'a str) -> Thunk<impl FnOnce(Continuation) -> Continuation + 'a> {
    Thunk::new(move |mut cont| {
        let code = cont.to_inline();
        *code = format!(
            "
                if {} {{{}
                }}",
            condition,
            code.replace("\n", "\n    ")
        );
        cont
    })
}

fn call(callee: CodeLabel) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    Thunk::new(move |mut cont| {
        cont.code = Code::Inline(format!(
            "
                c.code = {};
                p.gss.call(Call {{ callee: {}, range: _range }}, c);",
            cont.to_label(),
            callee
        ));
        cont
    })
}

fn ret() -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    thunk!(
        "
                p.gss.ret(c.frame, _range);"
    ) + Thunk::new(|mut cont| {
        assert_eq!(cont.to_inline(), "");
        cont
    })
}

fn sppf_add(
    parse_label: &ParseLabel,
    child: &str,
) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    thunk!(
        "
                p.sppf.add(",
        parse_label,
        ", c.frame.range.subtract_suffix(_range), ",
        child,
        ");"
    )
}

trait ForEachThunk {
    fn for_each_thunk(self, cont: &mut Continuation, f: impl FnMut(Continuation));
}

impl<F> ForEachThunk for Thunk<F>
where
    F: FnOnce(Continuation) -> Continuation,
{
    fn for_each_thunk(self, cont: &mut Continuation, mut f: impl FnMut(Continuation)) {
        f(self(cont.clone()));
    }
}

impl<T, U> ForEachThunk for (T, U)
where
    T: ForEachThunk,
    U: ForEachThunk,
{
    fn for_each_thunk(self, cont: &mut Continuation, mut f: impl FnMut(Continuation)) {
        self.0.for_each_thunk(cont, &mut f);
        self.1.for_each_thunk(cont, &mut f);
    }
}

struct ThunkIter<I>(I);

impl<I, T> ForEachThunk for ThunkIter<I>
where
    I: Iterator<Item = T>,
    T: ForEachThunk,
{
    fn for_each_thunk(self, cont: &mut Continuation, mut f: impl FnMut(Continuation)) {
        self.0.for_each(|x| {
            x.for_each_thunk(cont, &mut f);
        });
    }
}

fn parallel(thunks: impl ForEachThunk) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    Thunk::new(|mut cont| {
        cont.to_label();
        let mut code = String::new();
        let mut child_nested_frames = None;
        let nested_frames = cont.nested_frames.clone();
        thunks.for_each_thunk(&mut cont, |mut child_cont| {
            code.push_str(child_cont.to_inline());
            if let Some(prev) = child_nested_frames {
                assert_eq!(child_cont.nested_frames.len(), prev);
            } else {
                child_nested_frames = Some(child_cont.nested_frames.len());
            }
            assert_eq!(
                child_cont.nested_frames[..],
                nested_frames[..child_cont.nested_frames.len()]
            );
        });
        cont.code = Code::Inline(code);
        if let Some(child_nested_frames) = child_nested_frames {
            while cont.nested_frames.len() > child_nested_frames {
                assert_eq!(cont.nested_frames.pop(), Some(None));
            }
        }
        cont
    })
}

fn opt(
    thunk: Thunk<impl FnOnce(Continuation) -> Continuation>,
) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    parallel((thunk, thunk!("")))
}

fn fix<F: FnOnce(Continuation) -> Continuation>(
    f: impl FnOnce(CodeLabel) -> Thunk<F>,
) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    Thunk::new(|mut cont| {
        let nested_frames = mem::replace(&mut cont.nested_frames, vec![]);
        let ret_label = cont.to_label().clone();
        cont.code = Code::Inline(String::new());
        let label = cont.next_code_label();
        cont = (reify_as(label.clone()) + f(label) + ret())(cont);
        cont = call(mem::replace(cont.to_label(), ret_label))(cont);
        cont.nested_frames = nested_frames;
        cont
    })
}

fn reify_as(label: CodeLabel) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    Thunk::new(|mut cont| {
        cont.reify_as(label);
        cont
    })
}

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<Pat: Ord + ToRustSrc> Rule<Pat> {
    fn generate_parse<'a>(
        self: &'a Rc<Self>,
        parse_labels: Option<&'a RefCell<BTreeMap<Rc<Rule<Pat>>, (ParseLabel, ParseLabelKind<ParseLabel>)>>>
    ) -> Thunk<impl FnOnce(Continuation) -> Continuation + 'a> {
        Thunk::new(move |cont| match (&**self, parse_labels) {
            (Rule::Empty, _) => cont,
            (Rule::Match(pat), _) => {
                check(&format!("let Some(_range) = p.input_consume_left(_range, {})", pat.to_rust_src()))(cont)
            }
            (Rule::NotMatch(pat), _) => {
                check(&format!("p.input_consume_left(_range, {}).is_none()", pat.to_rust_src()))(cont)
            }
            (Rule::Call(r), _) => call(CodeLabel(r.clone()))(cont),
            (Rule::Concat([left, right]), None) => (
                left.generate_parse(None) +
                right.generate_parse(None)
            )(cont),
            (Rule::Concat([left, right]), Some(parse_labels)) => (
                thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                left.generate_parse(Some(parse_labels)) +
                push_state("c.frame.range.subtract_suffix(_range).len()") +
                right.generate_parse(Some(parse_labels)) +
                pop_state(|state| sppf_add(&self.parse_label(parse_labels), state))
            )(cont),
            (Rule::Or(rules), None) => {
                parallel(ThunkIter(rules.iter().map(|rule| {
                    rule.generate_parse(None)
                })))(cont)
            }
            (Rule::Or(rules), Some(parse_labels)) => (
                thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                parallel(ThunkIter(rules.iter().map(|rule| {
                    push_state(&format!("{}.to_usize()", rule.parse_label(parse_labels))) +
                    rule.generate_parse(Some(parse_labels))
                }))) +
                pop_state(|state| sppf_add(&self.parse_label(parse_labels), state))
            )(cont),
            (Rule::Opt(rule), _) => {
                let parse_label = parse_labels.and_then(|parse_labels| {
                    rule.parse_label(parse_labels);
                    match parse_labels.borrow()[rule].1 {
                        // TODO: unpack aliases?
                        ParseLabelKind::Choice | ParseLabelKind::Binary(..) => None,
                        _ => Some(self.parse_label(parse_labels)),
                    }
                });
                if let Some(parse_label) = parse_label {
                    (
                        thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                        opt(
                            rule.generate_parse(parse_labels) +
                            sppf_add(&parse_label, "0"),
                            )
                    )(cont)
                } else {
                    opt(rule.generate_parse(parse_labels))(cont)
                }
            }
            (Rule::RepeatMany(rule), None) => fix(|label| {
                opt(rule.generate_parse(None) + call(label))
            })(cont),
            (Rule::RepeatMany(rule), Some(parse_labels)) => fix(|label| {
                let more = Rc::new(Rule::RepeatMore(rule.clone()));
                opt(
                    thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                    rule.generate_parse(Some(parse_labels)) +
                    push_state("c.frame.range.subtract_suffix(_range).len()") +
                    call(label) +
                    pop_state(move |state| sppf_add(&more.parse_label(parse_labels), state))
                )
            })(cont),
            (Rule::RepeatMore(rule), None) => fix(|label| {
                rule.generate_parse(None) + opt(call(label))
            })(cont),
            (Rule::RepeatMore(rule), Some(parse_labels)) => fix(|label| {
                thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                rule.generate_parse(Some(parse_labels)) +
                push_state("c.frame.range.subtract_suffix(_range).len()") +
                opt(call(label)) +
                pop_state(|state| sppf_add(&self.parse_label(parse_labels), state))
            })(cont),
        })
    }
    fn generate_traverse(
        &self,
        node: &str,
        refutable: bool,
        parse_labels: &RefCell<BTreeMap<Rc<Rule<Pat>>, (ParseLabel, ParseLabelKind<ParseLabel>)>>,
    ) -> String {
        let mut out = String::new();
        macro put($($x:expr),*) {{ $(write!(out, "{}", $x).unwrap();)* }}

        match self {
            Rule::Empty | Rule::Match(_) | Rule::NotMatch(_) | Rule::Call(_) | Rule::RepeatMany(_) | Rule::RepeatMore(_) => {
                put!("::std::iter::once(");
                if refutable {
                    put!("Some(")
                }
                put!(node, ")");
                if refutable {
                    put!(")");
                }
            }
            Rule::Concat([left, right]) => {
                put!("self.parser.sppf.binary_children(", node, ").flat_map(move |(left, right)| {
            ", left.generate_traverse("left", refutable, parse_labels), ".flat_map(move |left| {
                ", right.generate_traverse("right", refutable, parse_labels).replace("\n", "\n    "), ".map(move |right| (left, right))
            })
        })");
            }
            Rule::Or(rules) => {
                put!("self.parser.sppf.unary_children(", node, ").flat_map(move |node| {
            enum Iter<");
                for i in 0..rules.len() {
                    put!("_", i, ",");
                }
                put!("> {");
                for i in 0..rules.len() {
                    put!("
                _", i, "(_", i, "),");
                }
                put!("
            }
            impl<");
                for i in 0..rules.len() {
                    put!("_", i, ": Iterator,");
                }
                put!("> Iterator for Iter<");
                for i in 0..rules.len() {
                    put!("_", i, ",");
                }
                put!(">
                where");
                for i in 0..rules.len() {
                    put!("
                    _", i, "::Item: Default,");
                }
                put!("
            {
                type Item = (");
                for i in 0..rules.len() {
                    put!("_", i, "::Item,");
                }
                put!(");
                fn next(&mut self) -> Option<Self::Item> {
                    let mut r = Self::Item::default();
                    match self {");
                for i in 0..rules.len() {
                    put!("
                        Iter::_", i, "(it) => r.", i, " = it.next()?,");
                }
                    put!("
                    }
                    Some(r)
                }
            }
            match node.l {");
                for (i, rule) in rules.iter().enumerate() {
                    put!("
                ", rule.parse_label(parse_labels), " => Iter::_", i, "(", rule.generate_traverse("node", true, parse_labels).replace("\n", "\n    "), "),");
                }
                put!("
                _ => unreachable!(),
            }
        })");
            }
            Rule::Opt(rule) => {
                put!("self.parser.sppf.unary_children(", node, ").flat_map(move |node| {
            match node.l {
                ", rule.parse_label(parse_labels), " => {
                    Some(", rule.generate_traverse("node", true, parse_labels).replace("\n", "\n        "), ".map(|x| (x,)))
                        .into_iter().flatten().chain(None)
                }
                ", Rc::new(Rule::Empty).parse_label(parse_labels), " => {
                    None.into_iter().flatten().chain(Some(<(_,)>::default()))
                }
                _ => unreachable!()
        })");
            }
        }
        out.replace("\n", "\n    ")
    }
}
