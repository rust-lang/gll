use ordermap::OrderMap;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt;
use std::fmt::Write as FmtWrite;
use std::io::Write;
use std::mem;
use std::ops::{Add, RangeInclusive};
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
        match *self.rule {
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
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rule<Pat> {
    Empty,
    Match(Pat),
    Call(String),
    Concat([Rc<Rule<Pat>>; 2]),
    Or(Vec<Rc<Rule<Pat>>>),
}

impl<Pat: Ord + ToRustSrc> Rule<Pat> {
    fn field_type(&self, path: &[usize]) -> &str {
        match self {
            Rule::Empty | Rule::Match(_) => "Terminal",
            Rule::Call(r) => r,
            Rule::Concat(rules) => rules[path[0]].field_type(&path[1..]),
            Rule::Or(rules) => rules[path[0]].field_type(&path[1..]),
        }
    }
    fn field_is_refutable(&self, path: &[usize]) -> bool {
        match self {
            Rule::Empty | Rule::Match(_) | Rule::Call(_) => false,
            Rule::Concat(rules) => rules[path[0]].field_is_refutable(&path[1..]),
            Rule::Or(..) => true,
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
    (@rule { $name:ident : $rule:tt }) => {
        grammar!(@rule $rule).with_field_name(stringify!($name))
    },
    (@rule $rule0:tt | $($rule:tt)|+) => {
        RuleWithNamedFields::or(vec![
            grammar!(@rule $rule0),
            $(grammar!(@rule $rule)),*
        ])
    },
    (@rule { $($rule:tt)* }) => {
        RuleWithNamedFields::empty()
            $(.then(grammar!(@rule $rule)))*
    },
    (@rule $rule:ident) => {
        RuleWithNamedFields::call(stringify!($rule).to_string())
    },
    (@rule $pat:expr) => {
        RuleWithNamedFields::match_(Pat::from($pat))
    },
    ($($rule_name:ident = $($rule:tt)|+;)*) => ({
        let mut grammar = Grammar::new();
        $(grammar.add_rule(stringify!($rule_name), grammar!(@rule $($rule)|+));)*
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

pub struct Handle<'a, 'b: 'a, 'i: 'a, T> {
    pub span: Range<'i>,
    pub parser: &'a Parser<'b, 'i>,
    _marker: PhantomData<T>,
}

impl<'a, 'b, 'i, T> Copy for Handle<'a, 'b, 'i, T> {}

impl<'a, 'b, 'i, T> Clone for Handle<'a, 'b, 'i, T> {
    fn clone(&self) -> Self {
        *self
    }
}

pub struct Terminal<'a, 'b: 'a, 'i: 'a> {
    _marker: PhantomData<(&'a (), &'b (), &'i ())>,
}

impl<'a, 'b, 'i> fmt::Debug for Terminal<'a, 'b, 'i> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct(\"\").finish()
    }
}

impl<'a, 'b, 'i> fmt::Debug for Handle<'a, 'b, 'i, Terminal<'a, 'b, 'i>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            \"{}..{}\",
            self.span.start(),
            self.span.end()
        )
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
                put!("Handle<'a, 'b, 'i, ", rule.rule.field_type(path), "<'a, 'b, 'i>>");
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
        if let Some(r) = p.gss.longest_result(call) {
            return Ok(Handle {
                span: r,
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
        write!(f, \"{}..{}\", self.span.start(), self.span.end())
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
            self.span.start(),
            self.span.end()
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
        let node = ParseNode { l: ", ParseLabel(name.clone()), ", range: self.span };
        self.parser.sppf.unary_children(node).flat_map(move |node| {
            ", rule.rule.generate_traverse("node", false, &parse_labels), "
        }).map(move |_r| ", name, " {");
            for (field_name, path) in &rule.fields {
                if rule.rule.field_is_refutable(path) {
                    put!("
            ", field_name, ": _r");
                    for p in path {
                        put!(" .", p);
                    }
                    put!(".map(|span| Handle {
                span,
                parser: self.parser,
                _marker: PhantomData,
            }),");
                } else {
                    put!("
            ", field_name, ": Handle {
                span: _r");
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
                ParseLabelKind::Unary(rule.rule.parse_label(parse_labels))
            } else {
                ParseLabelKind::Opaque
            };
            named_parse_labels.push((parse_label.clone(), kind));

            put!((
                reify_as(CodeLabel(name.clone())) +
                rule.rule.generate_parse(parse_labels) +
                thunk!(&format!("
                p.sppf.add({}, c.frame.range.subtract_suffix(_range), 0);", parse_label)) +
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
                ", label, " => ParseLabelKind::");
            match kind {
                ParseLabelKind::Opaque => put!("Opaque,"),
                ParseLabelKind::Unary(inner) => put!("Unary(", inner, "),"),
                ParseLabelKind::Binary(left, right) => put!("Binary(", left, ", ", right, "),"),
                ParseLabelKind::Choice => put!("Choice,"),
            }
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
                *self.code_label_counter += 1;
                let label = CodeLabel(format!(
                    "{}__{}",
                    self.code_label_prefix, self.code_label_counter
                ));
                self.code_labels.push(label.clone());
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
            cont = call(mem::replace(&mut cont.to_label(), ret_label))(cont);
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

fn parallel(
    thunks: impl Iterator<Item = Thunk<impl FnOnce(Continuation) -> Continuation>>,
) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    Thunk::new(|mut cont| {
        cont.to_label();
        let mut code = String::new();
        let mut child_nested_frames = None;
        for thunk in thunks {
            let mut child_cont = Continuation {
                code_labels: cont.code_labels,
                code_label_prefix: cont.code_label_prefix,
                code_label_counter: cont.code_label_counter,
                code_label_arms: cont.code_label_arms,
                code: cont.code.clone(),
                nested_frames: cont.nested_frames.clone(),
            };
            child_cont = thunk(child_cont);
            code.push_str(child_cont.to_inline());
            if let Some(prev) = child_nested_frames {
                assert_eq!(child_cont.nested_frames.len(), prev);
            } else {
                child_nested_frames = Some(child_cont.nested_frames.len());
            }
            assert_eq!(
                child_cont.nested_frames[..],
                cont.nested_frames[..child_cont.nested_frames.len()]
            );
        }
        cont.code = Code::Inline(code);
        if let Some(child_nested_frames) = child_nested_frames {
            while cont.nested_frames.len() > child_nested_frames {
                assert_eq!(cont.nested_frames.pop(), Some(None));
            }
        }
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
                check(&format!("let Some(_range) = p.input_consume_left(_range, {})",pat.to_rust_src()))(cont)
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
                pop_state(|state| thunk!("
                p.sppf.add(", self.parse_label(parse_labels), ", c.frame.range.subtract_suffix(_range), ", state, ");"))
            )(cont),
            (Rule::Or(rules), None) => {
                parallel(rules.iter().map(|rule| {
                    rule.generate_parse(None)
                }))(cont)
            }
            (Rule::Or(rules), Some(parse_labels)) => (
                thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                parallel(rules.iter().map(|rule| {
                    push_state(&format!("{}.to_usize()", rule.parse_label(parse_labels))) +
                    rule.generate_parse(Some(parse_labels))
                })) +
                pop_state(|state| thunk!("
                p.sppf.add(", self.parse_label(parse_labels), ", c.frame.range.subtract_suffix(_range), ", state, ");"))
            )(cont),
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
            Rule::Empty | Rule::Match(_) | Rule::Call(_) => {
                put!("::std::iter::once(");
                if refutable {
                    put!("Some(")
                }
                put!(node, ".range)");
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
                put!("self.parser.sppf.choice_children(", node, ").flat_map(move |node| {
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
        }
        out.replace("\n", "\n    ")
    }
}
