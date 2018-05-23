use ordermap::OrderMap;
use std::collections::BTreeMap;
use std::fmt;
use std::fmt::Write as FmtWrite;
use std::io::Write;
use std::rc::Rc;
use ParseLabelKind;

pub struct Grammar<A> {
    rules: OrderMap<String, RuleWithNamedFields<A>>,
}

impl<A> Grammar<A> {
    pub fn new() -> Self {
        Grammar {
            rules: OrderMap::new(),
        }
    }
    pub fn add_rule(&mut self, name: &str, rule: RuleWithNamedFields<A>) {
        self.rules.insert(name.to_string(), rule);
    }
}

pub struct RuleWithNamedFields<A> {
    rule: Rc<Rule<A>>,
    fields: OrderMap<String, Vec<usize>>,
}

impl<A: Clone + fmt::Debug + PartialEq> RuleWithNamedFields<A> {
    pub fn empty() -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::Empty),
            fields: OrderMap::new(),
        }
    }
    pub fn unit(unit: Unit<A>) -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::Concat(Rc::new(Rule::Empty), unit)),
            fields: OrderMap::new(),
        }
    }
    pub fn alternation(rules: Vec<Self>) -> Self {
        let mut fields = OrderMap::new();
        let choices = rules
            .into_iter()
            .enumerate()
            .map(|(i, rule)| {
                fields.extend(rule.fields.into_iter().map(|(name, path)| {
                    assert_eq!(path, &[1]);
                    (name, vec![i])
                }));

                match *rule.rule {
                    Rule::Concat(ref left, ref unit) => {
                        assert_eq!(**left, Rule::Empty);
                        unit.clone()
                    }
                    _ => unimplemented!(),
                }
            })
            .collect();
        RuleWithNamedFields {
            rule: Rc::new(Rule::Alternation(choices)),
            fields,
        }
    }
    pub fn with_field_name(mut self, name: &str) -> Self {
        match *self.rule {
            Rule::Concat(ref left, _) => {
                assert_eq!(**left, Rule::Empty);
            }
            _ => unimplemented!(),
        }
        self.fields.insert(name.to_string(), vec![1]);
        self
    }
    pub fn then(mut self, other: Self) -> Self {
        match *other.rule {
            Rule::Concat(ref left, ref unit) => {
                assert_eq!(**left, Rule::Empty);
                for path in self.fields.values_mut() {
                    path.insert(0, 0);
                }
                self.fields.extend(other.fields);
                self.rule = Rc::new(Rule::Concat(self.rule, unit.clone()));
            }
            _ => unimplemented!(),
        }
        self
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rule<A> {
    Empty,
    Concat(Rc<Rule<A>>, Unit<A>),
    Alternation(Vec<Unit<A>>),
}

impl<A: Atom + Ord> Rule<A> {
    fn field_type(&self, path: &[usize]) -> &str {
        let unit = match *self {
            Rule::Empty => return "Terminal",
            Rule::Concat(ref rule, ref unit) => match *path {
                [0, ref rest..] => {
                    return rule.field_type(rest);
                }
                [1] => unit,
                _ => unreachable!(),
            },
            Rule::Alternation(ref choices) => &choices[path[0]],
        };
        match *unit {
            Unit::Rule(ref r) => r,
            Unit::Atom(_) => "Terminal",
        }
    }
    fn field_is_refutable(&self, path: &[usize]) -> bool {
        match *self {
            Rule::Empty => false,
            Rule::Concat(ref rule, _) => match *path {
                [0, ref rest..] => rule.field_is_refutable(rest),
                [1] => false,
                _ => unreachable!(),
            },
            Rule::Alternation(..) => true,
        }
    }
    fn parse_label(
        self: &Rc<Self>,
        parse_labels: &mut BTreeMap<Rc<Self>, (ParseLabel, ParseLabelKind<ParseLabel>)>,
    ) -> ParseLabel {
        if let Some(&(ref label, _)) = parse_labels.get(self) {
            return label.clone();
        }
        let (label, kind) = match **self {
            Rule::Empty => (ParseLabel::new("()"), ParseLabelKind::Unary(None)),
            Rule::Concat(ref rule, ref unit) => {
                let left = rule.parse_label(parse_labels);
                let right = unit.to_label_description();
                let label = ParseLabel::new(&format!("({} {})", left.description, right));

                let right = match *unit {
                    Unit::Rule(ref r) => Some(ParseLabel::new(r)),
                    Unit::Atom(_) => None,
                };
                (label, ParseLabelKind::Binary(Some(left), right))
            }
            Rule::Alternation(ref units) => {
                assert!(units.len() > 1);
                let mut s = String::from("(");
                for (i, unit) in units.iter().enumerate() {
                    if i > 0 {
                        s.push_str(" | ");
                    }
                    s.push_str(&unit.to_label_description());
                }
                s.push(')');
                (ParseLabel::new(&s), ParseLabelKind::Choice)
            }
        };
        assert!(
            parse_labels
                .insert(self.clone(), (label.clone(), kind))
                .is_none()
        );
        label
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Unit<A> {
    Atom(A),
    Rule(String),
}

impl<A: Atom> Unit<A> {
    fn to_label_description(&self) -> String {
        match *self {
            Unit::Atom(ref a) => a.to_label_description(),
            Unit::Rule(ref r) => r.clone(),
        }
    }
}

pub trait Atom {
    fn to_label_description(&self) -> String;
    fn to_rust_slice(&self) -> String;
}

impl Atom for str {
    fn to_label_description(&self) -> String {
        format!("\"{}\"", self.escape_default())
    }
    fn to_rust_slice(&self) -> String {
        format!("{:?}.as_bytes()", self)
    }
}

impl Atom for char {
    fn to_label_description(&self) -> String {
        self.to_string().to_label_description()
    }
    fn to_rust_slice(&self) -> String {
        self.to_string().to_rust_slice()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ParseLabel {
    description: String,
}

impl ParseLabel {
    fn new(s: &str) -> ParseLabel {
        ParseLabel {
            description: s.to_string(),
        }
    }
    pub fn empty() -> ParseLabel {
        ParseLabel::new("")
    }
}

impl fmt::Display for ParseLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "P!({})", self.description)
    }
}

pub macro grammar {
    (@rule { $name:ident : $rule:tt }) => {
        grammar!(@rule $rule).with_field_name(stringify!($name))
    },
    (@rule $rule0:tt | $($rule:tt)|+) => {
        RuleWithNamedFields::alternation(vec![
            grammar!(@rule $rule0),
            $(grammar!(@rule $rule)),*
        ])
    },
    (@rule { $($rule:tt)* }) => {
        RuleWithNamedFields::empty()
            $(.then(grammar!(@rule $rule)))*
    },
    (@rule $rule:ident) => {
        RuleWithNamedFields::unit(Unit::Rule(stringify!($rule).to_string()))
    },
    (@rule $atom:expr) => {
        RuleWithNamedFields::unit(Unit::Atom($atom))
    },
    ($($rule_name:ident = $($rule:tt)|+;)*) => ({
        let mut grammar = Grammar::new();
        $(grammar.add_rule(stringify!($rule_name), grammar!(@rule $($rule)|+));)*
        grammar
    })
}

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<A: Atom + Ord> Grammar<A> {
    pub fn generate(&mut self, out: &mut Write) {
        macro put($($x:expr),*) {{ $(write!(out, "{}", $x).unwrap();)* }}

        let mut parse_labels = BTreeMap::new();
        let mut named_parse_labels = vec![];
        let mut code_labels = vec![];

        put!("extern crate gll;

use self::gll::{Call, Continuation, ParseLabel, CodeLabel, ParseLabelKind, ParseNode, Range};
use std::fmt;
use std::marker::PhantomData;

pub type Parser<'a, 'id> = gll::Parser<'id, _P, _C, &'a [u8]>;

#[derive(Debug)]
pub struct Ambiguity;

pub struct Handle<'a, 'b: 'a, 'id: 'a, T> {
    pub span: Range<'id>,
    pub parser: &'a Parser<'b, 'id>,
    _marker: PhantomData<T>,
}

impl<'a, 'b, 'id, T> Copy for Handle<'a, 'b, 'id, T> {}

impl<'a, 'b, 'id, T> Clone for Handle<'a, 'b, 'id, T> {
    fn clone(&self) -> Self {
        *self
    }
}

pub struct Terminal<'a, 'b: 'a, 'id: 'a> {
    _marker: PhantomData<(&'a (), &'b (), &'id ())>,
}

impl<'a, 'b, 'id> fmt::Debug for Terminal<'a, 'b, 'id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct(\"\").finish()
    }
}

impl<'a, 'b, 'id> fmt::Debug for Handle<'a, 'b, 'id, Terminal<'a, 'b, 'id>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            \"{}..{}\",
            self.span.start(),
            self.span.end()
        )
    }
}
");
        for (name, rule) in &self.rules {
            put!("

pub struct ", name, "<'a, 'b: 'a, 'id: 'a> {");
            for (field_name, path) in &rule.fields {
                let refutable = rule.rule.field_is_refutable(path);
                put!("
    pub ", field_name, ": ");
                if refutable {
                    put!("Option<");
                }
                put!("Handle<'a, 'b, 'id, ", rule.rule.field_type(path), "<'a, 'b, 'id>>");
                if refutable {
                    put!(">");
                }
                put!(",");
            }
            if rule.fields.is_empty() {
                put!("
    _marker: PhantomData<(&'a (), &'b (), &'id ())>,");
            }
            put!("
}

impl<'a, 'b, 'id> fmt::Debug for ", name, "<'a, 'b, 'id> {
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
}

impl<'a, 'b, 'id> fmt::Debug for Handle<'a, 'b, 'id, ", name, "<'a, 'b, 'id>> {
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

impl<'a, 'b, 'id> Handle<'a, 'b, 'id, ", name, "<'a, 'b, 'id>> {
    pub fn one(self) -> Result<", name, "<'a, 'b, 'id>, Ambiguity> {
        let mut iter = self.many();
        let first = iter.next().unwrap();
        if iter.next().is_none() {
            Ok(first)
        } else {
            Err(Ambiguity)
        }
    }
    pub fn many(self) -> impl Iterator<Item = ", name, "<'a, 'b, 'id>> {
        let node = ParseNode { l: Some(", ParseLabel::new(name), "), range: self.span };
        self.parser.sppf.unary_children(node).flat_map(move |node| {",
                rule.rule.generate_traverse(), "
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
}

impl<'a, 'b, 'id> ", name, "<'a, 'b, 'id> {
    pub fn parse(p: &'a mut Parser<'b, 'id>) -> Result<Handle<'a, 'b, 'id, Self>, ()> {
        let call = Call {
            callee: _C::", name, ",
            range: Range(p.input.range()),
        };
        if !p.gss.calls.contains_key(&call) {
            let dummy = Range(p.input.empty_range());
            p.gss.threads.spawn(
                Continuation {
                    code: call.callee,
                    stack: call,
                    state: 0,
                },
                dummy,
                call.range,
            );
            parse(p);
        }
        if let Some(node) = p.gss.calls.get(&call) {
            if let Some(&r) = node.results.iter().rev().next() {
                return Ok(Handle {
                    span: r,
                    parser: p,
                    _marker: PhantomData,
                });
            }
        }
        Err(())
    }
}");
        }
        put!("
fn parse(p: &mut Parser) {
    while let Some(Call { callee: (mut c, _result), range: _range }) = p.gss.threads.steal() {
        match c.code {");
        for (name, rule) in &self.rules {
            code_labels.push(name.clone());
            let parse_label = ParseLabel::new(name);
            let inner = rule.rule.parse_label(&mut parse_labels);
            named_parse_labels.push((parse_label.clone(), ParseLabelKind::Unary(Some(inner))));

            put!(reify_as(name.clone(), rule.rule.generate_parse(Continuation {
                code_labels: &mut code_labels,
                code_label_prefix: name,
                code_label_counter: &mut 0,
                code_label_arms: &mut String::new(),
                parse_labels: &mut parse_labels,
                code: Code::Inline(format!("
                p.sppf.add({}, _result, 0);
                p.gss.ret(c.stack, _result);", parse_label)),
            })).code_label_arms);
        }
        put!("
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum _P {");
        for i in 0..named_parse_labels.len() + parse_labels.len() {
            put!(
                "
    _", i, ",");
        }
        put!("
}

macro P {");
        for (i, &(ref l, _)) in named_parse_labels.iter().chain(parse_labels.values()).enumerate() {
            if i != 0 {
                put!(",");
            }
            put!("
    (", l.description, ") => (_P::_", i, ")");
        }
        put!("
}

impl fmt::Display for _P {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match *self {");
        for &(ref l, _) in named_parse_labels.iter().chain(parse_labels.values()) {
            put!("
            ", l, " => \"", l.description.escape_default(), "\",");
        }
        put!("
        };
        write!(f, \"{}\", s)
    }
}

impl ParseLabel for _P {
    fn kind(self) -> ParseLabelKind<Self> {
        match self {");
        for &(ref label, ref kind) in named_parse_labels.iter().chain(parse_labels.values()) {
            put!("
                ", label, " => ParseLabelKind::");
            match *kind {
                ParseLabelKind::Unary(ref inner) => {
                    put!("Unary(");
                    match *inner {
                        Some(ref x) => put!("Some(", x, ")"),
                        None => put!("None"),
                    }
                    put!("),");
                }
                ParseLabelKind::Binary(ref left, ref right) => {
                    put!("Binary(");
                    match *left {
                        Some(ref x) => put!("Some(", x, ")"),
                        None => put!("None"),
                    }
                    put!(", ");
                    match *right {
                        Some(ref x) => put!("Some(", x, ")"),
                        None => put!("None"),
                    }
                    put!("),");
                }
                ParseLabelKind::Choice => put!("Choice,"),
            }
        }
        put!("
        }
    }
    fn from_usize(i: usize) -> Self {
        match i {");

        for i in 0..named_parse_labels.len() + parse_labels.len() {
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
    ", s, ",");
        }
        put!("
}

impl CodeLabel for _C {}
");
    }
}

struct Continuation<'a, A: 'a> {
    code_labels: &'a mut Vec<String>,
    code_label_prefix: &'a str,
    code_label_counter: &'a mut usize,
    code_label_arms: &'a mut String,
    parse_labels: &'a mut BTreeMap<Rc<Rule<A>>, (ParseLabel, ParseLabelKind<ParseLabel>)>,
    code: Code,
}

#[derive(Clone)]
enum Code {
    Inline(String),
    Label(String),
}

impl<'a, A> Continuation<'a, A> {
    fn make_code_label(&mut self) -> String {
        *self.code_label_counter += 1;
        let next_code_label = format!("{}__{}", self.code_label_prefix, self.code_label_counter);
        self.code_labels.push(next_code_label.clone());
        next_code_label
    }
    fn to_inline(&mut self) -> &mut String {
        match self.code {
            Code::Inline(ref mut code) => code,
            Code::Label(ref label) => {
                self.code = Code::Inline(format!(
                    "
                c.code = _C::{};
                p.gss.threads.spawn(c, _result, _range);",
                    label
                ));
                self.to_inline()
            }
        }
    }
    fn to_label(&mut self) -> &str {
        match self.code {
            Code::Label(ref label) => label,
            Code::Inline(_) => {
                let label = self.make_code_label();
                self.reify_as(label);
                self.to_label()
            }
        }
    }

    #[cfg_attr(rustfmt, rustfmt_skip)]
    fn reify_as(&mut self, code_label: String) {
        let code = format!("
            _C::{} => {{{}
            }}", code_label, self.to_inline());
        self.code_label_arms.push_str(&code);
        self.code = Code::Label(code_label);
    }
}

macro build($($x:expr),*; $cont:expr) {{
    let mut prefix = String::new();
    $(write!(prefix, "{}", $x).unwrap();)*
    let mut cont = $cont;
    cont.to_inline().insert_str(0, &prefix);
    cont
}}

fn get_state<'a, A>(
    f: impl FnOnce(&str, Continuation<'a, A>) -> Continuation<'a, A>,
    cont: Continuation<'a, A>,
) -> Continuation<'a, A> {
    f("c.state", cont)
}

fn set_state<'a, A>(state: &str, cont: Continuation<'a, A>) -> Continuation<'a, A> {
    build!("
                c.state = ", state, ";"; cont)
}

fn reify_as<'a, A>(code_label: String, mut cont: Continuation<'a, A>) -> Continuation<'a, A> {
    cont.reify_as(code_label);
    cont
}

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<A: Atom + Ord> Unit<A> {
    fn generate_parse<'a>(&self, mut cont: Continuation<'a, A>) -> Continuation<'a, A> {
        match *self {
            Unit::Rule(ref r) => {
                cont.code = Code::Inline(format!("
                c.code = _C::{};
                p.gss.call(Call {{ callee: _C::{}, range: _range }}, c);",
                    cont.to_label(), r
                ));
                cont
            }
            Unit::Atom(ref a) => {
                let a = a.to_rust_slice();
                cont = build!("
                let _result = Range(_range.split_at(", a, ".len()).0);
                let _range = _range.subtract(_result);"; cont);
                let code = cont.to_inline();
                *code = format!("
                if p.input[_range.0].starts_with({}) {{{}
                }}", a, code.replace("\n", "\n    "));
                cont
            }
        }
    }
}

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<A: Atom + Ord> Rule<A> {
    fn generate_parse<'a>(self: &Rc<Self>, mut cont: Continuation<'a, A>) -> Continuation<'a, A> {
        match **self {
            Rule::Empty => {
                build!("
                let _result = Range(_range.frontiers().0);"; cont)
            }
            Rule::Concat(ref left, ref right) => {
                let parse_label = self.parse_label(cont.parse_labels);
                build!("
                assert_eq!(_range.start(), c.stack.range.start());";
                left.generate_parse(
                set_state("_result.len()",
                right.generate_parse(
                get_state(|state, cont| build!("
                let _result = Range(c.stack.range.split_at(", state, " + _result.len()).0);
                p.sppf.add(", parse_label, ", _result, ", state, ");"; cont), cont)))))
            }
            Rule::Alternation(ref rules) => {
                cont = get_state(|state, cont| build!("
                p.sppf.add(", self.parse_label(cont.parse_labels), ", _result, ", state, ");"; cont), cont);
                cont.to_label();
                let mut code = String::new();
                for unit in rules {
                    let parse_label = match *unit {
                        Unit::Rule(ref r) => ParseLabel::new(r),
                        Unit::Atom(..) => unimplemented!(),
                    };
                    code.push_str(set_state(&format!("{}.to_usize()", parse_label), unit.generate_parse(Continuation {
                        code_labels: cont.code_labels,
                        code_label_prefix: cont.code_label_prefix,
                        code_label_counter: cont.code_label_counter,
                        code_label_arms: cont.code_label_arms,
                        parse_labels: cont.parse_labels,
                        code: cont.code.clone(),
                    })).to_inline());
                }
                cont.code = Code::Inline(code);
                cont
            }
        }
    }
    fn generate_traverse(&self) -> String {
        let mut out = String::new();
        macro put($($x:expr),*) {{ $(write!(out, "{}", $x).unwrap();)* }}

        match *self {
            Rule::Empty => {
                put!("
        ::std::iter::once(node.range)");
            }
            Rule::Concat(ref rule, _) => {
                put!("
        self.parser.sppf.binary_children(node).flat_map(move |(node, right)| {",
                    rule.generate_traverse(), ".map(move |left| (left, right.range))
        })");
            }
            Rule::Alternation(ref choices) => {
                put!("
        self.parser.sppf.children[&node].iter().map(move |&i| {
            match _P::from_usize(i) {");
                for (i, unit) in choices.iter().enumerate() {
                    let parse_label = match *unit {
                        Unit::Rule(ref r) => ParseLabel::new(r),
                        Unit::Atom(..) => unimplemented!(),
                    };
                    put!("
                ", parse_label, " => (");
                    for (j, _) in choices.iter().enumerate() {
                        if i == j {
                            put!("Some(node.range),");
                        } else {
                            put!("None,");
                        }
                    }
                    put!("),");
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
