use ordermap::OrderMap;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt;
use std::fmt::Write as FmtWrite;
use std::io::Write;
use std::mem;
use std::ops::Add;
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
    pub fn atom(atom: A) -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::Atom(atom)),
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
            Rule::Atom(_) | Rule::Call(_) => {}
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
pub enum Rule<A> {
    Empty,
    Atom(A),
    Call(String),
    Concat([Rc<Rule<A>>; 2]),
    Or(Vec<Rc<Rule<A>>>),
}

impl<A: Atom + Ord> Rule<A> {
    fn field_type(&self, path: &[usize]) -> &str {
        match *self {
            Rule::Empty | Rule::Atom(_) => "Terminal",
            Rule::Call(ref r) => r,
            Rule::Concat(ref rules) => rules[path[0]].field_type(&path[1..]),
            Rule::Or(ref rules) => rules[path[0]].field_type(&path[1..]),
        }
    }
    fn field_is_refutable(&self, path: &[usize]) -> bool {
        match *self {
            Rule::Empty | Rule::Atom(_) | Rule::Call(_) => false,
            Rule::Concat(ref rules) => rules[path[0]].field_is_refutable(&path[1..]),
            Rule::Or(..) => true,
        }
    }
    fn parse_label(
        self: &Rc<Self>,
        parse_labels: &RefCell<BTreeMap<Rc<Self>, (ParseLabel, ParseLabelKind<ParseLabel>)>>,
    ) -> ParseLabel {
        if let Some(&(ref label, _)) = parse_labels.borrow().get(self) {
            return label.clone();
        }
        let (label, kind) = match **self {
            Rule::Empty => (ParseLabel("()".to_string()), ParseLabelKind::Unary(None)),
            Rule::Atom(ref a) => (
                ParseLabel(a.to_label_description()),
                ParseLabelKind::Unary(None),
            ),
            Rule::Call(ref r) => return ParseLabel(r.clone()),
            Rule::Concat([ref left, ref right]) => {
                let left = left.parse_label(parse_labels);
                let right = right.parse_label(parse_labels);

                (
                    ParseLabel(format!("({} {})", left.0, right.0)),
                    ParseLabelKind::Binary(Some(left), Some(right)),
                )
            }
            Rule::Or(ref rules) => {
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
    (@rule $atom:expr) => {
        RuleWithNamedFields::atom($atom)
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

        let mut parse_labels = RefCell::new(BTreeMap::new());
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
        let node = ParseNode { l: Some(", ParseLabel(name.clone()), "), range: self.span };
        self.parser.sppf.unary_children(node).flat_map(move |node| {
            ", rule.rule.generate_traverse("node", false, &mut parse_labels), "
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
            callee: ", CodeLabel(name.clone()), ",
            range: Range(p.input.range()),
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
}");
        }
        put!("
fn parse(p: &mut Parser) {
    while let Some(Call { callee: mut c, range: _range }) = p.gss.threads.steal() {
        match c.code {");
        for (name, rule) in &self.rules {
            code_labels.push(CodeLabel(name.clone()));
            let parse_label = ParseLabel(name.clone());
            let inner = rule.rule.parse_label(&mut parse_labels);
            named_parse_labels.push((parse_label.clone(), ParseLabelKind::Unary(Some(inner))));

            put!((reify_as(CodeLabel(name.clone())) + rule.rule.generate_parse(&mut parse_labels) + thunk!(&format!("
                p.sppf.add({}, c.frame.range.subtract_suffix(_range), 0);", parse_label)) + ret())(Continuation {
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
        for (i, &(ref l, _)) in named_parse_labels.iter().chain(parse_labels.borrow().values()).enumerate() {
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
        for &(ref l, _) in named_parse_labels.iter().chain(parse_labels.borrow().values()) {
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
        for &(ref label, ref kind) in named_parse_labels.iter().chain(parse_labels.borrow().values()) {
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
                nested_frames: vec![None],
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
impl<A: Atom + Ord> Rule<A> {
    fn generate_parse<'a>(
        self: &'a Rc<Self>,
        parse_labels: &'a RefCell<BTreeMap<Rc<Rule<A>>, (ParseLabel, ParseLabelKind<ParseLabel>)>>
    ) -> Thunk<impl FnOnce(Continuation) -> Continuation + 'a> {
        Thunk::new(move |cont| match **self {
            Rule::Empty => cont,
            Rule::Atom(ref a) => {
                let a = a.to_rust_slice();
                (
                    check(&format!("p.input[_range.0].starts_with({})", a)) +
                    thunk!("
                let _range = Range(_range.split_at(", a, ".len()).1);")
                )(cont)
            },
            Rule::Call(ref r) => {
                call(CodeLabel(r.clone()))(cont)
            },
            Rule::Concat([ref left, ref right]) =>
                (
                    thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                    left.generate_parse(parse_labels) +
                    push_state("c.frame.range.subtract_suffix(_range).len()") +
                    right.generate_parse(parse_labels) +
                    pop_state(|state| thunk!("
                p.sppf.add(", self.parse_label(parse_labels), ", c.frame.range.subtract_suffix(_range), ", state, ");"))
                )(cont),
            Rule::Or(ref rules) =>
                (
                    thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                    parallel(rules.iter().map(|rule| {
                        push_state(&format!("{}.to_usize()", rule.parse_label(parse_labels))) +
                        rule.generate_parse(parse_labels)
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
        parse_labels: &RefCell<BTreeMap<Rc<Rule<A>>, (ParseLabel, ParseLabelKind<ParseLabel>)>>,
    ) -> String {
        let mut out = String::new();
        macro put($($x:expr),*) {{ $(write!(out, "{}", $x).unwrap();)* }}

        match *self {
            Rule::Empty | Rule::Atom(_) | Rule::Call(_) => {
                put!("::std::iter::once(");
                if refutable {
                    put!("Some(")
                }
                put!(node, ".range)");
                if refutable {
                    put!(")");
                }
            }
            Rule::Concat([ref left, ref right]) => {
                put!("self.parser.sppf.binary_children(", node, ").flat_map(move |(left, right)| {
            ", left.generate_traverse("left", refutable, parse_labels), ".flat_map(move |left| {
                ", right.generate_traverse("right", refutable, parse_labels).replace("\n", "\n    "), ".map(move |right| (left, right))
            })
        })");
            }
            Rule::Or(ref rules) => {
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
                    match *self {");
                for i in 0..rules.len() {
                    put!("
                        Iter::_", i, "(ref mut it) => r.", i, " = it.next()?,");
                }
                    put!("
                    }
                    Some(r)
                }
            }
            match node.l.unwrap() {");
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
