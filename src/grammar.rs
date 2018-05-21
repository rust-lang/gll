use ordermap::OrderMap;
use std::collections::BTreeSet;
use std::fmt;
use std::io::Write;
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
    rule: Rule<A>,
    fields: OrderMap<String, Vec<usize>>,
}

impl<A: Clone> RuleWithNamedFields<A> {
    pub fn empty() -> Self {
        RuleWithNamedFields {
            rule: Rule::Empty,
            fields: OrderMap::new(),
        }
    }
    pub fn unit(unit: Unit<A>) -> Self {
        RuleWithNamedFields {
            rule: Rule::Concat(Box::new(Rule::Empty), (unit, ParseLabel::empty())),
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

                match rule.rule {
                    Rule::Concat(box Rule::Empty, (unit, _)) => unit,
                    _ => unimplemented!(),
                }
            })
            .collect();
        RuleWithNamedFields {
            rule: Rule::Alternation(ParseLabel::empty(), choices),
            fields,
        }
    }
    pub fn with_field_name(mut self, name: &str) -> Self {
        match self.rule {
            Rule::Concat(box Rule::Empty, _) => {}
            _ => unimplemented!(),
        }
        self.fields.insert(name.to_string(), vec![1]);
        self
    }
    pub fn then(mut self, other: Self) -> Self {
        match other.rule {
            Rule::Concat(box Rule::Empty, (unit, l)) => {
                for path in self.fields.values_mut() {
                    path.insert(0, 0);
                }
                self.fields.extend(other.fields);
                self.rule = Rule::Concat(Box::new(self.rule), (unit, l));
            }
            _ => unimplemented!(),
        }
        self
    }
}

pub enum Rule<A> {
    Empty,
    Concat(Box<Rule<A>>, (Unit<A>, ParseLabel)),
    Alternation(ParseLabel, Vec<Unit<A>>),
}

impl<A: Atom> Rule<A> {
    fn field_type(&self, path: &[usize]) -> &str {
        let unit = match *self {
            Rule::Empty => return "Terminal",
            Rule::Concat(ref rule, (ref unit, _)) => match *path {
                [0, ref rest..] => {
                    return rule.field_type(rest);
                }
                [1] => unit,
                _ => unreachable!(),
            },
            Rule::Alternation(_, ref choices) => &choices[path[0]],
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
    fn compute_parse_labels(
        &mut self,
        parse_labels: &mut BTreeSet<ParseLabel>,
        parse_label_kinds: &mut BTreeSet<(ParseLabel, ParseLabelKind<ParseLabel>)>,
    ) -> ParseLabel {
        match *self {
            Rule::Empty => {
                let label = ParseLabel::new("()");
                parse_labels.insert(label.clone());
                parse_label_kinds.insert((label.clone(), ParseLabelKind::Unary(None)));
                label
            }
            Rule::Concat(ref mut rule, (ref unit, ref mut label)) => {
                let left = rule.compute_parse_labels(parse_labels, parse_label_kinds);
                let right = unit.to_label_description();
                *label = ParseLabel::new(&format!("({} {})", left.description, right));
                parse_labels.insert(label.clone());

                let left = match **rule {
                    Rule::Empty => None,
                    Rule::Concat(_, (_, ref label)) | Rule::Alternation(ref label, _) => {
                        Some(label.clone())
                    }
                };
                let right = match *unit {
                    Unit::Rule(ref r) => Some(ParseLabel::new(r)),
                    Unit::Atom(_) => None,
                };
                parse_label_kinds.insert((label.clone(), ParseLabelKind::Binary(left, right)));

                label.clone()
            }
            Rule::Alternation(ref mut label, ref units) => {
                assert!(units.len() > 1);
                let mut s = String::from("(");
                for (i, unit) in units.iter().enumerate() {
                    if i > 0 {
                        s.push_str(" | ");
                    }
                    s.push_str(&unit.to_label_description());
                }
                s.push(')');
                *label = ParseLabel::new(&s);
                parse_labels.insert(label.clone());
                parse_label_kinds.insert((label.clone(), ParseLabelKind::Choice));
                label.clone()
            }
        }
    }
}

#[derive(Clone)]
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

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
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
impl<A: Atom> Grammar<A> {
    pub fn generate(&mut self, out: &mut Write) {
        macro put($($x:expr),*) {{ $(write!(out, "{}", $x).unwrap();)* }}

        let mut parse_labels = BTreeSet::new();
        let mut parse_label_kinds = BTreeSet::new();
        for (name, rule) in &mut self.rules {
            let inner = rule.rule.compute_parse_labels(&mut parse_labels, &mut parse_label_kinds);
            parse_labels.insert(ParseLabel::new(name));
            parse_label_kinds.insert((ParseLabel::new(name), ParseLabelKind::Unary(Some(inner))));
        }
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
        self.parser.sppf.unary_children(node).flat_map(move |node|");
            let mut cx = RuleContext {
                out,
                name,
                code_labels: &mut code_labels,
                code_label_counter: 0,
            };
            cx.generate_traverse(&rule.rule);

            put!(")
            .map(move |_r| ", name, " {");
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
    while let Some(Call { callee: (mut c, mut _result), range }) = p.gss.threads.steal() {
        match c.code {");
        for (name, rule) in &self.rules {
            put!("
            _C::", name, " => {");
            code_labels.push(name.clone());
            let mut cx = RuleContext {
                out,
                name,
                code_labels: &mut code_labels,
                code_label_counter: 0,
            };
            cx.generate_parse(&rule.rule);
            put!("
                p.sppf.add(", ParseLabel::new(name), ", _result, 0);
                p.gss.ret(c.stack, _result);
            }");
        }
        put!("
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum _P {");
        for i in 0..parse_labels.len() {
            put!(
                "
    _", i, ",");
        }
        put!("
}

macro P {");
        for (i, l) in parse_labels.iter().enumerate() {
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
        for l in parse_labels.iter() {
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
        for (label, kind) in parse_label_kinds {
            put!("
                ", label, " => ParseLabelKind::");
            match kind {
                ParseLabelKind::Unary(inner) => {
                    put!("Unary(");
                    match inner {
                        Some(x) => put!("Some(", x, ")"),
                        None => put!("None"),
                    }
                    put!("),");
                }
                ParseLabelKind::Binary(left, right) => {
                    put!("Binary(");
                    match left {
                        Some(x) => put!("Some(", x, ")"),
                        None => put!("None"),
                    }
                    put!(", ");
                    match right {
                        Some(x) => put!("Some(", x, ")"),
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

        for (i, l) in parse_labels.iter().enumerate() {
            put!("
            ", i, " => ", l, ",");
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

struct RuleContext<'a> {
    out: &'a mut Write,
    name: &'a str,
    code_labels: &'a mut Vec<String>,
    code_label_counter: usize,
}

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<'a> RuleContext<'a> {
    fn make_code_label(&mut self) -> String {
        self.code_label_counter += 1;
        let next_code_label = format!("{}__{}", self.name, self.code_label_counter);
        self.code_labels.push(next_code_label.clone());
        next_code_label
    }
    fn generate_parse_unit<A: Atom>(&mut self, unit: &Unit<A>) {
        macro put($($x:expr),*) {{ $(write!(self.out, "{}", $x).unwrap();)* }}

        match *unit {
            Unit::Rule(ref r) => put!("
                p.gss.call(Call { callee: _C::", r, ", range }, c);"),
            Unit::Atom(ref a) => {
                let a = a.to_rust_slice();
                put!("
                if !p.input[range.0].starts_with(", a, ") {
                    continue;
                }
                let (matched, rest, _) = range.split_at(", a, ".len());
                _result = Range(matched);
                p.gss.threads.spawn(c, _result, Range(rest));")
            }
        }
    }
    fn generate_parse<A: Atom>(&mut self, rule: &Rule<A>) {
        macro put($($x:expr),*) {{ $(write!(self.out, "{}", $x).unwrap();)* }}

        match *rule {
            Rule::Empty => {
                put!("
                _result = Range(range.frontiers().0);");
            }
            Rule::Concat(ref rule, (ref unit, ref label_after)) => {
                self.generate_parse(rule);
                let next_code_label = self.make_code_label();
                put!("
                c.code = _C::", next_code_label, ";");
                self.generate_parse_unit(unit);
                put!("
            }
            _C::", next_code_label, " => {
                _result = Range(c.stack.range.split_at(c.state + _result.len()).0);
                p.sppf.add(", label_after, ", _result, c.state);
                c.state = _result.len();");
            }
            Rule::Alternation(ref label, ref rules) => {
                let return_label = self.make_code_label();
                put!("
                c.code = _C::", return_label, ";");
                for unit in rules {
                    match *unit {
                        Unit::Rule(ref r) => put!("
                c.state = ", ParseLabel::new(r), ".to_usize();"),
                        Unit::Atom(..) => unimplemented!(),
                    }
                    self.generate_parse_unit(unit);
                }
                put!("
            }
            _C::", return_label, " => {
                p.sppf.add(", label, ", _result, c.state);");
            }
        }
    }
    fn generate_traverse<A: Atom>(&mut self, rule: &Rule<A>) {
        macro put($($x:expr),*) {{ $(write!(self.out, "{}", $x).unwrap();)* }}

        match *rule {
            Rule::Empty => {
                put!("
        ::std::iter::once(node.range)");
            }
            Rule::Concat(ref rule, _) => {
                put!("
        self.parser.sppf.binary_children(node).flat_map(move |(node, right)|");
                self.generate_traverse(rule);
                put!(".map(move |left| (left, right.range)))");
            }
            Rule::Alternation(_, ref choices) => {
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
    }
}
