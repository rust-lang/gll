use ordermap::OrderMap;
use std::fmt;
use std::io::{self, Write};
use std::iter;
use syntax::symbol::Symbol;

pub struct Grammar<A> {
    rules: OrderMap<Symbol, Rule<A>>,
}

impl<A> Grammar<A> {
    pub fn new() -> Self {
        Grammar {
            rules: OrderMap::new(),
        }
    }
    pub fn add_rule(&mut self, name: &str, rule: Rule<A>) {
        self.rules.insert(Symbol::from(name), rule);
    }
}

pub struct Rule<A> {
    label: Label,
    kind: RuleKind<A>,
}

pub enum RuleKind<A> {
    Sequence(Sequence<A>),
    Alternation(Vec<Label>, Vec<Symbol>),
}

impl<A> Rule<A> {
    pub fn sequence(seq: Sequence<A>) -> Self {
        Rule {
            label: Label::empty(),
            kind: RuleKind::Sequence(seq),
        }
    }
    pub fn alternation(rules: &[&str]) -> Self {
        Rule {
            label: Label::empty(),
            kind: RuleKind::Alternation(vec![], rules.iter().map(|&r| Symbol::from(r)).collect()),
        }
    }
    fn start_label(&self) -> Label {
        match self.kind {
            RuleKind::Sequence(ref seq) => if seq.units.is_empty() {
                self.label
            } else {
                seq.labels_before[0]
            },
            RuleKind::Alternation(_, _) => self.label,
        }
    }
}

pub struct Sequence<A> {
    units: Vec<Unit<A>>,
    labels_before: Vec<Label>,
}

impl<A> Sequence<A> {
    pub fn new(units: Vec<Unit<A>>) -> Self {
        Sequence {
            units,
            labels_before: vec![],
        }
    }
}

pub enum Unit<A> {
    Atom(A),
    Rule(Symbol),
}

impl<A> Unit<A> {
    pub fn rule(r: &str) -> Self {
        Unit::Rule(Symbol::from(r))
    }
}

pub trait Atom {
    fn to_label_description(&self) -> String;
    fn to_rust_slice(&self) -> String;
}

impl Atom for str {
    fn to_label_description(&self) -> String {
        format!("'{}'", self.escape_default())
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

#[derive(Copy, Clone)]
pub struct Label {
    pub description: Symbol,
}

impl Label {
    fn new(s: &str) -> Label {
        Label {
            description: Symbol::from(s),
        }
    }
    fn empty() -> Label {
        Label::new("")
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, r#"L!("{}")"#, self.description)
    }
}

pub macro grammar {
    (@unit $rule:ident) => {
        Unit::rule(stringify!($rule))
    },
    (@unit $atom:expr) => {
        Unit::Atom($atom)
    },
    ($($rule_name:ident =
        $($arm_name:ident { $($unit:tt)* })|+;
    )*) => ({
        let mut grammar = Grammar::new();
        $(
            grammar.add_rule(stringify!($rule_name),
                Rule::alternation(&[$(stringify!($arm_name)),*]));
            $(grammar.add_rule(stringify!($arm_name),
                Rule::sequence(Sequence::new(vec![$(grammar!(@unit $unit)),*])));)*
        )*
        grammar
    })
}

impl<A: Atom> Grammar<A> {
    #[cfg_attr(rustfmt, rustfmt_skip)]
    pub fn generate(&mut self, out: &mut Write) -> io::Result<()> {
        macro_rules! put {
            ($($x:expr),*) => ({
                $(write!(out, "{}", $x)?;)*
            })
        }
        for (rule_name, rule) in &mut self.rules {
            rule.label = Label::new(&rule_name.as_str());
            match rule.kind {
                RuleKind::Sequence(ref mut seq) => {
                    for i in 0..seq.units.len() {
                        let mut s = format!("{} ::=", rule_name);
                        for (j, unit) in seq.units.iter().enumerate() {
                            if i == j {
                                s.push('·');
                            } else {
                                s.push(' ');
                            }
                            match *unit {
                                Unit::Atom(ref a) => {
                                    s.push_str(&a.to_label_description());
                                }
                                Unit::Rule(r) => {
                                    s.push_str(&r.as_str());
                                }
                            }
                        }
                        seq.labels_before.push(Label::new(&s));
                    }
                }
                RuleKind::Alternation(ref mut return_labels, ref rules) => {
                    for r in rules {
                        return_labels.push(Label::new(&format!("{} ::= {}·", rule_name, r)));
                    }
                }
            }
        }
        let labels: Vec<_> = self.rules.values().flat_map(|rule| {
            let labels = match rule.kind {
                RuleKind::Sequence(ref seq) => &seq.labels_before[..],
                RuleKind::Alternation(ref labels, _) => labels,
            };
            iter::once(rule.label).chain(labels.iter().cloned())
        })
        .collect();

        put!("extern crate gll;

use self::gll::{Call, Continuation, Label, ParseNode, Range};
use std::fmt;

pub type Parser<'a, 'id> = gll::Parser<'id, _L, &'a [u8]>;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum _L {");
        for i in 0..labels.len() {
            put!(
                "
    _", i, ",");
        }
        put!("
}

macro_rules! L {");
        for (i, l) in labels.iter().enumerate() {
            put!("
    (\"", l.description, "\") => (_L::_", i, ");");
        }
        put!("
}

impl fmt::Display for _L {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match *self {");

        for l in labels.iter() {
            put!("
            ", l, " => \"", l.description, "\",");
        }
        put!("
        };
        write!(f, \"{}\", s)
    }
}

impl Label for _L {}");
        for (name, rule) in &self.rules {
            put!("

pub struct ", name, "<'id> {
    pub span: Range<'id>,
}

impl<'id> ", name, "<'id> {
    pub fn parse<'a>(p: &mut Parser<'a, 'id>) -> Result<Self, ()> {
        let call = Call {
            callee: ", rule.start_label(), ",
            range: Range(p.input.range()),
        };
        if !p.gss.results.contains_key(&call) {
            let dummy = Range(p.input.empty_range());
            p.gss.threads.spawn(Continuation { code: ", rule.start_label(), ", stack: call, left: dummy }, dummy, call.range);
            parse(p);
        }
        if let Some(results) = p.gss.results.get(&call) {
            if let Some(&r) = results.iter().rev().next() {
                return Ok(Self {
                    span: r
                });
            }
        }
        Err(())
    }
}");
        }
        put!("
fn parse(p: &mut Parser) {
    while let Some(Call { callee: (mut c, mut right), range }) = p.gss.threads.steal() {
        match c.code {");
        for rule in self.rules.values() {
            match rule.kind {
                RuleKind::Alternation(ref return_labels, ref rules) => {
                    put!("
            ", rule.label, " => {");
                    for (i, r) in rules.iter().enumerate() {
                        put!("
                c.code = ", return_labels[i], ";
                p.gss.call(Call { callee: ", self.rules[r].start_label(), ", range }, c);")
                    }
                    put!("
            }");
                    for (i, r) in rules.iter().enumerate() {
                        put!("
            ", return_labels[i], " => {
                c.left = p.sppf.add_unary(", rule.label, ", ParseNode { l: Some(", self.rules[r].label, "), range: right }).range;
                p.gss.ret(c.stack, c.left);
            }");
                    }
                }
                RuleKind::Sequence(ref seq) => {
                    for (i, unit) in seq.units.iter().enumerate() {
                        let next_label = if i == seq.units.len() - 1 {
                            rule.label
                        } else {
                            seq.labels_before[i + 1]
                        };
                        if i == 0 {
                            put!("
            ", seq.labels_before[i], " => {");
                        }
                        match *unit {
                            Unit::Rule(r) => put!("
                c.code = ", next_label, ";
                p.gss.call(Call { callee: ", self.rules[&r].start_label(), ", range }, c);
            }"),
                            Unit::Atom(ref a) => {
                                let a = a.to_rust_slice();
                                put!("
                if !p.input[range.0].starts_with(", a, ") {
                    continue;
                }
                let (matched, rest, _) = range.split_at(", a, ".len());
                right = Range(matched);
                p.gss.threads.spawn(Continuation { code: ", next_label, ", ..c }, right, Range(rest));
            }")
                            }
                        }
                        put!("
            ", next_label, " => {");
                        if i == 0 {
                            put!("
                c.left = p.sppf.add_unary(", next_label);
                        } else {
                            put!("
                c.left = p.sppf.add_binary(", next_label, ", ParseNode { l: Some(", seq.labels_before[i], "), range: c.left }");
                        }
                        match *unit {
                            Unit::Rule(r) => {
                                put!(", ParseNode { l: Some(", self.rules[&r].label, "), range: right }).range;");
                            }
                            Unit::Atom(_) => {
                                put!(", ParseNode::terminal(right)).range;");
                            }
                        }
                    }

                    if seq.units.is_empty() {
                        put!("
            ", rule.label, " => {
                right = Range(range.frontiers().0);
                c.left = p.sppf.add_unary(", rule.label, ", ParseNode::terminal(right)).range;");
                    }
                    put!("
                p.gss.ret(c.stack, c.left);
            }");
                }
            }
        }

        put!("
        }
    }
}
");
        Ok(())
    }
}
