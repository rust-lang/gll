use ordermap::OrderMap;
use std::fmt;
use std::io::{self, Write};
use std::iter;
use syntax::symbol::Symbol;

pub struct Grammar<A> {
    name: Symbol,
    l0: Label,
    rules: OrderMap<Symbol, Rule<A>>,
}

impl<A> Grammar<A> {
    pub fn new(name: &str) -> Self {
        Grammar {
            name: Symbol::from(name),
            l0: Label::empty(),
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
    Alternation(Vec<Symbol>),
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
            kind: RuleKind::Alternation(rules.iter().map(|&r| Symbol::from(r)).collect()),
        }
    }
    fn start_label(&self) -> Label {
        match self.kind {
            RuleKind::Sequence(ref seq) => if seq.units.is_empty() {
                self.label
            } else {
                seq.labels_before[0]
            },
            RuleKind::Alternation(_) => self.label,
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
        format!("{:?}", self)
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
    ($grammar_name:ident; $($rule_name:ident =
        $($arm_name:ident { $($unit:tt)* })|+;
    )*) => ({
        let mut grammar = Grammar::new(stringify!($grammar_name));
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
        self.l0 = Label::new("L₀");
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
                RuleKind::Alternation(_) => {}
            }
        }
        let labels: Vec<_> = iter::once(self.l0)
            .chain(self.rules.values().flat_map(|rule| {
                let labels = match rule.kind {
                    RuleKind::Sequence(ref seq) => &seq.labels_before[..],
                    RuleKind::Alternation(_) => &[],
                };
                iter::once(rule.label).chain(labels.iter().cloned())
            }))
            .collect();

        put!("extern crate gll;

use self::gll::{Candidate, Label, ParseNode, StackNode};
use std::fmt;

pub type Parser<'a> = gll::Parser<", self.name, ", &'a str>;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum ", self.name, " {");
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
    (\"", l.description, "\") => (", self.name, "::_", i, ");");
        }
        put!("
}

impl Default for ", self.name, " {
    fn default() -> ", self.name, " {
        ", self.l0,"
    }
}

impl fmt::Display for ", self.name, " {
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

impl Label for ", self.name, " {
    fn nonterminal_before_dot(&self) -> Option<Gamma0> {
        match *self {");
        for rule in self.rules.values() {
            match rule.kind {
                RuleKind::Sequence(ref seq) => {
                    for (i, unit) in seq.units.iter().enumerate() {
                        if let Unit::Rule(r) = *unit {
                            let next_label = if i == seq.units.len() - 1 {
                                rule.label
                            } else {
                                seq.labels_before[i + 1]
                            };
                            put!("
            ", next_label, " => Some(", self.rules[&r].label, "),");
                        }
                    }
                }
                RuleKind::Alternation(_) => {}
            }
        }
        put!("
            _ => None,
        }
    }
}");
        for (name, rule) in &self.rules {
            put!("

pub struct ", name, ";

impl ", name, " {
    pub fn parse(p: &mut Parser) {
        p.candidates.add(", rule.start_label(), ", StackNode {
            l: ", rule.start_label(), ",
            i: 0
        }, 0, ParseNode::DUMMY);
        parse(p);
    }
}");
        }
        put!("
fn parse(p: &mut Parser) {
    let mut c = Candidate {
        l: ", self.l0, ",
        u: StackNode { l: ", self.l0, ", i: 0 },
        i: 0,
        w: ParseNode::DUMMY,
    };
    loop {
        match c.l {
            ", self.l0, " => if let Some(next) = p.candidates.remove() {
                c = next;
            } else {
                return;
            },");
        for rule in self.rules.values() {
            match rule.kind {
                RuleKind::Alternation(ref rules) => {
                    put!("
            ", rule.label, " => {");
                    for r in rules {
                        put!("
                p.candidates.add(", self.rules[r].start_label(), ", c.u, c.i, ParseNode::DUMMY);")
                    }
                    put!("
                c.l = ", self.l0, ";
            }");
                }
                RuleKind::Sequence(ref seq) => {
                    for (i, unit) in seq.units.iter().enumerate() {
                        let next_label = if i == seq.units.len() - 1 {
                            rule.label
                        } else {
                            seq.labels_before[i + 1]
                        };
                        match *unit {
                            Unit::Rule(r) => put!("
            ", seq.labels_before[i], " => {
                c.u = p.create(", next_label, ", c.u, c.i, c.w);
                c.l = ", self.rules[&r].start_label(), ";
            }"),
                            Unit::Atom(ref a) => {
                                let a = a.to_rust_slice();
                                put!("
            ", seq.labels_before[i], " => if p.input[c.i..].starts_with(", a, ") {
                let j = c.i + ", a, ".len();
                let c_r = ParseNode::terminal(c.i, j);
                c.i = j;
                c.w = p.sppf.add_packed(", next_label, ", c.w, c_r);
                c.l = ", next_label, ";
            } else {
                c.l = ", self.l0, ";
            },")
                            }
                        }
                    }

                    put!("
            ", rule.label, " => {
                p.pop(c.u, c.i, c.w);
                c.l = ", self.l0, ";
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
