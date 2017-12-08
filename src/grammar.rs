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
    arms: OrderMap<Symbol, Arm<A>>,
}

impl<A> Rule<A> {
    pub fn new() -> Self {
        Rule {
            label: Label::empty(),
            arms: OrderMap::new(),
        }
    }
    pub fn add_arm(&mut self, name: &str, arm: Arm<A>) {
        self.arms.insert(Symbol::from(name), arm);
    }
}

pub struct Arm<A> {
    units: Vec<Unit<A>>,
    labels: Vec<Label>,
}

impl<A> Arm<A> {
    pub fn new(units: Vec<Unit<A>>) -> Self {
        Arm {
            units,
            labels: vec![],
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
        $(grammar.add_rule(stringify!($rule_name), {
            let mut rule = Rule::new();
            $(rule.add_arm(stringify!($arm_name), Arm::new(vec![$(grammar!(@unit $unit)),*]));)*
            rule
        });)*
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
            for (arm_name, arm) in &mut rule.arms {
                for i in 0..arm.units.len() + 1 {
                    let mut s = format!("{}.{} ::=", rule_name, arm_name);
                    for (j, unit) in arm.units.iter().enumerate() {
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
                    if i == arm.units.len() {
                        s.push('·');
                    }
                    arm.labels.push(Label::new(&s));
                }
            }
        }
        let labels: Vec<_> = iter::once(self.l0)
            .chain(self.rules.values().flat_map(|rule| {
                iter::once(rule.label).chain(
                    rule.arms
                        .values()
                        .flat_map(|arm| arm.labels.iter().cloned()),
                )
            }))
            .collect();
        let entry_rule_label = self.rules.values().next().unwrap().label;

        put!("extern crate gll;

use self::gll::{Candidate, Label, ParseNode, Parser, StackNode};
use std::fmt;

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
            for arm in rule.arms.values() {
                for (i, unit) in arm.units.iter().enumerate() {
                    if let Unit::Rule(r) = *unit {
                        put!("
            ", arm.labels[i + 1], " => Some(", self.rules[&r].label, "),");
                    }
                }
            }
        }
        put!("
            _ => None,
        }
    }
}

pub fn parse(input: &str) -> Parser<", self.name, "> {
    let mut p = Parser::default();
    let mut c = Candidate {
        l: ", entry_rule_label, ",
        u: StackNode { l: ", entry_rule_label, ", i: 0 },
        i: 0,
        w: ParseNode::DUMMY,
    };
    loop {
        match c.l {
            ", self.l0, " => if let Some(next) = p.candidates.remove() {
                c = next;
            } else {
                return p;
            },");
        for rule in self.rules.values() {
            put!("
            ", rule.label, " => {");
            for arm in rule.arms.values() {
                put!("
                p.candidates
                    .add(", arm.labels[0], ", c.u, c.i, ParseNode::DUMMY);")
            }
            put!("
                c.l = ", self.l0, ";
            }");
            for arm in rule.arms.values() {
                for (i, unit) in arm.units.iter().enumerate() {
                    match *unit {
                        Unit::Rule(r) => put!("
            ", arm.labels[i], " => {
                c.u = p.create(", arm.labels[i + 1], ", c.u, c.i, c.w);
                c.l = ", self.rules[&r].label, ";
            }"),
                        Unit::Atom(ref a) => {
                            let a = a.to_rust_slice();
                            put!("
            ", arm.labels[i], " => if input[c.i..].starts_with(", a, ") {
                let j = c.i + ", a, ".len();
                let c_r = ParseNode::terminal(c.i, j);
                c.i = j;
                c.w = p.sppf.add_packed(", arm.labels[i + 1], ", c.w, c_r);
                c.l = ", arm.labels[i + 1], ";
            } else {
                c.l = ", self.l0, ";
            },")
                        }
                    }
                }

                put!("
            ", arm.labels[arm.units.len()], " => {
                c.w = p.sppf.add_packed(", rule.label, ", ParseNode::DUMMY, c.w);
                p.pop(c.u, c.i, c.w);
                c.l = ", self.l0, ";
            }");
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
