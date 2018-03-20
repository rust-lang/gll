use ordermap::OrderMap;
use std::fmt;
use std::io::{self, Write};
use std::iter;
use std::slice;

pub struct Grammar<A> {
    rules: OrderMap<String, Rule<A>>,
}

impl<A> Grammar<A> {
    pub fn new() -> Self {
        Grammar {
            rules: OrderMap::new(),
        }
    }
    pub fn add_rule(&mut self, name: &str, rule: Rule<A>) {
        self.rules.insert(name.to_string(), rule);
    }
}

pub struct Rule<A> {
    label: Label,
    kind: RuleKind<A>,
}

pub enum RuleKind<A> {
    Sequence(Sequence<A>),
    Alternation(Label, Vec<String>),
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
            kind: RuleKind::Alternation(
                Label::empty(),
                rules.iter().map(|&r| r.to_string()).collect(),
            ),
        }
    }
    fn start_label(&self) -> &Label {
        match self.kind {
            RuleKind::Sequence(ref seq) => if seq.units.is_empty() {
                &self.label
            } else {
                &seq.labels_before[0]
            },
            RuleKind::Alternation(_, _) => &self.label,
        }
    }
}

pub struct Sequence<A> {
    units: Vec<(Option<String>, Unit<A>)>,
    labels_before: Vec<Label>,
}

impl<A> Sequence<A> {
    pub fn new(units: Vec<(Option<String>, Unit<A>)>) -> Self {
        Sequence {
            units,
            labels_before: vec![],
        }
    }
}

pub enum Unit<A> {
    Atom(A),
    Rule(String),
}

impl<A> Unit<A> {
    pub fn rule(r: &str) -> Self {
        Unit::Rule(r.to_string())
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

#[derive(Clone)]
pub struct Label {
    pub description: String,
}

impl Label {
    fn new(s: &str) -> Label {
        Label {
            description: s.to_string(),
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
    (@unit { $name:ident : $unit:tt }) => {
        (Some(stringify!($name).to_string()), grammar!(@unit $unit).1)
    },
    (@unit $rule:ident) => {
        (None::<String>, Unit::rule(stringify!($rule)))
    },
    (@unit $atom:expr) => {
        (None::<String>, Unit::Atom($atom))
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
                        for (j, &(ref name, ref unit)) in seq.units.iter().enumerate() {
                            if i == j {
                                s.push('·');
                            } else {
                                s.push(' ');
                            }
                            if let Some(ref name) = *name {
                               s.push_str(name);
                               s.push(':');
                            }
                            match *unit {
                                Unit::Atom(ref a) => {
                                    s.push_str(&a.to_label_description());
                                }
                                Unit::Rule(ref r) => {
                                    s.push_str(&r.as_str());
                                }
                            }
                        }
                        seq.labels_before.push(Label::new(&s));
                    }
                }
                RuleKind::Alternation(ref mut return_label, _) => {
                    *return_label = Label::new(&format!("{} ::=·", rule_name));
                }
            }
        }
        let labels: Vec<_> = self.rules.values().flat_map(|rule| {
            let labels = match rule.kind {
                RuleKind::Sequence(ref seq) => &seq.labels_before[..],
                RuleKind::Alternation(ref l, _) => slice::from_ref(l),
            };
            iter::once(&rule.label).chain(labels.iter())
        })
        .collect();

        put!("extern crate gll;

use self::gll::{Call, Continuation, Label, LabelKind, ParseNode, Range};
use std::fmt;
use std::marker::PhantomData;

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

impl Label for _L {
    fn kind(self) -> LabelKind<Self> {
        match self {");
        for rule in self.rules.values() {
            match rule.kind {
                RuleKind::Alternation(ref return_label, _) => {
                    put!("
            ", rule.label, " => LabelKind::Choice,
            ", return_label, " => unreachable!(),");
                }
                RuleKind::Sequence(ref seq) => {
                    if seq.units.is_empty() {
                        put!("
            ", rule.label, " => LabelKind::Unary(None),");
                    }
                    for (i, &(_, ref unit)) in seq.units.iter().enumerate() {
                        let next_label = if i == seq.units.len() - 1 {
                            &rule.label
                        } else {
                            &seq.labels_before[i + 1]
                        };
                        if i == 0 {
                            put!("
            ", seq.labels_before[i], " => unreachable!(),");
                        }
                        put!("
            ", next_label, " => LabelKind::");
                        if i == 0 {
                            put!("Unary(");
                        } else {
                            put!("Binary(");
                            if i == 1 {
                                match seq.units[i - 1].1 {
                                    Unit::Rule(ref r) => put!("Some(", self.rules[r].label, ")"),
                                    Unit::Atom(_) => put!("None"),
                                }
                            } else {
                                put!("Some(", seq.labels_before[i], ")");
                            }
                            put!(", ");
                        }
                        match *unit {
                            Unit::Rule(ref r) => put!("Some(", self.rules[r].label, ")"),
                            Unit::Atom(_) => put!("None"),
                        }
                        put!("),");
                    }
                }
            }
        }
        put!("
        }
    }
    fn from_usize(i: usize) -> Self {
        match i {");

        for (i, l) in labels.iter().enumerate() {
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
");
        for (name, rule) in &self.rules {
            match rule.kind {
                RuleKind::Sequence(ref seq) => {
                    put!("

#[derive(Debug)]
pub struct ", name, "<'a, 'b: 'a, 'id: 'a> {");
                    let mut has_named_units = false;
                    for &(ref unit_name, ref unit) in &seq.units {
                        if let Some(ref unit_name) = *unit_name {
                            if let Unit::Rule(ref r) = *unit {
                                put!("
    pub ", unit_name, ": Handle<'a, 'b, 'id, ", r, "<'a, 'b, 'id>>,");
                                has_named_units = true;
                            }
                        }
                    }
                    if !has_named_units {
                        put!("
    _marker: PhantomData<(&'a (), &'b (), &'id ())>,");
                    }
                    put!("
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
            }");
                    if has_named_units {
                        put!("
            fmt::Debug::fmt(&_x, f)?;");
                    } else {
                        put!("
            write!(f, \"", name, "\")?;");
                    }
                    put!("
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
    pub fn many(self) -> impl Iterator<Item = ", name, "<'a, 'b, 'id>> {");
                    if seq.units.len() == 0 {
                        put!("
        ::std::iter::once(", name, " {
             _marker: PhantomData,
        })");
                    } else {
                        put!("
        let node = ParseNode { l: Some(", rule.label, "), range: self.span };");
                        if seq.units.len() == 1 {
                            put!("
        self.parser.sppf.unary_children(node)");
                        } else {
                            put!("
        self.parser.sppf.binary_children(node)");
                            for _ in 0..seq.units.len() - 2 {
                                put!("
            .flat_map(move |(left, right)| self.parser.sppf.binary_children(left).map(move |left| (left, right)))");
                            }
                        }
                        put!("
            .map(move |");
                        for _ in 0..seq.units.len() - 1 {
                            put!("(");
                        }
                        for (i, &(ref unit_name, ref unit)) in seq.units.iter().enumerate() {
                            if i > 0 {
                                put!(", ");
                            }
                            if let Some(ref unit_name) = *unit_name {
                                if let Unit::Rule(_) = *unit {
                                    put!(unit_name);
                                } else {
                                    put!("_");
                                }
                            } else {
                                put!("_");
                            }
                            if i > 0 {
                                put!(")");
                            }
                        }
                        put!("| ", name, " {");
                        for &(ref unit_name, ref unit) in &seq.units {
                            if let Some(ref unit_name) = *unit_name {
                                if let Unit::Rule(_) = *unit {
                                    put!("
                ", unit_name, ": Handle {
                    span: ", unit_name, ".range,
                    parser: self.parser,
                    _marker: PhantomData,
                },");
                                }
                            }
                        }
                        if !has_named_units {
                            put!("
                _marker: PhantomData,");
                        }
                        put!("
            })");
                    }
                    put!("
    }
}
");
                }
                RuleKind::Alternation(_, ref rules) => {
                    put!("

pub enum ", name, "<'a, 'b: 'a, 'id: 'a> {");
                    for r in rules {
                        put!("
    ", r, "(Handle<'a, 'b, 'id, ", r, "<'a, 'b, 'id>>),");
                    }
                    put!("
}

impl<'a, 'b, 'id> fmt::Debug for ", name, "<'a, 'b, 'id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {");
                    for r in rules {
                        put!("
            ", name, "::", r, "(ref x) => fmt::Debug::fmt(x, f),");
                    }
                    put!("
        }
    }
}

impl<'a, 'b, 'id> fmt::Debug for Handle<'a, 'b, 'id, ", name, "<'a, 'b, 'id>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, x) in self.many().enumerate() {
            if i > 0 {
                write!(f, \" | \")?;
            }
            fmt::Debug::fmt(&x, f)?;
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
        let node = ParseNode { l: Some(", rule.label, "), range: self.span };
        self.parser.sppf.children[&node].iter().map(move |&i| {
            match _L::from_usize(i) {");
                    for r in rules {
                        put!("
                ", self.rules[r].label," => ", name, "::", r, "(Handle {
                    span: self.span,
                    parser: self.parser,
                    _marker: PhantomData,
                }),");
                    }
                    put!("
                _ => unreachable!(),
            }
        })
    }
}
");
                }
            }

            put!("

impl<'a, 'b, 'id> ", name, "<'a, 'b, 'id> {
    pub fn parse(p: &'a mut Parser<'b, 'id>) -> Result<Handle<'a, 'b, 'id, Self>, ()> {
        let call = Call {
            callee: ", rule.start_label(), ",
            range: Range(p.input.range()),
        };
        if !p.gss.results.contains_key(&call) {
            let dummy = Range(p.input.empty_range());
            p.gss.threads.spawn(
                Continuation {
                    code: ", rule.start_label(), ",
                    stack: call,
                    state: 0,
                },
                dummy,
                call.range,
            );
            parse(p);
        }
        if let Some(results) = p.gss.results.get(&call) {
            if let Some(&r) = results.iter().rev().next() {
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
    while let Some(Call { callee: (mut c, mut result), range }) = p.gss.threads.steal() {
        match c.code {");
        for rule in self.rules.values() {
            match rule.kind {
                RuleKind::Alternation(ref return_label, ref rules) => {
                    put!("
            ", rule.label, " => {
                c.code = ", return_label, ";");
                    for r in rules {
                        put!("
                c.state = ", self.rules[r].label, ".to_usize();
                p.gss.call(Call { callee: ", self.rules[r].start_label(), ", range }, c);")
                    }
                    put!("
            }
            ", return_label, " => {
                p.sppf.add(", rule.label, ", result, c.state);
                p.gss.ret(c.stack, result);
            }");
                }
                RuleKind::Sequence(ref seq) => {
                    for (i, &(_, ref unit)) in seq.units.iter().enumerate() {
                        let next_label = if i == seq.units.len() - 1 {
                            &rule.label
                        } else {
                            &seq.labels_before[i + 1]
                        };
                        if i == 0 {
                            put!("
            ", seq.labels_before[i], " => {");
                        }
                        match *unit {
                            Unit::Rule(ref r) => put!("
                c.code = ", next_label, ";
                p.gss.call(Call { callee: ", self.rules[r].start_label(), ", range }, c);
            }"),
                            Unit::Atom(ref a) => {
                                let a = a.to_rust_slice();
                                put!("
                if !p.input[range.0].starts_with(", a, ") {
                    continue;
                }
                let (matched, rest, _) = range.split_at(", a, ".len());
                result = Range(matched);
                c.code = ", next_label, ";
                p.gss.threads.spawn(c, result, Range(rest));
            }")
                            }
                        }
                        put!("
            ", next_label, " => {");
                        if i == 0 {
                            if seq.units.len() == 1 {
                                put!("
                p.sppf.add(", next_label, ", result, 0);");
                            }
                        } else {
                            put!("
                result = Range(c.stack.range.split_at(c.state + result.len()).0);
                p.sppf.add(", next_label, ", result, c.state);");
                        }
                        put!("
                c.state = result.len();");
                    }

                    if seq.units.is_empty() {
                        put!("
            ", rule.label, " => {
                result = Range(range.frontiers().0);
                p.sppf.add(", rule.label, ", result, 0);");
                    }
                    put!("
                p.gss.ret(c.stack, result);
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
