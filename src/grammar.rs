use ordermap::OrderMap;
use std::fmt;
use std::io::Write;

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
    fields: OrderMap<String, usize>,
}

impl<A: Clone> RuleWithNamedFields<A> {
    pub fn empty() -> Self {
        RuleWithNamedFields {
            rule: Rule::Sequence(vec![]),
            fields: OrderMap::new(),
        }
    }
    pub fn unit(unit: Unit<A>) -> Self {
        RuleWithNamedFields {
            rule: Rule::Sequence(vec![(unit, ParseLabel::empty())]),
            fields: OrderMap::new(),
        }
    }
    pub fn alternation(rules: Vec<Self>) -> Self {
        let mut fields = OrderMap::new();
        let choices = rules
            .into_iter()
            .enumerate()
            .map(|(i, rule)| {
                fields.extend(rule.fields.into_iter().map(|(name, j)| {
                    assert_eq!(j, 0);
                    (name, i)
                }));

                match rule.rule {
                    Rule::Sequence(units) => match units[..] {
                        [(ref unit, _)] => unit.clone(),
                        _ => unimplemented!(),
                    },
                    Rule::Alternation(..) => unimplemented!(),
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
            Rule::Sequence(ref units) => assert!(units.len() == 1),
            _ => unimplemented!(),
        }
        self.fields.insert(name.to_string(), 0);
        self
    }
    pub fn then(mut self, other: Self) -> Self {
        match (self.rule, other.rule) {
            (Rule::Sequence(mut self_units), Rule::Sequence(other_units)) => {
                self.fields.extend(
                    other
                        .fields
                        .into_iter()
                        .map(|(name, i)| (name, i + self_units.len())),
                );
                self_units.extend(other_units);
                self.rule = Rule::Sequence(self_units);
            }
            _ => unimplemented!(),
        }
        self
    }
}

pub enum Rule<A> {
    Sequence(Vec<(Unit<A>, ParseLabel)>),
    Alternation(ParseLabel, Vec<Unit<A>>),
}

impl<A: Atom> Rule<A> {
    fn field_type(&self, i: usize) -> &str {
        let unit = match *self {
            Rule::Sequence(ref units) => &units[i].0,
            Rule::Alternation(_, ref choices) => &choices[i],
        };
        match *unit {
            Unit::Rule(ref r) => r,
            Unit::Atom(_) => "Terminal",
        }
    }
    fn field_is_refutable(&self, _i: usize) -> bool {
        match *self {
            Rule::Sequence(_) => false,
            Rule::Alternation(..) => true,
        }
    }
    fn compute_parse_labels(&mut self, name: &str, parse_labels: &mut Vec<ParseLabel>) {
        match *self {
            Rule::Sequence(ref mut units) => for i in 0..units.len() {
                let mut s = format!("{} ::=", name);
                for (j, &(ref unit, _)) in units.iter().enumerate() {
                    if i + 1 == j {
                        s.push('·');
                        break;
                    } else {
                        s.push(' ');
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
                units[i].1 = ParseLabel::new(&s);
                parse_labels.push(units[i].1.clone());
            },
            Rule::Alternation(ref mut label, _) => {
                *label = ParseLabel::new(&format!("{} ::=·", name));
                parse_labels.push(label.clone());
            }
        }
    }
}

#[derive(Clone)]
pub enum Unit<A> {
    Atom(A),
    Rule(String),
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
        write!(f, r#"P!("{}")"#, self.description)
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

        let mut parse_labels = vec![];
        for (rule_name, rule) in &mut self.rules {
            rule.rule.compute_parse_labels(rule_name, &mut parse_labels);
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
            for (field_name, &i) in &rule.fields {
                let refutable = rule.rule.field_is_refutable(i);
                put!("
    pub ", field_name, ": ");
                if refutable {
                    put!("Option<");
                }
                put!("Handle<'a, 'b, 'id, ", rule.rule.field_type(i), "<'a, 'b, 'id>>");
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
        for (field_name, &i) in &rule.fields {
            if rule.rule.field_is_refutable(i) {
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
    pub fn many(self) -> impl Iterator<Item = ", name, "<'a, 'b, 'id>> {");
            let mut cx = RuleContext {
                out,
                name,
                code_labels: &mut code_labels,
            };
            cx.generate_traverse(&rule.rule, &rule.fields);
            put!("
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
    while let Some(Call { callee: (mut c, mut result), range }) = p.gss.threads.steal() {
        match c.code {");
        for (name, rule) in &self.rules {
            let mut cx = RuleContext {
                out,
                name,
                code_labels: &mut code_labels,
            };
            cx.generate_parse(&rule.rule);
        }
        put!("
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum _P {");
        for (name, _) in &self.rules {
            put!(
                "
    ", name, ",");
        }
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
    (\"", l.description, "\") => (_P::_", i, ")");
        }
        put!("
}

impl fmt::Display for _P {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match *self {");
        for (name, _) in &self.rules {
            put!(
                "
            _P::", name, " => \"", name, "\",");
        }
        for l in parse_labels.iter() {
            put!("
            ", l, " => \"", l.description, "\",");
        }
        put!("
        };
        write!(f, \"{}\", s)
    }
}

impl ParseLabel for _P {
    fn kind(self) -> ParseLabelKind<Self> {
        match self {");
        for (name, rule) in &self.rules {
            let mut cx = RuleContext {
                out,
                name,
                code_labels: &mut code_labels,
            };
            cx.generate_parse_label_kind(&rule.rule);
        }
        put!("
        }
    }
    fn from_usize(i: usize) -> Self {
        match i {");

        for (i, (name, _)) in self.rules.iter().enumerate() {
            put!(
                "
            ", i, " => _P::", name, ",");
        }
        for (i, l) in parse_labels.iter().enumerate() {
            put!("
            ", i + self.rules.len(), " => ", l, ",");
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
}

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<'a> RuleContext<'a> {
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
                result = Range(matched);
                p.gss.threads.spawn(c, result, Range(rest));")
            }
        }
    }
    fn generate_parse<A: Atom>(&mut self, rule: &Rule<A>) {
        macro put($($x:expr),*) {{ $(write!(self.out, "{}", $x).unwrap();)* }}

        put!("
            _C::", self.name, " => {");
        self.code_labels.push(self.name.clone().to_string());
        match *rule {
            Rule::Alternation(ref label, ref rules) => {
                let return_label = format!("{}__1", self.name);
                put!("
                c.code = _C::", return_label, ";");
                for unit in rules {
                    match *unit {
                        Unit::Rule(ref r) => put!("
                c.state = _P::", r, ".to_usize();"),
                        Unit::Atom(..) => unimplemented!(),
                    }
                    self.generate_parse_unit(unit);
                }
                put!("
            }
            _C::", return_label, " => {
                p.sppf.add(", label, ", result, c.state);");
                self.code_labels.push(return_label);
            }
            Rule::Sequence(ref units) => {
                for (i, &(ref unit, ref label_after)) in units.iter().enumerate() {
                    let next_code_label = format!("{}__{}", self.name, i + 1);
                    put!("
                c.code = _C::", next_code_label, ";");
                    self.generate_parse_unit(unit);
                    put!("
            }
            _C::", next_code_label, " => {");
                    self.code_labels.push(next_code_label);
                    if i == 0 {
                        if units.len() == 1 {
                            put!("
                p.sppf.add(", label_after, ", result, 0);");
                        }
                    } else {
                        put!("
                result = Range(c.stack.range.split_at(c.state + result.len()).0);
                p.sppf.add(", label_after, ", result, c.state);");
                    }
                    put!("
                c.state = result.len();");
                }

                if units.is_empty() {
                    put!("
                result = Range(range.frontiers().0);");
                }
            }
        }
        put!("
                p.sppf.add(_P::", self.name, ", result, 0);
                p.gss.ret(c.stack, result);
            }");
    }
    fn generate_parse_label_kind<A: Atom>(&mut self, rule: &Rule<A>){
        macro put($($x:expr),*) {{ $(write!(self.out, "{}", $x).unwrap();)* }}

        match *rule {
            Rule::Alternation(ref label, _) => {
                put!("
            _P::", self.name, " => ParseLabelKind::Unary(Some(", label, ")),
            ", label, " => ParseLabelKind::Choice,");
            }
            Rule::Sequence(ref units) => {
                if let Some(label) = units.last() {
                    put!("
            _P::", self.name, " => ParseLabelKind::Unary(Some(", label.1, ")),");
                } else {
                    put!("
            _P::", self.name, " => ParseLabelKind::Unary(None),");
                }
                for (i, &(ref unit, ref label_after)) in units.iter().enumerate() {
                    put!("
            ", label_after, " => ParseLabelKind::");
                    if i == 0 {
                        put!("Unary(");
                    } else {
                        put!("Binary(");
                        if i == 1 {
                            match units[i - 1].0 {
                                Unit::Rule(ref r) => put!("Some(_P::", r, ")"),
                                Unit::Atom(_) => put!("None"),
                            }
                        } else {
                            put!("Some(", units[i - 1].1, ")");
                        }
                        put!(", ");
                    }
                    match *unit {
                        Unit::Rule(ref r) => put!("Some(_P::", r, ")"),
                        Unit::Atom(_) => put!("None"),
                    }
                    put!("),");
                }
            }
        }
    }
    fn generate_traverse<A: Atom>(&mut self, rule: &Rule<A>, fields: &OrderMap<String, usize>) {
        macro put($($x:expr),*) {{ $(write!(self.out, "{}", $x).unwrap();)* }}

        match *rule {
            Rule::Sequence(ref units) => {
                if units.len() == 0 {
                    put!("
        ::std::iter::once(", self.name, " {
            _marker: PhantomData,
        })");
                } else {
                    put!("
        let node = ParseNode { l: Some(", units.last().unwrap().1, "), range: self.span };");
                    if units.len() == 1 {
                        put!("
        self.parser.sppf.unary_children(node)");
                    } else {
                        put!("
        self.parser.sppf.binary_children(node)");
                        for _ in 0..units.len() - 2 {
                            put!("
            .flat_map(move |(left, right)| self.parser.sppf.binary_children(left).map(move |left| (left, right)))");
                        }
                    }
                    put!("
            .map(move |");
                    for _ in 0..units.len() - 1 {
                        put!("(");
                    }
                    for i in 0..units.len() {
                        if i > 0 {
                            put!(", ");
                        }
                        put!("_", i);
                        if i > 0 {
                            put!(")");
                        }
                    }
                    put!("| ", self.name, " {");
                    for (field_name, &i) in fields {
                        put!("
                ", field_name, ": Handle {
                    span: _", i, ".range,
                    parser: self.parser,
                    _marker: PhantomData,
                },");
                    }
                    if fields.is_empty() {
                        put!("
                _marker: PhantomData,");
                    }
                    put!("
            })");
                }
            }
            Rule::Alternation(ref label, ref choices) => {
                put!("
        let node = ParseNode { l: Some(", label, "), range: self.span };
        self.parser.sppf.children[&node].iter().map(move |&i| {
            match _P::from_usize(i) {");
                for (i, unit) in choices.iter().enumerate() {
                    let parse_label = match *unit {
                        Unit::Rule(ref r) => r,
                        Unit::Atom(..) => unimplemented!(),
                    };
                    put!("
                _P::", parse_label, " => ", self.name, " {");
                    for (field_name, &j) in fields {
                        put!("
                ", field_name, ": ");
                        if i == j {
                            put!("Some(Handle {
                    span: self.span,
                    parser: self.parser,
                    _marker: PhantomData,
                }),");
                        } else {
                            put!("None,");
                        }
                    }
                    if fields.is_empty() {
                        put!("
                _marker: PhantomData,");
                    }
                    put!("
            },");
                }
                put!("
                _ => unreachable!(),
            }
        })");
            }
        }
    }
}
