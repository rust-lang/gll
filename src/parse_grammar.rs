// HACK(eddyb) silence warnings from unused exports in the generated code.
#![allow(unused)]

// HACK(eddyb) needed for bootstrapping.
use crate as gll;

include!(concat!(env!("OUT_DIR"), "/parse_grammar.rs"));

use crate::scannerless::Pat as SPat;
use crate::{grammar, runtime};
use std::ops::Bound;
use std::str::FromStr;

impl<Pat: From<SPat>> FromStr for grammar::Grammar<Pat> {
    type Err = runtime::ParseError<runtime::LineColumn, runtime::LineColumnRange>;
    fn from_str(src: &str) -> Result<Self, Self::Err> {
        let mut grammar = grammar::Grammar::new();
        Grammar::parse(src)?.with(|g| {
            for rule_def in g.one().unwrap().rules {
                let rule_def = rule_def.unwrap().one().unwrap();
                grammar.define(rule_def.name.source(), rule_def.rule.one().unwrap().lower());
            }
        });
        Ok(grammar)
    }
}

impl Or<'_, '_, &str> {
    fn lower<Pat: From<SPat>>(self) -> grammar::RuleWithNamedFields<Pat> {
        let mut rules = self.rules.map(|rule| rule.unwrap().one().unwrap().lower());
        let first = rules.next().unwrap();
        rules.fold(first, |a, b| a | b)
    }
}

impl Concat<'_, '_, &str> {
    fn lower<Pat: From<SPat>>(self) -> grammar::RuleWithNamedFields<Pat> {
        self.rules
            .map(|rule| rule.unwrap().one().unwrap().lower())
            .fold(grammar::empty(), |a, b| a + b)
    }
}

impl Rule<'_, '_, &str> {
    fn lower<Pat: From<SPat>>(self) -> grammar::RuleWithNamedFields<Pat> {
        let mut rule = self.rule.one().unwrap().lower();
        if let Some(modifier) = self.modifier {
            rule = modifier.one().unwrap().lower(rule);
        }
        if let Some(field) = self.field {
            rule = rule.field(field.source());
        }
        rule
    }
}

impl Primary<'_, '_, &str> {
    fn lower<Pat: From<SPat>>(self) -> grammar::RuleWithNamedFields<Pat> {
        match self {
            Primary::Eat(pat) => grammar::eat(pat.one().unwrap().lower()),
            Primary::NegativeLookahead { pat } => {
                grammar::negative_lookahead(pat.one().unwrap().lower())
            }
            Primary::Call(name) => grammar::call(name.source()),
            Primary::Group { or } => or.map_or_else(grammar::empty, |or| or.one().unwrap().lower()),
        }
    }
}

impl Modifier<'_, '_, &str> {
    fn lower<Pat: From<SPat>>(
        self,
        rule: grammar::RuleWithNamedFields<Pat>,
    ) -> grammar::RuleWithNamedFields<Pat> {
        match self {
            Modifier::Opt(_) => rule.opt(),
            Modifier::Repeat { repeat, sep } => {
                let sep = sep.map(|sep| sep.one().unwrap().lower());
                match repeat.one().unwrap() {
                    Repeat::Many(_) => rule.repeat_many(sep),
                    Repeat::More(_) => rule.repeat_more(sep),
                }
            }
        }
    }
}

impl Pattern<'_, '_, &str> {
    fn lower(self) -> SPat {
        fn unescape<T>(handle: Handle<'_, '_, &str, T>) -> String {
            let mut out = String::new();
            let s = handle.source();
            let mut chars = s[1..s.len() - 1].chars();
            while let Some(c) = chars.next() {
                let c = match c {
                    '\\' => match chars.next().unwrap() {
                        't' => '\t',
                        'n' => '\n',
                        'r' => '\r',
                        c => c,
                    },
                    _ => c,
                };
                out.push(c);
            }
            out
        }
        let unescape_char = |c| unescape(c).parse::<char>().unwrap();
        match self {
            Pattern::Str(s) => SPat::from(unescape(s)),
            Pattern::CharRange { start, end } => SPat::from((
                start
                    .map(unescape_char)
                    .map_or(Bound::Unbounded, Bound::Included),
                end.map(unescape_char)
                    .map_or(Bound::Unbounded, Bound::Excluded),
            )),
            Pattern::CharRangeInclusive { start, end } => SPat::from((
                start
                    .map(unescape_char)
                    .map_or(Bound::Unbounded, Bound::Included),
                Bound::Included(unescape_char(end)),
            )),
        }
    }
}
