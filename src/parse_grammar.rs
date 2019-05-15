// HACK(eddyb) silence warnings from unused exports in the generated code.
#![allow(unused)]
#![allow(non_camel_case_types)]

// HACK(eddyb) needed for bootstrapping.
use crate as gll;

include!(concat!(env!("OUT_DIR"), "/parse_grammar.rs"));

use crate::parser::ParseError;
use crate::proc_macro::{FlatToken, Span, TokenStream};
use crate::scannerless::Pat as SPat;
use std::ops::Bound;
use std::str::FromStr;

pub fn parse_grammar<Pat: From<SPat>>(
    stream: TokenStream,
) -> Result<grammer::Grammar<Pat>, ParseError<Span>> {
    let mut grammar = grammer::Grammar::new();
    Grammar::parse(stream)?.with(|g| {
        for rule_def in g.one().unwrap().rules {
            let rule_def = rule_def.unwrap().one().unwrap();
            let name = match rule_def.name.source() {
                [FlatToken::Ident(ident)] => ident.to_string(),
                _ => unreachable!(),
            };
            grammar.define(&name, rule_def.rule.one().unwrap().lower());
        }
    });
    Ok(grammar)
}

impl Or<'_, '_, TokenStream> {
    fn lower<Pat: From<SPat>>(self) -> grammer::RuleWithNamedFields<Pat> {
        let mut rules = self.rules.map(|rule| rule.unwrap().one().unwrap().lower());
        let first = rules.next().unwrap();
        rules.fold(first, |a, b| a | b)
    }
}

impl Concat<'_, '_, TokenStream> {
    fn lower<Pat: From<SPat>>(self) -> grammer::RuleWithNamedFields<Pat> {
        self.rules
            .map(|rule| rule.unwrap().one().unwrap().lower())
            .fold(grammer::empty(), |a, b| a + b)
    }
}

impl Rule<'_, '_, TokenStream> {
    fn lower<Pat: From<SPat>>(self) -> grammer::RuleWithNamedFields<Pat> {
        let mut rule = self.rule.one().unwrap().lower();
        if let Some(modifier) = self.modifier {
            rule = modifier.one().unwrap().lower(rule);
        }
        if let Some(field) = self.field {
            let field = match field.source() {
                [FlatToken::Ident(ident)] => ident.to_string(),
                _ => unreachable!(),
            };
            rule = rule.field(&field);
        }
        rule
    }
}

impl Primary<'_, '_, TokenStream> {
    fn lower<Pat: From<SPat>>(self) -> grammer::RuleWithNamedFields<Pat> {
        match self {
            Primary::Eat(pat) => grammer::eat(pat.one().unwrap().lower()),
            Primary::Call(name) => {
                let name = match name.source() {
                    [FlatToken::Ident(ident)] => ident.to_string(),
                    _ => unreachable!(),
                };
                grammer::call(&name)
            }
            Primary::Group { or } => or.map_or_else(grammer::empty, |or| or.one().unwrap().lower()),
        }
    }
}

impl Modifier<'_, '_, TokenStream> {
    fn lower<Pat: From<SPat>>(
        self,
        rule: grammer::RuleWithNamedFields<Pat>,
    ) -> grammer::RuleWithNamedFields<Pat> {
        match self {
            Modifier::Opt(_) => rule.opt(),
            Modifier::Repeat { repeat, sep, kind } => {
                let sep = sep.map(|sep| {
                    (
                        sep.one().unwrap().lower(),
                        kind.unwrap().one().unwrap().lower(),
                    )
                });
                match repeat.one().unwrap() {
                    Repeat::Many(_) => rule.repeat_many(sep),
                    Repeat::More(_) => rule.repeat_more(sep),
                }
            }
        }
    }
}

impl SepKind<'_, '_, TokenStream> {
    fn lower(&self) -> grammer::SepKind {
        match self {
            SepKind::Simple(_) => grammer::SepKind::Simple,
            SepKind::Trailing(_) => grammer::SepKind::Trailing,
        }
    }
}

impl Pattern<'_, '_, TokenStream> {
    fn lower(self) -> SPat {
        fn unescape<T>(handle: Handle<'_, '_, TokenStream, T>) -> String {
            let mut out = String::new();
            let s = match handle.source() {
                [FlatToken::Literal(lit)] => lit.to_string(),
                _ => unreachable!(),
            };
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
