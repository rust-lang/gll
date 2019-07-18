// HACK(eddyb) silence warnings from unused exports in the generated code.
#![allow(unused)]
#![allow(non_camel_case_types)]

// HACK(eddyb) needed for bootstrapping.
use crate as gll;

include!(concat!(env!("OUT_DIR"), "/parse_grammar.rs"));

use grammer::context::Context;
use grammer::parser::ParseError;
use grammer::proc_macro::{FlatToken, FlatTokenPat, Span, TokenStream};
use grammer::rule;
use grammer::scannerless::Pat as SPat;
use std::hash::Hash;
use std::ops::Bound;
use std::str::FromStr;

pub fn parse_grammar<Pat: Eq + Hash + From<SPat>>(
    cx: &mut Context<Pat>,
    stream: TokenStream,
) -> Result<grammer::Grammar, ParseError<Span, &'static [FlatTokenPat<&'static str>]>> {
    let mut grammar = grammer::Grammar::new();
    Grammar::parse(stream)?.with(|g| {
        for rule_def in g.one().unwrap().rules {
            let rule_def = rule_def.unwrap().one().unwrap();
            let name = match rule_def.name.source() {
                [FlatToken::Ident(ident)] => ident.to_string(),
                _ => unreachable!(),
            };
            grammar.define(cx.intern(name), rule_def.rule.one().unwrap().lower(cx));
        }
    });
    Ok(grammar)
}

impl Or<'_, '_, TokenStream> {
    fn lower<Pat: Eq + Hash + From<SPat>>(
        self,
        cx: &mut Context<Pat>,
    ) -> rule::RuleWithNamedFields {
        let mut rules = self.rules.map(|rule| rule.unwrap().one().unwrap());
        let first = rules.next().unwrap().lower(cx);
        rules.fold(first, |a, b| (a | b.lower(cx)).finish(cx))
    }
}

impl Concat<'_, '_, TokenStream> {
    fn lower<Pat: Eq + Hash + From<SPat>>(
        self,
        cx: &mut Context<Pat>,
    ) -> rule::RuleWithNamedFields {
        self.rules
            .map(|rule| rule.unwrap().one().unwrap())
            .fold(rule::empty().finish(cx), |a, b| {
                (a + b.lower(cx)).finish(cx)
            })
    }
}

impl Rule<'_, '_, TokenStream> {
    fn lower<Pat: Eq + Hash + From<SPat>>(
        self,
        cx: &mut Context<Pat>,
    ) -> rule::RuleWithNamedFields {
        let mut rule = self.rule.one().unwrap().lower(cx);
        if let Some(modifier) = self.modifier {
            rule = modifier.one().unwrap().lower(cx, rule);
        }
        if let Some(field) = self.field {
            let field = match field.source() {
                [FlatToken::Ident(ident)] => ident.to_string(),
                _ => unreachable!(),
            };
            rule = rule.field(&field).finish(cx);
        }
        rule
    }
}

impl Primary<'_, '_, TokenStream> {
    fn lower<Pat: Eq + Hash + From<SPat>>(
        self,
        cx: &mut Context<Pat>,
    ) -> rule::RuleWithNamedFields {
        match self {
            Primary::Eat(pat) => rule::eat(pat.one().unwrap().lower(cx)).finish(cx),
            Primary::Call(name) => {
                let name = match name.source() {
                    [FlatToken::Ident(ident)] => ident.to_string(),
                    _ => unreachable!(),
                };
                rule::call(&name).finish(cx)
            }
            Primary::Group { or } => or
                .map(|or| or.one().unwrap().lower(cx))
                .unwrap_or_else(|| rule::empty().finish(cx)),
        }
    }
}

impl Modifier<'_, '_, TokenStream> {
    fn lower<Pat: Eq + Hash + From<SPat>>(
        self,
        cx: &mut Context<Pat>,
        rule: rule::RuleWithNamedFields,
    ) -> rule::RuleWithNamedFields {
        match self {
            Modifier::Opt(_) => rule.opt().finish(cx),
            Modifier::Repeat { repeat, sep, kind } => {
                let repeat = repeat.one().unwrap();
                if let Some(sep) = sep {
                    let sep = sep.one().unwrap().lower(cx);
                    let kind = kind.unwrap().one().unwrap().lower(cx);
                    match repeat {
                        Repeat::Many(_) => rule.repeat_many_sep(sep, kind).finish(cx),
                        Repeat::More(_) => rule.repeat_more_sep(sep, kind).finish(cx),
                    }
                } else {
                    match repeat {
                        Repeat::Many(_) => rule.repeat_many().finish(cx),
                        Repeat::More(_) => rule.repeat_more().finish(cx),
                    }
                }
            }
        }
    }
}

impl SepKind<'_, '_, TokenStream> {
    fn lower<Pat: Eq + Hash>(&self, cx: &mut Context<Pat>) -> rule::SepKind {
        match self {
            SepKind::Simple(_) => rule::SepKind::Simple,
            SepKind::Trailing(_) => rule::SepKind::Trailing,
        }
    }
}

impl Pattern<'_, '_, TokenStream> {
    fn lower<Pat: Eq + Hash>(self, cx: &mut Context<Pat>) -> SPat {
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
