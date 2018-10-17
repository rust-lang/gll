include!(concat!(env!("OUT_DIR"), "/parse_grammar.rs"));

use scannerless::Pat as SPat;
use std::ops::Bound;
use std::str::FromStr;

impl<Pat: From<SPat>> FromStr for ::grammar::Grammar<Pat> {
    type Err = ::runtime::LineColumn;
    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Grammar::parse_with(src, |_, g| {
            g.map_err(|err| match err {
                ParseError::TooShort(handle) => handle.source_info().end,
                ParseError::NoParse => ::runtime::LineColumn::default(),
            })
            .map(|g| {
                let mut grammar = ::grammar::Grammar::new();
                for rule_def in g.one().unwrap().rules {
                    let rule_def = rule_def.unwrap().one().unwrap();
                    grammar.define(rule_def.name.source(), rule_def.rule.one().unwrap().lower());
                }
                grammar
            })
        })
    }
}

impl<'a, 'i, 's> Or<'a, 'i, &'s str> {
    fn lower<Pat: From<SPat>>(self) -> ::grammar::RuleWithNamedFields<Pat> {
        let mut rules = self.rules.map(|rule| rule.unwrap().one().unwrap().lower());
        let first = rules.next().unwrap();
        rules.fold(first, |a, b| a | b)
    }
}

impl<'a, 'i, 's> Concat<'a, 'i, &'s str> {
    fn lower<Pat: From<SPat>>(self) -> ::grammar::RuleWithNamedFields<Pat> {
        self.rules
            .map(|rule| rule.unwrap().one().unwrap().lower())
            .fold(::grammar::empty(), |a, b| a + b)
    }
}

impl<'a, 'i, 's> Rule<'a, 'i, &'s str> {
    fn lower<Pat: From<SPat>>(self) -> ::grammar::RuleWithNamedFields<Pat> {
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

impl<'a, 'i, 's> Primary<'a, 'i, &'s str> {
    fn lower<Pat: From<SPat>>(self) -> ::grammar::RuleWithNamedFields<Pat> {
        match self {
            Primary::Eat(pat) => ::grammar::eat(pat.one().unwrap().lower()),
            Primary::NegativeLookahead { pat } => {
                ::grammar::negative_lookahead(pat.one().unwrap().lower())
            }
            Primary::Call(name) => ::grammar::call(name.source()),
            Primary::Group { or } => {
                or.map_or_else(::grammar::empty, |or| or.one().unwrap().lower())
            }
        }
    }
}

impl<'a, 'i, 's> Modifier<'a, 'i, &'s str> {
    fn lower<Pat: From<SPat>>(
        self,
        rule: ::grammar::RuleWithNamedFields<Pat>,
    ) -> ::grammar::RuleWithNamedFields<Pat> {
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

impl<'a, 'i, 's> Pattern<'a, 'i, &'s str> {
    fn lower(self) -> SPat {
        fn unescape<T>(handle: Handle<&str, T>) -> String {
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
            Pattern::Str(s) => ::scannerless::Pat::from(unescape(s)),
            Pattern::CharRange { start, end } => ::scannerless::Pat::from((
                start
                    .map(unescape_char)
                    .map_or(Bound::Unbounded, Bound::Included),
                end.map(unescape_char)
                    .map_or(Bound::Unbounded, Bound::Excluded),
            )),
            Pattern::CharRangeInclusive { start, end } => ::scannerless::Pat::from((
                start
                    .map(unescape_char)
                    .map_or(Bound::Unbounded, Bound::Included),
                Bound::Included(unescape_char(end)),
            )),
        }
    }
}
