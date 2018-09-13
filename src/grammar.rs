use ordermap::{orderset, OrderMap, OrderSet};
use std::char;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::hash::Hash;
use std::ops::{
    BitAnd, BitOr, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};
use std::rc::Rc;

pub struct Grammar<Pat> {
    pub(crate) rules: OrderMap<String, RuleWithNamedFields<Pat>>,
}

impl<Pat> Grammar<Pat> {
    pub fn new() -> Self {
        Grammar {
            rules: OrderMap::new(),
        }
    }
    pub fn add_rule(&mut self, name: &str, rule: RuleWithNamedFields<Pat>) {
        self.rules.insert(name.to_string(), rule);
    }
}

pub struct RuleWithNamedFields<Pat> {
    pub(crate) rule: Rc<Rule<Pat>>,
    pub(crate) fields: OrderMap<String, OrderSet<Vec<usize>>>,
}

impl<Pat: PartialEq> RuleWithNamedFields<Pat> {
    pub fn empty() -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::Empty),
            fields: OrderMap::new(),
        }
    }
    pub fn match_(pat: Pat) -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::Match(pat)),
            fields: OrderMap::new(),
        }
    }
    pub fn not_match(pat: Pat) -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::NotMatch(pat)),
            fields: OrderMap::new(),
        }
    }
    pub fn call(call: String) -> Self {
        RuleWithNamedFields {
            rule: Rc::new(Rule::Call(call)),
            fields: OrderMap::new(),
        }
    }
    pub fn or(rules: Vec<Self>) -> Self {
        let mut fields = OrderMap::new();
        let rules = rules
            .into_iter()
            .enumerate()
            .map(|(i, rule)| {
                for (name, paths) in rule.fields {
                    fields
                        .entry(name)
                        .or_insert_with(OrderSet::new)
                        .extend(paths.into_iter().map(|mut path| {
                            path.insert(0, i);
                            path
                        }));
                }

                rule.rule
            }).collect();
        RuleWithNamedFields {
            rule: Rc::new(Rule::Or(rules)),
            fields,
        }
    }
    pub fn with_field_name(mut self, name: &str) -> Self {
        match &*self.rule {
            Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => match **rule {
                Rule::Match(_) | Rule::Call(_) => {}
                _ => unimplemented!(),
            },
            _ => {}
        }
        self.fields.insert(name.to_string(), orderset![vec![]]);
        self
    }
    pub fn then(mut self, other: Self) -> Self {
        if *self.rule == Rule::Empty && self.fields.is_empty() {
            return other;
        }
        if *other.rule == Rule::Empty && other.fields.is_empty() {
            return self;
        }
        self.fields = self
            .fields
            .into_iter()
            .map(|(name, paths)| {
                (
                    name,
                    paths
                        .into_iter()
                        .map(|mut path| {
                            path.insert(0, 0);
                            path
                        }).collect(),
                )
            }).collect();
        for (name, paths) in other.fields {
            assert!(!self.fields.contains_key(&name), "duplicate field {}", name);
            self.fields.insert(
                name,
                paths
                    .into_iter()
                    .map(|mut path| {
                        path.insert(0, 1);
                        path
                    }).collect(),
            );
        }
        self.rule = Rc::new(Rule::Concat([self.rule, other.rule]));
        self
    }
    pub fn opt(mut self) -> Self {
        self.fields = self
            .fields
            .into_iter()
            .map(|(name, paths)| {
                (
                    name,
                    paths
                        .into_iter()
                        .map(|mut path| {
                            path.insert(0, 0);
                            path
                        }).collect(),
                )
            }).collect();
        self.rule = Rc::new(Rule::Opt(self.rule));
        self
    }
    pub fn repeat_many(mut self, sep: Option<Self>) -> Self {
        self.fields = self
            .fields
            .into_iter()
            .map(|(name, paths)| {
                (
                    name,
                    paths
                        .into_iter()
                        .map(|mut path| {
                            path.insert(0, 0);
                            path
                        }).collect(),
                )
            }).collect();
        if let Some(sep) = &sep {
            assert!(sep.fields.is_empty());
        }
        self.rule = Rc::new(Rule::RepeatMany(self.rule, sep.map(|sep| sep.rule)));
        self
    }
    pub fn repeat_more(mut self, sep: Option<Self>) -> Self {
        self.fields = self
            .fields
            .into_iter()
            .map(|(name, paths)| {
                (
                    name,
                    paths
                        .into_iter()
                        .map(|mut path| {
                            path.insert(0, 0);
                            path
                        }).collect(),
                )
            }).collect();
        if let Some(sep) = &sep {
            assert!(sep.fields.is_empty());
        }
        self.rule = Rc::new(Rule::RepeatMore(self.rule, sep.map(|sep| sep.rule)));
        self
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rule<Pat> {
    Empty,
    Match(Pat),
    NotMatch(Pat),
    Call(String),

    Concat([Rc<Rule<Pat>>; 2]),
    Or(Vec<Rc<Rule<Pat>>>),

    Opt(Rc<Rule<Pat>>),
    RepeatMany(Rc<Rule<Pat>>, Option<Rc<Rule<Pat>>>),
    RepeatMore(Rc<Rule<Pat>>, Option<Rc<Rule<Pat>>>),
}

impl<Pat: Ord + Hash + MatchesEmpty> Rule<Pat> {
    pub(crate) fn field_pathset_is_refutable(&self, paths: &OrderSet<Vec<usize>>) -> bool {
        if paths.len() > 1 {
            true
        } else {
            self.field_is_refutable(paths.get_index(0).unwrap())
        }
    }
    pub(crate) fn field_is_refutable(&self, path: &[usize]) -> bool {
        match self {
            Rule::Empty
            | Rule::Match(_)
            | Rule::NotMatch(_)
            | Rule::Call(_)
            | Rule::RepeatMany(..)
            | Rule::RepeatMore(..) => false,
            Rule::Concat(rules) => rules[path[0]].field_is_refutable(&path[1..]),
            Rule::Or(..) | Rule::Opt(_) => true,
        }
    }
    fn can_be_empty(
        self: &Rc<Self>,
        cache: &mut HashMap<Rc<Self>, MaybeKnown<bool>>,
        grammar: &Grammar<Pat>,
    ) -> MaybeKnown<bool> {
        match cache.entry(self.clone()) {
            Entry::Occupied(entry) => return *entry.get(),
            Entry::Vacant(entry) => {
                entry.insert(MaybeKnown::Unknown);
            }
        }
        let r = match &**self {
            Rule::Empty | Rule::NotMatch(_) | Rule::Opt(_) | Rule::RepeatMany(..) => {
                MaybeKnown::Known(true)
            }
            Rule::Match(pat) => pat.matches_empty(),
            Rule::Call(rule) => grammar.rules[rule].rule.can_be_empty(cache, grammar),
            Rule::Concat([left, right]) => {
                left.can_be_empty(cache, grammar) & right.can_be_empty(cache, grammar)
            }
            Rule::Or(rules) => rules.iter().fold(MaybeKnown::Known(false), |prev, rule| {
                prev | rule.can_be_empty(cache, grammar)
            }),
            Rule::RepeatMore(elem, _) => elem.can_be_empty(cache, grammar),
        };
        match r {
            MaybeKnown::Known(_) => *cache.get_mut(self).unwrap() = r,
            MaybeKnown::Unknown => {
                cache.remove(self);
            }
        }
        r
    }

    fn check_non_empty_opt(
        self: &Rc<Self>,
        cache: &mut HashMap<Rc<Self>, MaybeKnown<bool>>,
        grammar: &Grammar<Pat>,
    ) {
        match &**self {
            Rule::Empty | Rule::Match(_) | Rule::NotMatch(_) | Rule::Call(_) => {}
            Rule::Concat([left, right]) => {
                left.check_non_empty_opt(cache, grammar);
                right.check_non_empty_opt(cache, grammar);
            }
            Rule::Or(rules) => {
                for rule in rules {
                    rule.check_non_empty_opt(cache, grammar);
                }
            }
            Rule::Opt(rule) => {
                assert_eq!(rule.can_be_empty(cache, grammar), MaybeKnown::Known(false));
                rule.check_non_empty_opt(cache, grammar)
            }
            Rule::RepeatMany(elem, sep) | Rule::RepeatMore(elem, sep) => {
                assert_eq!(elem.can_be_empty(cache, grammar), MaybeKnown::Known(false));
                elem.check_non_empty_opt(cache, grammar);
                if let Some(sep) = sep {
                    sep.check_non_empty_opt(cache, grammar);
                }
            }
        }
    }

    fn check_call_names(self: &Rc<Self>, grammar: &Grammar<Pat>) {
        match &**self {
            Rule::Empty | Rule::Match(_) | Rule::NotMatch(_) => {}
            Rule::Call(rule) => {
                assert!(grammar.rules.contains_key(rule), "no rule named `{}`", rule);
            }
            Rule::Concat([left, right]) => {
                left.check_call_names(grammar);
                right.check_call_names(grammar);
            }
            Rule::Or(rules) => {
                for rule in rules {
                    rule.check_call_names(grammar);
                }
            }
            Rule::Opt(rule) => rule.check_call_names(grammar),
            Rule::RepeatMany(elem, sep) | Rule::RepeatMore(elem, sep) => {
                elem.check_call_names(grammar);
                if let Some(sep) = sep {
                    sep.check_call_names(grammar);
                }
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MaybeKnown<T> {
    Known(T),
    Unknown,
}

impl BitOr for MaybeKnown<bool> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        match (self, rhs) {
            (MaybeKnown::Known(true), _) | (_, MaybeKnown::Known(true)) => MaybeKnown::Known(true),
            (MaybeKnown::Known(false), x) | (x, MaybeKnown::Known(false)) => x,
            (MaybeKnown::Unknown, MaybeKnown::Unknown) => MaybeKnown::Unknown,
        }
    }
}

impl BitAnd for MaybeKnown<bool> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        match (self, rhs) {
            (MaybeKnown::Known(false), _) | (_, MaybeKnown::Known(false)) => {
                MaybeKnown::Known(false)
            }
            (MaybeKnown::Known(true), x) | (x, MaybeKnown::Known(true)) => x,
            (MaybeKnown::Unknown, MaybeKnown::Unknown) => MaybeKnown::Unknown,
        }
    }
}

pub trait MatchesEmpty {
    fn matches_empty(&self) -> MaybeKnown<bool>;
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Pat<S, C> {
    String(S),
    Range(C, C),
}

impl<'a> From<&'a str> for Pat<&'a str, char> {
    fn from(s: &'a str) -> Self {
        Pat::String(s)
    }
}

impl<'a> From<RangeInclusive<char>> for Pat<&'a str, char> {
    fn from(range: RangeInclusive<char>) -> Self {
        Pat::Range(*range.start(), *range.end())
    }
}

impl<'a> From<RangeToInclusive<char>> for Pat<&'a str, char> {
    fn from(range: RangeToInclusive<char>) -> Self {
        Self::from('\0'..=range.end)
    }
}

impl<'a> From<Range<char>> for Pat<&'a str, char> {
    fn from(range: Range<char>) -> Self {
        Self::from(range.start..=char::try_from(range.end as u32 - 1).unwrap())
    }
}

impl<'a> From<RangeFrom<char>> for Pat<&'a str, char> {
    fn from(range: RangeFrom<char>) -> Self {
        Self::from(range.start..=char::MAX)
    }
}

impl<'a> From<RangeTo<char>> for Pat<&'a str, char> {
    fn from(range: RangeTo<char>) -> Self {
        Self::from('\0'..range.end)
    }
}

impl<'a> From<RangeFull> for Pat<&'a str, char> {
    fn from(_: RangeFull) -> Self {
        Self::from('\0'..)
    }
}

impl<S: MatchesEmpty, C: MatchesEmpty> MatchesEmpty for Pat<S, C> {
    fn matches_empty(&self) -> MaybeKnown<bool> {
        match self {
            Pat::String(s) => s.matches_empty(),
            Pat::Range(start, end) => start.matches_empty() | end.matches_empty(),
        }
    }
}

impl<'a> MatchesEmpty for &'a str {
    fn matches_empty(&self) -> MaybeKnown<bool> {
        MaybeKnown::Known(self.is_empty())
    }
}

impl MatchesEmpty for char {
    fn matches_empty(&self) -> MaybeKnown<bool> {
        MaybeKnown::Known(false)
    }
}

pub macro grammar {
    (@rule_tok { $($rule:tt)* }) => {
        grammar!(@rule [$($rule)*] () [])
    },
    (@rule_tok $rule:ident) => {
        RuleWithNamedFields::call(stringify!($rule).to_string())
    },
    (@rule_tok $pat:expr) => {
        RuleWithNamedFields::match_(Pat::from($pat))
    },
    (@rule [] ($current:expr) []) => { $current },
    (@rule [] ($current:expr) [$($rules:expr)+]) => {
        RuleWithNamedFields::or(vec![$($rules,)+ $current])
    },
    (@rule [$($input:tt)*] () [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] (RuleWithNamedFields::empty()) [$($rules)*])
    },
    (@rule [| $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] () [$($rules)* $current])
    },
    (@rule [! $input0:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            RuleWithNamedFields::not_match(Pat::from($input0))
        )) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt ? $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).with_field_name(stringify!($name)).opt()
        )) [$($rules)*])
    },
    (@rule [$input0:tt ? $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).opt()
        )) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt * % $input1:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_many(Some(grammar!(@rule_tok $input1))).with_field_name(stringify!($name))
        )) [$($rules)*])
    },
    (@rule [$input0:tt * % $input1:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_many(Some(grammar!(@rule_tok $input1)))
        )) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt * $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_many(None).with_field_name(stringify!($name))
        )) [$($rules)*])
    },
    (@rule [$input0:tt * $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_many(None)
        )) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt + % $input1:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_more(Some(grammar!(@rule_tok $input1))).with_field_name(stringify!($name))
        )) [$($rules)*])
    },
    (@rule [$input0:tt + % $input1:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_more(Some(grammar!(@rule_tok $input1)))
        )) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt + $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_more(None).with_field_name(stringify!($name))
        )) [$($rules)*])
    },
    (@rule [$input0:tt + $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).repeat_more(None)
        )) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0).with_field_name(stringify!($name))
        )) [$($rules)*])
    },
    (@rule [$input0:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current.then(
            grammar!(@rule_tok $input0)
        )) [$($rules)*])
    },
    ($($rule_name:ident = { $($rule:tt)* };)*) => ({
        let mut grammar = Grammar::new();
        $(grammar.add_rule(stringify!($rule_name), grammar!(@rule_tok { $($rule)* }));)*
        grammar
    })
}

impl<Pat: Ord + Hash + MatchesEmpty> Grammar<Pat> {
    pub(crate) fn check(&self) {
        for rule in self.rules.values() {
            rule.rule.check_call_names(self);
        }

        let mut can_be_empty_cache = HashMap::new();
        for rule in self.rules.values() {
            rule.rule.check_non_empty_opt(&mut can_be_empty_cache, self);
        }
    }
}
