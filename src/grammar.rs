use ordermap::{orderset, OrderMap, OrderSet};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;
use std::iter;
use std::ops::{Add, BitAnd, BitOr};
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
    pub fn define(&mut self, name: &str, rule: RuleWithNamedFields<Pat>) {
        self.rules.insert(name.to_string(), rule);
    }
}

pub struct RuleWithNamedFields<Pat> {
    pub(crate) rule: Rc<Rule<Pat>>,
    pub(crate) fields: OrderMap<String, OrderSet<Vec<usize>>>,
}

pub fn empty<Pat>() -> RuleWithNamedFields<Pat> {
    RuleWithNamedFields {
        rule: Rc::new(Rule::Empty),
        fields: OrderMap::new(),
    }
}
pub fn eat<Pat>(pat: impl Into<Pat>) -> RuleWithNamedFields<Pat> {
    RuleWithNamedFields {
        rule: Rc::new(Rule::Eat(pat.into())),
        fields: OrderMap::new(),
    }
}
pub fn negative_lookahead<Pat>(pat: impl Into<Pat>) -> RuleWithNamedFields<Pat> {
    RuleWithNamedFields {
        rule: Rc::new(Rule::NegativeLookahead(pat.into())),
        fields: OrderMap::new(),
    }
}
pub fn call<Pat>(name: &str) -> RuleWithNamedFields<Pat> {
    RuleWithNamedFields {
        rule: Rc::new(Rule::Call(name.to_string())),
        fields: OrderMap::new(),
    }
}

impl<Pat> RuleWithNamedFields<Pat> {
    pub fn field(mut self, name: &str) -> Self {
        match &*self.rule {
            Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => match **rule {
                Rule::Eat(_) | Rule::Call(_) => {}
                _ => unimplemented!(),
            },
            _ => {}
        }
        self.fields.insert(name.to_string(), orderset![vec![]]);
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

impl<Pat> Add for RuleWithNamedFields<Pat> {
    type Output = Self;

    fn add(mut self, other: Self) -> Self {
        match (&*self.rule, &*other.rule) {
            (Rule::Empty, _) if self.fields.is_empty() => return other,
            (_, Rule::Empty) if other.fields.is_empty() => return self,
            _ => {}
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
}

impl<Pat> BitOr for RuleWithNamedFields<Pat> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self {
        let (old_rules, this, mut fields) = match &*self.rule {
            Rule::Or(rules) => (&rules[..], None, self.fields),
            _ => (&[][..], Some(self), OrderMap::new()),
        };
        let new_rules =
            this.into_iter()
                .chain(iter::once(other))
                .enumerate()
                .map(|(i, rule)| {
                    for (name, paths) in rule.fields {
                        fields.entry(name).or_insert_with(OrderSet::new).extend(
                            paths.into_iter().map(|mut path| {
                                path.insert(0, old_rules.len() + i);
                                path
                            }),
                        );
                    }

                    rule.rule
                });
        let rules = old_rules.iter().cloned().chain(new_rules).collect();

        RuleWithNamedFields {
            rule: Rc::new(Rule::Or(rules)),
            fields,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rule<Pat> {
    Empty,
    Eat(Pat),
    NegativeLookahead(Pat),
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
            | Rule::Eat(_)
            | Rule::NegativeLookahead(_)
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
            Rule::Empty | Rule::NegativeLookahead(_) | Rule::Opt(_) | Rule::RepeatMany(..) => {
                MaybeKnown::Known(true)
            }
            Rule::Eat(pat) => pat.matches_empty(),
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
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) | Rule::Call(_) => {}
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
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) => {}
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

pub macro grammar {
    (@rule_tok { $($rule:tt)* }) => {
        grammar!(@rule [$($rule)*] () [])
    },
    (@rule_tok $rule:ident) => {
        call(stringify!($rule))
    },
    (@rule_tok $pat:expr) => {
        eat($pat)
    },
    (@rule [] ($current:expr) []) => { $current },
    (@rule [] ($current:expr) [$($rules:expr)+]) => {
        $($rules |)+ $current
    },
    (@rule [$($input:tt)*] () [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] (empty()) [$($rules)*])
    },
    (@rule [| $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] () [$($rules)* $current])
    },
    (@rule [! $input0:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            negative_lookahead($input0)
        ) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt ? $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).field(stringify!($name)).opt()
        ) [$($rules)*])
    },
    (@rule [$input0:tt ? $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).opt()
        ) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt * % $input1:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).repeat_many(Some(grammar!(@rule_tok $input1))).field(stringify!($name))
        ) [$($rules)*])
    },
    (@rule [$input0:tt * % $input1:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).repeat_many(Some(grammar!(@rule_tok $input1)))
        ) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt * $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).repeat_many(None).field(stringify!($name))
        ) [$($rules)*])
    },
    (@rule [$input0:tt * $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).repeat_many(None)
        ) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt + % $input1:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).repeat_more(Some(grammar!(@rule_tok $input1))).field(stringify!($name))
        ) [$($rules)*])
    },
    (@rule [$input0:tt + % $input1:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).repeat_more(Some(grammar!(@rule_tok $input1)))
        ) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt + $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).repeat_more(None).field(stringify!($name))
        ) [$($rules)*])
    },
    (@rule [$input0:tt + $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).repeat_more(None)
        ) [$($rules)*])
    },
    (@rule [$name:ident : $input0:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0).field(stringify!($name))
        ) [$($rules)*])
    },
    (@rule [$input0:tt $($input:tt)*] ($current:expr) [$($rules:expr)*]) => {
        grammar!(@rule [$($input)*] ($current +
            grammar!(@rule_tok $input0)
        ) [$($rules)*])
    },
    ($($rule_name:ident = { $($rule:tt)* };)*) => ({
        let mut grammar = Grammar::new();
        $(grammar.define(stringify!($rule_name), grammar!(@rule_tok { $($rule)* }));)*
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
