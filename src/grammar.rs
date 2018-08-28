use ordermap::{orderset, OrderMap, OrderSet};
use std::cell::RefCell;
use std::char;
use std::convert::TryFrom;
use std::fmt;
use std::fmt::Write as FmtWrite;
use std::hash::Hash;
use std::io::Write;
use std::mem;
use std::ops::{Add, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};
use std::process::{Command, Stdio};
use std::rc::Rc;
use ParseNodeShape;

pub struct Grammar<Pat> {
    rules: OrderMap<String, RuleWithNamedFields<Pat>>,
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
    rule: Rc<Rule<Pat>>,
    fields: OrderMap<String, OrderSet<Vec<usize>>>,
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
    fn find_variant_fields(
        &self,
    ) -> Option<Vec<(Rc<Rule<Pat>>, &str, OrderMap<&str, OrderSet<Vec<usize>>>)>> {
        if let Rule::Or(rules) = &*self.rule {
            if self.fields.is_empty() {
                return None;
            }
            let mut variants: Vec<_> = rules
                .iter()
                .map(|rule| (rule.clone(), "", OrderMap::new()))
                .collect();
            for (field, paths) in &self.fields {
                for path in paths {
                    if path.len() == 0 {
                        return None;
                    }
                    if path.len() == 1 {
                        if variants[path[0]].1 != "" {
                            return None;
                        }
                        variants[path[0]].1 = field;
                    } else {
                        variants[path[0]]
                            .2
                            .entry(&field[..])
                            .or_insert_with(OrderSet::new)
                            .insert(path[1..].to_vec());
                    }
                }
            }
            if variants.iter().any(|x| x.1 == "") {
                return None;
            }
            Some(variants)
        } else {
            None
        }
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

impl<Pat: Ord + Hash + ToRustSrc> Rule<Pat> {
    fn field_pathset_type(&self, paths: &OrderSet<Vec<usize>>) -> String {
        let ty = self.field_type(paths.get_index(0).unwrap());
        for path in paths.iter().skip(1) {
            if self.field_type(path) != ty {
                return "()".to_string();
            }
        }
        ty
    }
    fn field_type(&self, path: &[usize]) -> String {
        match self {
            Rule::Empty | Rule::Match(_) | Rule::NotMatch(_) => {
                assert_eq!(path, []);
                "()".to_string()
            }
            Rule::Call(r) => format!("{}<'a, 'i, 's>", r),
            Rule::Concat(rules) => rules[path[0]].field_type(&path[1..]),
            Rule::Or(rules) => rules[path[0]].field_type(&path[1..]),
            Rule::Opt(rule) => [rule][path[0]].field_type(&path[1..]),
            Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => {
                assert_eq!(path, []);
                format!("[{}]", rule.field_type(&[]))
            }
        }
    }
    fn field_pathset_is_refutable(&self, paths: &OrderSet<Vec<usize>>) -> bool {
        if paths.len() > 1 {
            true
        } else {
            self.field_is_refutable(paths.get_index(0).unwrap())
        }
    }
    fn field_is_refutable(&self, path: &[usize]) -> bool {
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
    fn parse_node_kind(
        self: &Rc<Self>,
        parse_nodes: &RefCell<
            OrderMap<Rc<Self>, (ParseNodeKind, Option<ParseNodeShape<ParseNodeKind>>)>,
        >,
    ) -> ParseNodeKind {
        if let Some((kind, _)) = parse_nodes.borrow().get(self) {
            return kind.clone();
        }
        let kind = match &**self {
            Rule::Empty => ParseNodeKind("()".to_string()),
            Rule::Match(pat) => ParseNodeKind(pat.to_rust_src()),
            Rule::NotMatch(pat) => ParseNodeKind(format!("!{}", pat.to_rust_src())),
            Rule::Call(r) => return ParseNodeKind(r.clone()),
            Rule::Concat([left, right]) => ParseNodeKind(format!(
                "({} {})",
                left.parse_node_kind(parse_nodes).0,
                right.parse_node_kind(parse_nodes).0
            )),
            Rule::Or(rules) => {
                assert!(rules.len() > 1);
                let mut s = String::from("(");
                for (i, rule) in rules.iter().enumerate() {
                    if i > 0 {
                        s.push_str(" | ");
                    }
                    s.push_str(&rule.parse_node_kind(parse_nodes).0);
                }
                s.push(')');
                ParseNodeKind(s)
            }
            Rule::Opt(rule) => ParseNodeKind(format!("({}?)", rule.parse_node_kind(parse_nodes).0)),
            Rule::RepeatMany(rule, None) => {
                ParseNodeKind(format!("({}*)", rule.parse_node_kind(parse_nodes).0))
            }
            Rule::RepeatMany(elem, Some(sep)) => ParseNodeKind(format!(
                "({}* % {})",
                elem.parse_node_kind(parse_nodes).0,
                sep.parse_node_kind(parse_nodes).0
            )),
            Rule::RepeatMore(rule, None) => {
                ParseNodeKind(format!("({}+)", rule.parse_node_kind(parse_nodes).0))
            }
            Rule::RepeatMore(elem, Some(sep)) => ParseNodeKind(format!(
                "({}+ % {})",
                elem.parse_node_kind(parse_nodes).0,
                sep.parse_node_kind(parse_nodes).0
            )),
        };
        assert!(
            parse_nodes
                .borrow_mut()
                .insert(self.clone(), (kind.clone(), None))
                .is_none()
        );
        kind
    }

    fn fill_parse_node_shape(
        self: &Rc<Self>,
        parse_nodes: &RefCell<
            OrderMap<Rc<Self>, (ParseNodeKind, Option<ParseNodeShape<ParseNodeKind>>)>,
        >,
    ) {
        if parse_nodes.borrow()[self].1.is_some() {
            return;
        }
        let shape = match &**self {
            Rule::Empty | Rule::Match(_) | Rule::NotMatch(_) => ParseNodeShape::Opaque,
            Rule::Call(_) => unreachable!(),
            Rule::Concat([left, right]) => ParseNodeShape::Binary(
                left.parse_node_kind(parse_nodes),
                right.parse_node_kind(parse_nodes),
            ),
            Rule::Or(_) => ParseNodeShape::Choice,
            Rule::Opt(rule) => ParseNodeShape::Opt {
                none: Rc::new(Rule::Empty).parse_node_kind(parse_nodes),
                some: rule.parse_node_kind(parse_nodes),
            },
            Rule::RepeatMany(elem, sep) => ParseNodeShape::Opt {
                none: Rc::new(Rule::Empty).parse_node_kind(parse_nodes),
                some: Rc::new(Rule::RepeatMore(elem.clone(), sep.clone()))
                    .parse_node_kind(parse_nodes),
            },
            Rule::RepeatMore(rule, None) => ParseNodeShape::Binary(
                rule.parse_node_kind(parse_nodes),
                Rc::new(Rule::RepeatMany(rule.clone(), None)).parse_node_kind(parse_nodes),
            ),
            Rule::RepeatMore(elem, Some(sep)) => ParseNodeShape::Binary(
                elem.parse_node_kind(parse_nodes),
                Rc::new(Rule::Opt(Rc::new(Rule::Concat([
                    sep.clone(),
                    self.clone(),
                ])))).parse_node_kind(parse_nodes),
            ),
        };
        parse_nodes.borrow_mut().get_mut(self).unwrap().1 = Some(shape);
    }
}

pub trait ToRustSrc {
    fn to_rust_src(&self) -> String;
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

impl<S: fmt::Debug, C: fmt::Debug> ToRustSrc for Pat<S, C> {
    fn to_rust_src(&self) -> String {
        match self {
            Pat::String(s) => format!("{:?}", s),
            Pat::Range(start, end) => format!("{:?}", start..=end),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ParseNodeKind(String);

impl fmt::Display for ParseNodeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "P!({})", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct CodeLabel(String);

impl fmt::Display for CodeLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "_C::{}", self.0)
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

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<Pat: Ord + Hash + ToRustSrc> Grammar<Pat> {
    pub fn generate(&mut self) -> String {
        let mut out = String::new();
        macro put($($x:expr),*) {{ $(write!(out, "{}", $x).unwrap();)* }}

        let parse_nodes = RefCell::new(OrderMap::new());
        let mut named_parse_nodes = vec![];
        let mut code_labels = vec![];

        put!("extern crate gll;

use self::gll::{Call, Continuation, ParseNodeKind, CodeLabel, ParseNodeShape, ParseNode, Range};
use std::any;
use std::fmt;
use std::marker::PhantomData;

pub type Parser<'a, 'i> = gll::Parser<'i, _P, _C, &'a gll::Str>;

pub type Any = dyn any::Any;

#[derive(Debug)]
pub struct Ambiguity<T>(T);

pub struct Handle<'a, 'i: 'a, 's: 'a, T: ?Sized> {
    pub node: ParseNode<'i, _P>,
    pub parser: &'a Parser<'s, 'i>,
    _marker: PhantomData<T>,
}

impl<'a, 'i, 's, T: ?Sized> Copy for Handle<'a, 'i, 's, T> {}

impl<'a, 'i, 's, T: ?Sized> Clone for Handle<'a, 'i, 's, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, 'i, 's, T> From<Ambiguity<Handle<'a, 'i, 's, T>>> for Ambiguity<Handle<'a, 'i, 's, Any>> {
    fn from(x: Ambiguity<Handle<'a, 'i, 's, T>>) -> Self {
        Ambiguity(Handle {
            node: x.0.node,
            parser: x.0.parser,
            _marker: PhantomData,
        })
    }
}

impl<'a, 'i, 's, T> From<Ambiguity<Handle<'a, 'i, 's, [T]>>> for Ambiguity<Handle<'a, 'i, 's, Any>> {
    fn from(x: Ambiguity<Handle<'a, 'i, 's, [T]>>) -> Self {
        Ambiguity(Handle {
            node: x.0.node,
            parser: x.0.parser,
            _marker: PhantomData,
        })
    }
}

impl<'a, 'i, 's> fmt::Debug for Handle<'a, 'i, 's, ()> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            \"{}..{}\",
            self.node.range.start(),
            self.node.range.end()
        )
    }
}

impl<'a, 'i, 's> fmt::Debug for Handle<'a, 'i, 's, Any> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        handle_any_match_type!(self, |handle| write!(f, \"{:?}\", handle))
    }
}

impl<'a, 'i, 's, T> fmt::Debug for Handle<'a, 'i, 's, [T]>
    where Handle<'a, 'i, 's, T>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            \"{}..{} => \",
            self.node.range.start(),
            self.node.range.end()
        )?;
        for (i, x) in self.list_head_many().enumerate() {
            if i > 0 {
                write!(f, \" | \")?;
            }
            match x {
                ListHead::Cons(elem, rest) => {
                    enum Elem<T, L> {
                        One(T),
                        Spread(L),
                    }
                    impl<T: fmt::Debug, L: fmt::Debug> fmt::Debug for Elem<T, L> {
                        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                            match self {
                                Elem::One(x) => write!(f, \"{:?}\", x),
                                Elem::Spread(xs) => write!(f, \"..({:?})\", xs),
                            }
                        }
                    }
                    f.debug_list().entries(::std::iter::once(Elem::One(elem)).chain(rest.map(|r| {
                        match r {
                            Ok(x) => Elem::One(x),
                            Err(Ambiguity(xs)) => Elem::Spread(xs),
                        }
                    }))).finish()?;
                }
                ListHead::Nil => {
                    f.debug_list().entries(None::<()>).finish()?;
                }
            }
        }
        Ok(())
    }
}

impl<'a, 'i, 's, T> Iterator for Handle<'a, 'i, 's, [T]> {
    type Item = Result<Handle<'a, 'i, 's, T>, Ambiguity<Self>>;
    fn next(&mut self) -> Option<Self::Item> {
        let mut iter = self.list_head_many();
        let first = iter.next().unwrap();
        if let Some(second) = iter.next() {
            let original = *self;
            match (first, second) {
                (ListHead::Cons(_, rest), _) |
                (_, ListHead::Cons(_, rest)) => {
                    match rest.node.kind.shape() {
                        ParseNodeShape::Opt { .. } => {
                            self.node.kind = rest.node.kind;
                            self.node.range = Range(self.node.range.split_at(0).0);
                        }
                        _ => unreachable!(),
                    }
                }
                _ => unreachable!(),
            }
            match self.list_head_one() {
                Ok(ListHead::Nil) => {}
                _ => unreachable!(),
            }
            Some(Err(Ambiguity(original)))
        } else {
            match first {
                ListHead::Cons(elem, rest) => {
                    *self = rest;
                    Some(Ok(elem))
                }
                ListHead::Nil => None,
            }
        }
    }
}

pub enum ListHead<'a, 'i: 'a, 's: 'a, T> {
    Cons(Handle<'a, 'i, 's, T>, Handle<'a, 'i, 's, [T]>),
    Nil,
}

impl<'a, 'i, 's, T> Handle<'a, 'i, 's, [T]> {
    fn list_head_one(self) -> Result<ListHead<'a, 'i, 's, T>, Ambiguity<Self>> {
        let mut iter = self.list_head_many();
        let first = iter.next().unwrap();
        if iter.next().is_none() {
            Ok(first)
        } else {
            Err(Ambiguity(self))
        }
    }
    fn list_head_many(self) -> impl Iterator<Item = ListHead<'a, 'i, 's, T>> {
        let mut maybe_cons = None;
        let mut maybe_nil = None;
        if let ParseNodeShape::Opt { none, .. } = self.node.kind.shape() {
            for opt_child in self.parser.sppf.unary_children(self.node) {
                if opt_child.kind == none {
                    maybe_nil = Some(ListHead::Nil);
                } else {
                    maybe_cons = Some(opt_child);
                }
            }
        } else {
            maybe_cons = Some(self.node);
        }
        maybe_cons.into_iter().flat_map(move |node| {
            self.parser.sppf.binary_children(node).flat_map(move |(elem, rest)| {
                if let ParseNodeShape::Binary(..) = rest.kind.shape() {
                    Some(self.parser.sppf.binary_children(rest)).into_iter().flatten().chain(None)
                } else {
                    None.into_iter().flatten().chain(Some((elem, rest)))
                }
            }).map(move |(elem, rest)| {
                ListHead::Cons(Handle {
                    node: elem,
                    parser: self.parser,
                    _marker: PhantomData,
                }, Handle { node: rest, ..self })
            })
        }).chain(maybe_nil)
    }
}");
        for (name, rule) in &self.rules {
            let variants = rule.find_variant_fields();
            if let Some(variants) = &variants {
                put!("

pub enum ", name, "<'a, 'i: 'a, 's: 'a> {");
                for (rule, variant, fields) in variants {
                    if fields.is_empty() {
                        put!("
    ", variant, "(Handle<'a, 'i, 's, ", rule.field_type(&[]), ">),");
                    } else {
                        put!("
    ", variant, " {");
                        for (field_name, paths) in fields {
                            let refutable = rule.field_pathset_is_refutable(paths);
                            put!("
        ", field_name, ": ");
                            if refutable {
                                put!("Option<");
                            }
                            put!("Handle<'a, 'i, 's, ", rule.field_pathset_type(paths), ">");
                            if refutable {
                                put!(">");
                            }
                            put!(",");
                        }
                        put!("
    },");
                    }
                }
                put!("
}");
            } else {
                put!("

pub struct ", name, "<'a, 'i: 'a, 's: 'a> {");
                for (field_name, paths) in &rule.fields {
                    let refutable = rule.rule.field_pathset_is_refutable(paths);
                    put!("
    pub ", field_name, ": ");
                    if refutable {
                        put!("Option<");
                    }
                    put!("Handle<'a, 'i, 's, ", rule.rule.field_pathset_type(paths), ">");
                    if refutable {
                        put!(">");
                    }
                    put!(",");
                }
                if rule.fields.is_empty() {
                    put!("
    _marker: PhantomData<(&'a (), &'i (), &'s ())>,");
                }
                put!("
}");
            }
            put!("

impl<'a, 'i, 's> ", name, "<'a, 'i, 's> {
    pub fn parse(p: &'a mut Parser<'s, 'i>, range: Range<'i>) -> Result<Handle<'a, 'i, 's, Self>, ()> {
        let call = Call {
            callee: ", CodeLabel(name.clone()), ",
            range,
        };
        if !p.gss.calls.contains_key(&call) {
            p.gss.threads.spawn(
                Continuation {
                    code: call.callee,
                    frame: call,
                    state: 0,
                },
                call.range,
            );
            parse(p);
        }
        if let Some(range) = p.gss.longest_result(call) {
            return Ok(Handle {
                node: ParseNode { kind: ", ParseNodeKind(name.clone()), ", range },
                parser: p,
                _marker: PhantomData,
            });
        }
        Err(())
    }
}

impl<'a, 'i, 's> fmt::Debug for ", name, "<'a, 'i, 's> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {");
            if let Some(variants) = &variants {
                put!("
        match self {
        ");
                for (rule, variant, fields) in variants {
                    if fields.is_empty() {
                        put!("
            ", name, "::", variant, "(x) => f.debug_tuple(\"", name, "::", variant, "\").field(x).finish(),");
                    } else {
                        put!("
            ", name, "::", variant, " { ");
                        for field_name in fields.keys() {
                            put!(field_name, ": f_", field_name, ", ");
                        }
                        put!(" } => {
                let mut d = f.debug_struct(\"", name, "::", variant, "\");");
                        for (field_name, paths) in fields {
                            if rule.field_pathset_is_refutable(paths) {
                                put!("
                if let Some(field) = f_", field_name, " {
                    d.field(\"", field_name,"\", field);
                }");
                            } else {
                            put!("
                d.field(\"", field_name,"\", f_", field_name, ");");
                            }
                        }
                put!("
                d.finish()
            }");
                    }
                }
                put!("
            }");
            } else {
                put!("
        let mut d = f.debug_struct(\"", name, "\");");
                for (field_name, paths) in &rule.fields {
                    if rule.rule.field_pathset_is_refutable(paths) {
                        put!("
        if let Some(ref field) = self.", field_name, " {
            d.field(\"", field_name,"\", field);
        }");
                    } else {
                    put!("
        d.field(\"", field_name,"\", &self.", field_name, ");");
                    }
                }
                put!("
        d.finish()");
            }
            put!("
    }
}");
            if rule.fields.is_empty() {
                put!("

impl<'a, 'i, 's> fmt::Debug for Handle<'a, 'i, 's, ", name, "<'a, 'i, 's>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, \"{}..{}\", self.node.range.start(), self.node.range.end())
    }
}");
                continue;
            }
            put!("

impl<'a, 'i, 's> fmt::Debug for Handle<'a, 'i, 's, ", name, "<'a, 'i, 's>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            \"{}..{} => \",
            self.node.range.start(),
            self.node.range.end()
        )?;
        for (i, x) in self.many().enumerate() {
            if i > 0 {
                write!(f, \" | \")?;
            }
            fmt::Debug::fmt(&x, f)?;
        }
        Ok(())
    }
}

impl<'a, 'i, 's> Handle<'a, 'i, 's, ", name, "<'a, 'i, 's>> {
    pub fn one(self) -> Result<", name, "<'a, 'i, 's>, Ambiguity<Self>> {
        let mut iter = self.many();
        let first = iter.next().unwrap();
        if iter.next().is_none() {
            Ok(first)
        } else {
            Err(Ambiguity(self))
        }
    }
    pub fn many(self) -> impl Iterator<Item = ", name, "<'a, 'i, 's>> {
        self.parser.sppf.unary_children(self.node).flat_map(move |node| {");
            if let Some(variants) = variants {
                put!("
            self.parser.sppf.unary_children(node).flat_map(move |node| {
                enum Iter<");
                for i in 0..variants.len() {
                    put!("_", i, ",");
                }
                put!("> {");
                for i in 0..variants.len() {
                    put!("
                _", i, "(_", i, "),");
                }
                put!("
            }
            impl<_0: Iterator,");
                for i in 1..variants.len() {
                    put!("_", i, ": Iterator<Item = _0::Item>,");
                }
                put!("> Iterator for Iter<");
                for i in 0..variants.len() {
                    put!("_", i, ",");
                }
                put!("> {
                type Item = _0::Item;
                fn next(&mut self) -> Option<Self::Item> {
                    match self {");
                for i in 0..variants.len() {
                    put!("
                        Iter::_", i, "(it) => it.next(),");
                }
                    put!("
                    }
                }
            }
                match node.kind {");
                for (i, (rule, variant, fields)) in variants.iter().enumerate() {
                    put!("
                    ", rule.parse_node_kind(&parse_nodes), " => Iter::_", i, "(");
                    if fields.is_empty() {
                        put!("::std::iter::once(", name, "::", variant, "(Handle {
                        node,
                        parser: self.parser,
                        _marker: PhantomData,
                    }))");
                    } else {
                        put!(rule.generate_traverse("node", false, &parse_nodes).replace("\n", "\n        "),
                            ".map(move |_r| ", name, "::", variant, " {");
                        for (field_name, paths) in fields {
                            if rule.field_pathset_is_refutable(paths) {
                                put!("
                                ", field_name, ": None.or(_r");
                                for path in paths {
                                    for p in path {
                                        put!(" .", p);
                                    }
                                }
                                put!(").map(|node| Handle {
                                    node,
                                    parser: self.parser,
                                    _marker: PhantomData,
                                }),");
                            } else {
                                put!("
                                ", field_name, ": Handle {
                                    node: _r");
                                assert_eq!(paths.len(), 1);
                                for p in paths.get_index(0).unwrap() {
                                    put!(" .", p);
                                }
                                put!(",
                                    parser: self.parser,
                                    _marker: PhantomData,
                                },");
                            }
                        }
                        put!("
                    })");
                    }
                    put!("),");
                }
                put!("
                    _ => unreachable!(),
                }
            })");
            } else {
                put!("
            ", rule.rule.generate_traverse("node", false, &parse_nodes), "
        }).map(move |_r| ", name, " {");
                for (field_name, paths) in &rule.fields {
                    if rule.rule.field_pathset_is_refutable(paths) {
                        put!("
            ", field_name, ": None.or(_r");
                        for path in paths {
                            for p in path {
                                put!(" .", p);
                            }
                        }
                        put!(").map(|node| Handle {
                node,
                parser: self.parser,
                _marker: PhantomData,
            }),");
                    } else {
                        put!("
            ", field_name, ": Handle {
                node: _r");
                        assert_eq!(paths.len(), 1);
                        for p in paths.get_index(0).unwrap() {
                            put!(" .", p);
                        }
                    put!(",
                parser: self.parser,
                _marker: PhantomData,
            },");
                    }
                }
                if rule.fields.is_empty() {
                    put!("
            _marker: PhantomData,");
                }
            }
                put!("
        })
    }
}");
        }
        put!("
fn parse(p: &mut Parser) {
    while let Some(Call { callee: mut c, range: _range }) = p.gss.threads.steal() {
        match c.code {");
        for (name, rule) in &self.rules {
            let parse_nodes = if rule.fields.is_empty() {
                None
            } else {
                Some(&parse_nodes)
            };
            code_labels.push(CodeLabel(name.clone()));
            let parse_node_kind = ParseNodeKind(name.clone());
            let shape = if let Some(parse_nodes) = parse_nodes {
                ParseNodeShape::Alias(rule.rule.parse_node_kind(parse_nodes))
            } else {
                ParseNodeShape::Opaque
            };
            named_parse_nodes.push((parse_node_kind.clone(), shape));

            put!((
                reify_as(CodeLabel(name.clone())) +
                rule.rule.clone().generate_parse(parse_nodes) +
                ret()
            )(Continuation {
                code_labels: &mut code_labels,
                code_label_prefix: name,
                code_label_counter: &mut 0,
                code_label_arms: &mut String::new(),
                code: Code::Inline(String::new()),
                nested_frames: vec![],
            }).code_label_arms);
        }
        put!("
        }
    }
}
");
        let mut i = 0;
        while i < parse_nodes.borrow().len() {
            let rule = parse_nodes.borrow().get_index(i).unwrap().0.clone();
            rule.fill_parse_node_shape(&parse_nodes);
            i += 1;
        }
        let mut all_parse_nodes: Vec<_> = named_parse_nodes.into_iter().map(|(k, s)| (k.clone(), s, Some(k.0)))
            .chain(parse_nodes.into_inner().into_iter().map(|(r, (k, s))| {
                (k, s.unwrap(), match &*r {
                    Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => match &**rule {
                        Rule::Match(_) => Some("()".to_string()),
                        Rule::Call(r) => Some(r.clone()),
                        _ => None,
                    },
                    _ => None,
                })
            }))
            .collect();
        all_parse_nodes.sort();
        put!("
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum _P {");
        for i in 0..all_parse_nodes.len() {
            put!(
                "
    _", i, ",");
        }
        put!("
}

macro handle_any_match_type($handle:expr, $case:expr) {
    match $handle.node.kind {");
        for (kind, _, ty) in &all_parse_nodes {
            if let Some(ty) = ty {
                put!("
        ", kind, " => $case(Handle::<", ty, "> {
            node: $handle.node,
            parser: $handle.parser,
            _marker: PhantomData,
        }),");
            }
        }
        put!("
        _ => $case(Handle::<()> {
            node: $handle.node,
            parser: $handle.parser,
            _marker: PhantomData,
        }),
    }
}

macro P {");
        for (i, (kind, _, _)) in all_parse_nodes.iter().enumerate() {
            if i != 0 {
                put!(",");
            }
            put!("
    (", kind.0, ") => (_P::_", i, ")");
        }
        put!("
}

impl fmt::Display for _P {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match *self {");
        for (kind, _, _) in &all_parse_nodes {
            put!("
            ", kind, " => \"", kind.0.escape_default(), "\",");
        }
        put!("
        };
        write!(f, \"{}\", s)
    }
}

impl ParseNodeKind for _P {
    fn shape(self) -> ParseNodeShape<Self> {
        match self {");
        for (kind, shape, _) in &all_parse_nodes {
            put!("
                ", kind, " => ParseNodeShape::", shape, ",");
        }
        put!("
        }
    }
    fn from_usize(i: usize) -> Self {
        match i {");

        for i in 0..all_parse_nodes.len() {
            put!("
            ", i, " => _P::_", i, ",");
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
    ", s.0, ",");
        }
        put!("
}

impl CodeLabel for _C {}
");
        let rustfmt = Command::new("rustfmt")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn();

        if let Ok(mut rustfmt) = rustfmt {
            let stdin_result = {
                let stdin = rustfmt.stdin.as_mut().unwrap();
                stdin.write_all(out.as_bytes())
            };

            if let Ok(output) = rustfmt.wait_with_output() {
                if output.status.success() {
                    stdin_result.unwrap();
                    out = String::from_utf8_lossy(&output.stdout).to_string();
                }
            }
        }
        out
    }
}

#[must_use]
struct Continuation<'a> {
    code_labels: &'a mut Vec<CodeLabel>,
    code_label_prefix: &'a str,
    code_label_counter: &'a mut usize,
    code_label_arms: &'a mut String,
    code: Code,
    nested_frames: Vec<Option<CodeLabel>>,
}

#[derive(Clone)]
enum Code {
    Inline(String),
    Label(CodeLabel),
}

impl<'a> Continuation<'a> {
    fn next_code_label(&mut self) -> CodeLabel {
        *self.code_label_counter += 1;
        let label = CodeLabel(format!(
            "{}__{}",
            self.code_label_prefix, self.code_label_counter
        ));
        self.code_labels.push(label.clone());
        label
    }

    fn clone(&mut self) -> Continuation {
        Continuation {
            code_labels: self.code_labels,
            code_label_prefix: self.code_label_prefix,
            code_label_counter: self.code_label_counter,
            code_label_arms: self.code_label_arms,
            code: self.code.clone(),
            nested_frames: self.nested_frames.clone(),
        }
    }

    fn to_inline(&mut self) -> &mut String {
        match self.code {
            Code::Inline(ref mut code) => code,
            Code::Label(ref label) => {
                self.code = Code::Inline(format!(
                    "
                c.code = {};
                p.gss.threads.spawn(c, _range);",
                    label
                ));
                self.to_inline()
            }
        }
    }

    fn to_label(&mut self) -> &mut CodeLabel {
        match self.code {
            Code::Label(ref mut label) => label,
            Code::Inline(_) => {
                let label = self.next_code_label();
                self.reify_as(label);
                self.to_label()
            }
        }
    }

    #[cfg_attr(rustfmt, rustfmt_skip)]
    fn reify_as(&mut self, label: CodeLabel) {
        let code = format!("
            {} => {{{}
            }}", label, self.to_inline());
        self.code_label_arms.push_str(&code);
        self.code = Code::Label(label);
    }
}

struct Compose<F, G>(F, G);

impl<A, F: FnOnce<A>, G: FnOnce<(F::Output,)>> FnOnce<A> for Compose<F, G> {
    type Output = G::Output;
    extern "rust-call" fn call_once(self, args: A) -> Self::Output {
        self.1(self.0.call_once(args))
    }
}

#[must_use]
struct Thunk<F>(F);

impl<F> Thunk<F> {
    fn new(f: F) -> Self
    where
        F: FnOnce(Continuation) -> Continuation,
    {
        Thunk(f)
    }
}

impl<F, G> Add<Thunk<G>> for Thunk<F> {
    type Output = Thunk<Compose<G, F>>;
    fn add(self, other: Thunk<G>) -> Self::Output {
        Thunk(Compose(other.0, self.0))
    }
}

impl<A, F: FnOnce<A>> FnOnce<A> for Thunk<F> {
    type Output = F::Output;
    extern "rust-call" fn call_once(self, args: A) -> Self::Output {
        self.0.call_once(args)
    }
}

macro thunk($($x:expr),*) {{
    let mut prefix = String::new();
    $(write!(prefix, "{}", $x).unwrap();)*
    Thunk::new(move |mut cont| {
        cont.to_inline().insert_str(0, &prefix);
        cont
    })
}}

fn pop_state<F: FnOnce(Continuation) -> Continuation>(
    f: impl FnOnce(&str) -> Thunk<F>,
) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    f("c.state") + Thunk::new(|mut cont| {
        if let Some(&None) = cont.nested_frames.last() {
            *cont.nested_frames.last_mut().unwrap() = Some(cont.to_label().clone());
            cont.code = Code::Inline(String::new());
            cont = ret()(cont);
        }
        cont.nested_frames.push(None);
        cont
    })
}

fn push_state(state: &str) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    thunk!(
        "
                c.state = ",
        state,
        ";"
    ) + Thunk::new(move |mut cont| {
        if let Some(ret_label) = cont.nested_frames.pop().unwrap() {
            cont = call(mem::replace(cont.to_label(), ret_label))(cont);
        }
        cont
    })
}

fn check<'a>(condition: &'a str) -> Thunk<impl FnOnce(Continuation) -> Continuation + 'a> {
    Thunk::new(move |mut cont| {
        let code = cont.to_inline();
        *code = format!(
            "
                if {} {{{}
                }}",
            condition,
            code.replace("\n", "\n    ")
        );
        cont
    })
}

fn call(callee: CodeLabel) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    Thunk::new(move |mut cont| {
        cont.code = Code::Inline(format!(
            "
                c.code = {};
                p.gss.call(Call {{ callee: {}, range: _range }}, c);",
            cont.to_label(),
            callee
        ));
        cont
    })
}

fn ret() -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    thunk!(
        "
                p.gss.ret(c.frame, _range);"
    ) + Thunk::new(|mut cont| {
        assert_eq!(cont.to_inline(), "");
        cont
    })
}

fn sppf_add(
    parse_node_kind: &ParseNodeKind,
    child: &str,
) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    thunk!(
        "
                p.sppf.add(",
        parse_node_kind,
        ", c.frame.range.subtract_suffix(_range), ",
        child,
        ");"
    )
}

trait ForEachThunk {
    fn for_each_thunk(self, cont: &mut Continuation, f: impl FnMut(Continuation));
}

impl<F> ForEachThunk for Thunk<F>
where
    F: FnOnce(Continuation) -> Continuation,
{
    fn for_each_thunk(self, cont: &mut Continuation, mut f: impl FnMut(Continuation)) {
        f(self(cont.clone()));
    }
}

impl<T, U> ForEachThunk for (T, U)
where
    T: ForEachThunk,
    U: ForEachThunk,
{
    fn for_each_thunk(self, cont: &mut Continuation, mut f: impl FnMut(Continuation)) {
        self.0.for_each_thunk(cont, &mut f);
        self.1.for_each_thunk(cont, &mut f);
    }
}

struct ThunkIter<I>(I);

impl<I, T> ForEachThunk for ThunkIter<I>
where
    I: Iterator<Item = T>,
    T: ForEachThunk,
{
    fn for_each_thunk(self, cont: &mut Continuation, mut f: impl FnMut(Continuation)) {
        self.0.for_each(|x| {
            x.for_each_thunk(cont, &mut f);
        });
    }
}

fn parallel(thunks: impl ForEachThunk) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    Thunk::new(|mut cont| {
        cont.to_label();
        let mut code = String::new();
        let mut child_nested_frames = None;
        let nested_frames = cont.nested_frames.clone();
        thunks.for_each_thunk(&mut cont, |mut child_cont| {
            if let Some(prev) = child_nested_frames {
                assert_eq!(child_cont.nested_frames.len(), prev);
            } else {
                child_nested_frames = Some(child_cont.nested_frames.len());
            }
            if let Some(Some(ret_label)) = child_cont.nested_frames.last().cloned() {
                if let None = nested_frames[child_cont.nested_frames.len() - 1] {
                    child_cont = call(mem::replace(child_cont.to_label(), ret_label))(child_cont);
                    *child_cont.nested_frames.last_mut().unwrap() = None;
                }
            }
            assert_eq!(
                child_cont.nested_frames[..],
                nested_frames[..child_cont.nested_frames.len()]
            );
            code.push_str(child_cont.to_inline());
        });
        cont.code = Code::Inline(code);
        if let Some(child_nested_frames) = child_nested_frames {
            while cont.nested_frames.len() > child_nested_frames {
                assert_eq!(cont.nested_frames.pop(), Some(None));
            }
        }
        cont
    })
}

fn opt(
    thunk: Thunk<impl FnOnce(Continuation) -> Continuation>,
) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    parallel((thunk, thunk!("")))
}

fn fix<F: FnOnce(Continuation) -> Continuation>(
    f: impl FnOnce(CodeLabel) -> Thunk<F>,
) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    Thunk::new(|mut cont| {
        let nested_frames = mem::replace(&mut cont.nested_frames, vec![]);
        let ret_label = cont.to_label().clone();
        cont.code = Code::Inline(String::new());
        let label = cont.next_code_label();
        cont = (reify_as(label.clone()) + f(label) + ret())(cont);
        cont = call(mem::replace(cont.to_label(), ret_label))(cont);
        cont.nested_frames = nested_frames;
        cont
    })
}

fn reify_as(label: CodeLabel) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    Thunk::new(|mut cont| {
        cont.reify_as(label);
        cont
    })
}

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<Pat: Ord + Hash + ToRustSrc> Rule<Pat> {
    fn generate_parse<'a>(
        self: &'a Rc<Self>,
        parse_nodes: Option<&'a RefCell<OrderMap<Rc<Rule<Pat>>, (ParseNodeKind, Option<ParseNodeShape<ParseNodeKind>>)>>>
    ) -> Thunk<impl FnOnce(Continuation) -> Continuation + 'a> {
        Thunk::new(move |cont| match (&**self, parse_nodes) {
            (Rule::Empty, _) => cont,
            (Rule::Match(pat), _) => {
                check(&format!("let Some(_range) = p.input_consume_left(_range, {})", pat.to_rust_src()))(cont)
            }
            (Rule::NotMatch(pat), _) => {
                check(&format!("p.input_consume_left(_range, {}).is_none()", pat.to_rust_src()))(cont)
            }
            (Rule::Call(r), _) => call(CodeLabel(r.clone()))(cont),
            (Rule::Concat([left, right]), None) => (
                left.generate_parse(None) +
                right.generate_parse(None)
            )(cont),
            (Rule::Concat([left, right]), Some(parse_nodes)) => (
                thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                left.generate_parse(Some(parse_nodes)) +
                push_state("c.frame.range.subtract_suffix(_range).len()") +
                right.generate_parse(Some(parse_nodes)) +
                pop_state(|state| sppf_add(&self.parse_node_kind(parse_nodes), state))
            )(cont),
            (Rule::Or(rules), None) => {
                parallel(ThunkIter(rules.iter().map(|rule| {
                    rule.generate_parse(None)
                })))(cont)
            }
            (Rule::Or(rules), Some(parse_nodes)) => (
                thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                parallel(ThunkIter(rules.iter().map(|rule| {
                    push_state(&format!("{}.to_usize()", rule.parse_node_kind(parse_nodes))) +
                    rule.generate_parse(Some(parse_nodes))
                }))) +
                pop_state(|state| sppf_add(&self.parse_node_kind(parse_nodes), state))
            )(cont),
            (Rule::Opt(rule), _) => {
                let parse_node_kind = parse_nodes.and_then(|parse_nodes| {
                    rule.parse_node_kind(parse_nodes);
                    rule.fill_parse_node_shape(parse_nodes);
                    match parse_nodes.borrow()[rule].1.as_ref().unwrap() {
                        // TODO: unpack aliases?
                        ParseNodeShape::Choice | ParseNodeShape::Binary(..) => None,
                        _ => Some(self.parse_node_kind(parse_nodes)),
                    }
                });
                if let Some(parse_node_kind) = parse_node_kind {
                    (
                        thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                        opt(
                            rule.generate_parse(parse_nodes) +
                            sppf_add(&parse_node_kind, "0"),
                            )
                    )(cont)
                } else {
                    opt(rule.generate_parse(parse_nodes))(cont)
                }
            }
            (Rule::RepeatMany(rule, None), None) => fix(|label| {
                opt(rule.generate_parse(None) + call(label))
            })(cont),
            (Rule::RepeatMany(rule, None), Some(parse_nodes)) => fix(|label| {
                let more = Rc::new(Rule::RepeatMore(rule.clone(), None));
                opt(
                    thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                    rule.generate_parse(Some(parse_nodes)) +
                    push_state("c.frame.range.subtract_suffix(_range).len()") +
                    call(label) +
                    pop_state(move |state| sppf_add(&more.parse_node_kind(parse_nodes), state))
                )
            })(cont),
            (Rule::RepeatMany(elem, Some(sep)), parse_nodes) => {
                opt(Rc::new(Rule::RepeatMore(elem.clone(), Some(sep.clone()))).generate_parse(parse_nodes))(cont)
            }
            (Rule::RepeatMore(rule, None), None) => fix(|label| {
                rule.generate_parse(None) + opt(call(label))
            })(cont),
            (Rule::RepeatMore(elem, Some(sep)), None) => fix(|label| {
                elem.generate_parse(None) + opt(sep.generate_parse(None) + call(label))
            })(cont),
            (Rule::RepeatMore(rule, None), Some(parse_nodes)) => fix(|label| {
                thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                rule.generate_parse(Some(parse_nodes)) +
                push_state("c.frame.range.subtract_suffix(_range).len()") +
                opt(call(label)) +
                pop_state(|state| sppf_add(&self.parse_node_kind(parse_nodes), state))
            })(cont),
            (Rule::RepeatMore(elem, Some(sep)), Some(parse_nodes)) => fix(|label| {
                thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                elem.generate_parse(Some(parse_nodes)) +
                push_state("c.frame.range.subtract_suffix(_range).len()") +
                opt(
                    thunk!("
                assert_eq!(_range.start(), c.frame.range.start());") +
                    sep.generate_parse(None) +
                    push_state("c.frame.range.subtract_suffix(_range).len()") +
                    call(label) +
                    pop_state(|state| {
                        sppf_add(&Rc::new(Rule::Concat([
                            sep.clone(),
                            self.clone(),
                        ])).parse_node_kind(parse_nodes), state)
                    })
                ) +
                pop_state(|state| sppf_add(&self.parse_node_kind(parse_nodes), state))
            })(cont),
        })
    }
    fn generate_traverse(
        &self,
        node: &str,
        refutable: bool,
        parse_nodes: &RefCell<OrderMap<Rc<Rule<Pat>>, (ParseNodeKind, Option<ParseNodeShape<ParseNodeKind>>)>>,
    ) -> String {
        let mut out = String::new();
        macro put($($x:expr),*) {{ $(write!(out, "{}", $x).unwrap();)* }}

        match self {
            Rule::Empty | Rule::Match(_) | Rule::NotMatch(_) | Rule::Call(_) | Rule::RepeatMany(..) | Rule::RepeatMore(..) => {
                put!("::std::iter::once(");
                if refutable {
                    put!("Some(")
                }
                put!(node, ")");
                if refutable {
                    put!(")");
                }
            }
            Rule::Concat([left, right]) => {
                put!("self.parser.sppf.binary_children(", node, ").flat_map(move |(left, right)| {
            ", left.generate_traverse("left", refutable, parse_nodes), ".flat_map(move |left| {
                ", right.generate_traverse("right", refutable, parse_nodes).replace("\n", "\n    "), ".map(move |right| (left, right))
            })
        })");
            }
            Rule::Or(rules) => {
                put!("self.parser.sppf.unary_children(", node, ").flat_map(move |node| {
            enum Iter<");
                for i in 0..rules.len() {
                    put!("_", i, ",");
                }
                put!("> {");
                for i in 0..rules.len() {
                    put!("
                _", i, "(_", i, "),");
                }
                put!("
            }
            impl<");
                for i in 0..rules.len() {
                    put!("_", i, ": Iterator,");
                }
                put!("> Iterator for Iter<");
                for i in 0..rules.len() {
                    put!("_", i, ",");
                }
                put!(">
                where");
                for i in 0..rules.len() {
                    put!("
                    _", i, "::Item: Default,");
                }
                put!("
            {
                type Item = (");
                for i in 0..rules.len() {
                    put!("_", i, "::Item,");
                }
                put!(");
                fn next(&mut self) -> Option<Self::Item> {
                    let mut r = Self::Item::default();
                    match self {");
                for i in 0..rules.len() {
                    put!("
                        Iter::_", i, "(it) => r.", i, " = it.next()?,");
                }
                    put!("
                    }
                    Some(r)
                }
            }
            match node.kind {");
                for (i, rule) in rules.iter().enumerate() {
                    put!("
                ", rule.parse_node_kind(parse_nodes), " => Iter::_", i, "(", rule.generate_traverse("node", true, parse_nodes).replace("\n", "\n    "), "),");
                }
                put!("
                _ => unreachable!(),
            }
        })");
            }
            Rule::Opt(rule) => {
                put!("self.parser.sppf.unary_children(", node, ").flat_map(move |node| {
            match node.kind {
                ", rule.parse_node_kind(parse_nodes), " => {
                    Some(", rule.generate_traverse("node", true, parse_nodes).replace("\n", "\n        "), ".map(|x| (x,)))
                        .into_iter().flatten().chain(None)
                }
                ", Rc::new(Rule::Empty).parse_node_kind(parse_nodes), " => {
                    None.into_iter().flatten().chain(Some(<(_,)>::default()))
                }
                _ => unreachable!()
            }
        })");
            }
        }
        out.replace("\n", "\n    ")
    }
}
