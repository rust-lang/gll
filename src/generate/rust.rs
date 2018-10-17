use grammar::ParseNodeShape;
use grammar::{Grammar, MatchesEmpty, Rule, RuleWithNamedFields};
use ordermap::{OrderMap, OrderSet};
use scannerless;
use std::cell::RefCell;
use std::fmt;
use std::fmt::Write as FmtWrite;
use std::hash::Hash;
use std::io::Write;
use std::mem;
use std::ops::Add;
use std::process::{Command, Stdio};
use std::rc::Rc;

pub trait RustInputPat {
    fn rust_slice_ty() -> String;
    fn rust_matcher(&self) -> String;
}

impl<S: AsRef<str>> RustInputPat for scannerless::Pat<S> {
    fn rust_slice_ty() -> String {
        "str".to_string()
    }
    fn rust_matcher(&self) -> String {
        match self {
            scannerless::Pat::String(s) => format!("{:?}", s.as_ref()),
            scannerless::Pat::Range(start, end) => format!("{:?}", start..=end),
        }
    }
}

impl<Pat: PartialEq> RuleWithNamedFields<Pat> {
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

impl<Pat: Ord + Hash + MatchesEmpty + RustInputPat> Rule<Pat> {
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
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) => {
                assert_eq!(path, []);
                "()".to_string()
            }
            Rule::Call(r) => format!("{}<'a, 'i, I>", r),
            Rule::Concat(rules) => {
                if path.is_empty() {
                    return "()".to_string();
                }
                rules[path[0]].field_type(&path[1..])
            }
            Rule::Or(rules) => rules[path[0]].field_type(&path[1..]),
            Rule::Opt(rule) => [rule][path[0]].field_type(&path[1..]),
            Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => {
                assert_eq!(path, []);
                format!("[{}]", rule.field_type(&[]))
            }
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
            Rule::Eat(pat) => ParseNodeKind(pat.rust_matcher()),
            Rule::NegativeLookahead(pat) => ParseNodeKind(format!("!{}", pat.rust_matcher())),
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
            Rule::RepeatMore(rule, None) => ParseNodeKind(format!(
                // FIXME(rust-lang-nursery/rustfmt#3004) work around rustfmt removing trailing +.
                "({}+ HACK)",
                rule.parse_node_kind(parse_nodes).0
            )),
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
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) => ParseNodeShape::Opaque,
            Rule::Call(_) => unreachable!(),
            Rule::Concat([left, right]) => ParseNodeShape::Split(
                left.parse_node_kind(parse_nodes),
                right.parse_node_kind(parse_nodes),
            ),
            Rule::Or(_) => ParseNodeShape::Choice,
            Rule::Opt(rule) => ParseNodeShape::Opt(rule.parse_node_kind(parse_nodes)),
            Rule::RepeatMany(elem, sep) => ParseNodeShape::Opt(
                Rc::new(Rule::RepeatMore(elem.clone(), sep.clone())).parse_node_kind(parse_nodes),
            ),
            Rule::RepeatMore(rule, None) => ParseNodeShape::Split(
                rule.parse_node_kind(parse_nodes),
                Rc::new(Rule::RepeatMany(rule.clone(), None)).parse_node_kind(parse_nodes),
            ),
            Rule::RepeatMore(elem, Some(sep)) => ParseNodeShape::Split(
                elem.parse_node_kind(parse_nodes),
                Rc::new(Rule::Opt(Rc::new(Rule::Concat([
                    sep.clone(),
                    self.clone(),
                ]))))
                .parse_node_kind(parse_nodes),
            ),
        };
        parse_nodes.borrow_mut().get_mut(self).unwrap().1 = Some(shape);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ParseNodeKind(String);

impl fmt::Display for ParseNodeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "P!({})", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct CodeLabel(String);

impl fmt::Display for CodeLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "_C::{}", self.0)
    }
}

#[cfg_attr(rustfmt, rustfmt_skip)]
impl<Pat: Ord + Hash + MatchesEmpty + RustInputPat> Grammar<Pat> {
    pub fn generate_rust(&self) -> String {
        self.check();

        let mut out = String::new();
        macro put($($x:expr),*) {{ $(write!(out, "{}", $x).unwrap();)* }}

        let parse_nodes = RefCell::new(OrderMap::new());
        let mut named_parse_nodes = vec![];
        let mut code_labels = OrderMap::new();

        put!("
use gll::runtime::{Call, Continuation, ParseNodeKind, CodeLabel, ParseNodeShape, ParseNode, Range, traverse};
use std::any;
use std::fmt;
use std::marker::PhantomData;
use std::ops::{GeneratorState, Generator};

struct GenIter<G>(G);

impl<G: Generator<Return = ()>> Iterator for GenIter<G> {
    type Item = G::Yield;

    fn next(&mut self) -> Option<Self::Item> {
        match unsafe { self.0.resume() } {
            GeneratorState::Complete(..) => None,
            GeneratorState::Yielded(v) => Some(v),
        }
    }
}

#[derive(Debug)]
pub enum ParseError<T> {
    TooShort(T),
    NoParse,
}

pub type ParseResult<'a, 'i, I, T> =
    Result<Handle<'a, 'i, I, T>, ParseError<Handle<'a, 'i, I, T>>>;

pub type Any = dyn any::Any;

#[derive(Debug)]
pub struct Ambiguity<T>(T);

pub struct Handle<'a, 'i: 'a, I: 'a + ::gll::runtime::Input, T: ?Sized> {
    pub node: ParseNode<'i, _P>,
    pub parser: &'a ::gll::runtime::Parser<'i, _P, _C, I>,
    _marker: PhantomData<T>,
}

impl<'a, 'i, I: ::gll::runtime::Input, T: ?Sized> Copy for Handle<'a, 'i, I, T> {}

impl<'a, 'i, I: ::gll::runtime::Input, T: ?Sized> Clone for Handle<'a, 'i, I, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, 'i, I: ::gll::runtime::Input, T: ?Sized> Handle<'a, 'i, I, T> {
    pub fn source(self) -> &'a I::Slice {
        self.parser.input(self.node.range)
    }
    pub fn source_info(self) -> I::SourceInfo {
        self.parser.source_info(self.node.range)
    }
}

impl<'a, 'i, I: ::gll::runtime::Input, T> From<Ambiguity<Handle<'a, 'i, I, T>>> for Ambiguity<Handle<'a, 'i, I, Any>> {
    fn from(x: Ambiguity<Handle<'a, 'i, I, T>>) -> Self {
        Ambiguity(Handle {
            node: x.0.node,
            parser: x.0.parser,
            _marker: PhantomData,
        })
    }
}

impl<'a, 'i, I: ::gll::runtime::Input, T> From<Ambiguity<Handle<'a, 'i, I, [T]>>> for Ambiguity<Handle<'a, 'i, I, Any>> {
    fn from(x: Ambiguity<Handle<'a, 'i, I, [T]>>) -> Self {
        Ambiguity(Handle {
            node: x.0.node,
            parser: x.0.parser,
            _marker: PhantomData,
        })
    }
}

impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for Handle<'a, 'i, I, ()> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, \"{:?}\", self.source_info())
    }
}

impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for Handle<'a, 'i, I, Any> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        handle_any_match_type!(self, |handle| write!(f, \"{:?}\", handle))
    }
}

impl<'a, 'i, I: ::gll::runtime::Input, T> fmt::Debug for Handle<'a, 'i, I, [T]>
    where Handle<'a, 'i, I, T>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, \"{:?} => \", self.source_info())?;
        match self.all_list_heads() {
            ListHead::Cons(cons) => {
                for (i, (elem, rest)) in cons.enumerate() {
                    if i > 0 {
                        write!(f, \" | \")?;
                    }
                    enum Elem<T, L> {
                        One(T),
                        Spread(L),
                    }
                    impl<T: fmt::Debug, L: fmt::Debug> fmt::Debug for Elem<T, L> {
                        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                            match self {
                                Elem::One(x) => fmt::Debug::fmt(x, f),
                                Elem::Spread(xs) => {
                                    write!(f, \"..(\")?;
                                    fmt::Debug::fmt(xs, f)?;
                                    write!(f, \")\")
                                }
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
            }
            ListHead::Nil => {
                f.debug_list().entries(None::<()>).finish()?;
            }
        }
        Ok(())
    }
}

impl<'a, 'i, I: ::gll::runtime::Input, T> Iterator for Handle<'a, 'i, I, [T]> {
    type Item = Result<Handle<'a, 'i, I, T>, Ambiguity<Self>>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.all_list_heads() {
            ListHead::Cons(mut iter) => {
                let (elem, rest) = iter.next().unwrap();
                let original = *self;
                *self = rest;
                if iter.next().is_none() {
                    Some(Ok(elem))
                } else {
                    match self.node.kind.shape() {
                        ParseNodeShape::Opt(_) => {
                            self.node.range = Range(original.node.range.split_at(0).0);
                        }
                        _ => unreachable!(),
                    }
                    match self.one_list_head() {
                        ListHead::Nil => {}
                        _ => unreachable!(),
                    }
                    Some(Err(Ambiguity(original)))
                }
            }
            ListHead::Nil => None,
        }
    }
}

pub enum ListHead<C> {
    Cons(C),
    Nil,
}

impl<'a, 'i, I: ::gll::runtime::Input, T> Handle<'a, 'i, I, [T]> {
    fn one_list_head(self) -> ListHead<Result<(Handle<'a, 'i, I, T>, Handle<'a, 'i, I, [T]>), Ambiguity<Self>>> {
        match self.all_list_heads() {
            ListHead::Cons(mut iter) => {
                let first = iter.next().unwrap();
                if iter.next().is_none() {
                    ListHead::Cons(Ok(first))
                } else {
                    ListHead::Cons(Err(Ambiguity(self)))
                }
            }
            ListHead::Nil => ListHead::Nil,
        }
    }
    fn all_list_heads(mut self) -> ListHead<impl Iterator<Item = (Handle<'a, 'i, I, T>, Handle<'a, 'i, I, [T]>)>> {
        if let ParseNodeShape::Opt(_) = self.node.kind.shape() {
            if let Some(opt_child) = self.node.unpack_opt() {
                self.node = opt_child;
            } else {
                return ListHead::Nil;
            }
        }
        ListHead::Cons(self.parser.sppf.all_splits(self.node).flat_map(move |(elem, rest)| {
            if let ParseNodeShape::Split(..) = rest.kind.shape() {
                Some(self.parser.sppf.all_splits(rest)).into_iter().flatten().chain(None)
            } else {
                None.into_iter().flatten().chain(Some((elem, rest)))
            }
        }).map(move |(elem, rest)| {
            (Handle {
                node: elem,
                parser: self.parser,
                _marker: PhantomData,
            }, Handle { node: rest, ..self })
        }))
    }
}");
        for (name, rule) in &self.rules {
            let variants = rule.find_variant_fields();
            if let Some(variants) = &variants {
                put!("

pub enum ", name, "<'a, 'i: 'a, I: 'a + ::gll::runtime::Input> {");
                for (rule, variant, fields) in variants {
                    if fields.is_empty() {
                        put!("
    ", variant, "(Handle<'a, 'i, I, ", rule.field_type(&[]), ">),");
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
                            put!("Handle<'a, 'i, I, ", rule.field_pathset_type(paths), ">");
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

pub struct ", name, "<'a, 'i: 'a, I: 'a + ::gll::runtime::Input> {");
                for (field_name, paths) in &rule.fields {
                    let refutable = rule.rule.field_pathset_is_refutable(paths);
                    put!("
    pub ", field_name, ": ");
                    if refutable {
                        put!("Option<");
                    }
                    put!("Handle<'a, 'i, I, ", rule.rule.field_pathset_type(paths), ">");
                    if refutable {
                        put!(">");
                    }
                    put!(",");
                }
                if rule.fields.is_empty() {
                    put!("
    _marker: PhantomData<(&'a (), &'i (), I)>,");
                }
                put!("
}");
            }
            put!("

impl<'a, 'i, I: ::gll::runtime::Input<Slice = ", Pat::rust_slice_ty() ,">> ", name, "<'a, 'i, I> {
    pub fn parse_with<R>(
        input: I,
        f: impl for<'b, 'i2> FnOnce(
            &'b ::gll::runtime::Parser<'i2, _P, _C, I>,
            ParseResult<'b, 'i2, I, ", name, "<'b, 'i2, I>>,
        ) -> R,
    ) -> R {
        ::gll::runtime::Parser::with(input, |mut parser, range| {
            let call = Call {
                callee: ", CodeLabel(name.clone()), ",
                range,
            };
            parser.threads.spawn(
                Continuation {
                    code: call.callee,
                    fn_input: call.range,
                    state: 0,
                },
                call.range,
            );
            parse(&mut parser);
            let result = parser.memoizer.longest_result(call);
            f(&parser, result.ok_or(ParseError::NoParse).and_then(|range| {
                let handle = Handle {
                    node: ParseNode { kind: ", ParseNodeKind(name.clone()), ", range },
                    parser: &parser,
                    _marker: PhantomData,
                };
                if range == call.range {
                    Ok(handle)
                } else {
                    Err(ParseError::TooShort(handle))
                }
            }))
        })
    }
}

impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for ", name, "<'a, 'i, I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {");
            if let Some(variants) = &variants {
                put!("
        match self {");
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

impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for Handle<'a, 'i, I, ", name, "<'a, 'i, I>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, \"{:?}\", self.source_info())
    }
}");
                continue;
            }
            put!("

impl<'a, 'i, I: ::gll::runtime::Input> fmt::Debug for Handle<'a, 'i, I, ", name, "<'a, 'i, I>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, \"{:?} => \", self.source_info())?;
        for (i, x) in self.all().enumerate() {
            if i > 0 {
                write!(f, \" | \")?;
            }
            fmt::Debug::fmt(&x, f)?;
        }
        Ok(())
    }
}

impl<'a, 'i, I: ::gll::runtime::Input> ", name, "<'a, 'i, I> {");
            if let Some(variants) = &variants {
                for (rule, variant, fields) in variants {
                    put!("
    #[allow(non_snake_case)]
    fn ", variant, "_from_sppf(
        parser: &'a ::gll::runtime::Parser<'i, _P, _C, I>,
        _node: ParseNode<'i, _P>,
        _r: traverse!(typeof(ParseNode<'i, _P>) ", rule.generate_traverse_shape(false, &parse_nodes), "),
    ) -> Self {");
                    if fields.is_empty() {
                        put!("
        ", name, "::", variant, "(Handle {
            node: _node,
            parser,
            _marker: PhantomData,
        })");
                    } else {
                        put!("
        ", name, "::", variant, " {");
                        for (field_name, paths) in fields {
                            if rule.field_pathset_is_refutable(&paths) {
                                put!("
            ", field_name, ": None.or(_r");
                                for path in paths {
                                    for p in path {
                                        put!(" .", p);
                                    }
                                }
                                put!(").map(|node| Handle {
                node,
                parser,
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
                parser,
                _marker: PhantomData,
            },");
                            }
                        }
                        put!("
        }");
                    }
                    put!("
    }");
                }
            } else {
                put!("
    fn from_sppf(
        parser: &'a ::gll::runtime::Parser<'i, _P, _C, I>,
        _node: ParseNode<'i, _P>,
        _r: traverse!(typeof(ParseNode<'i, _P>) ", rule.rule.generate_traverse_shape(false, &parse_nodes), "),
    ) -> Self {
        ", name, " {");
                for (field_name, paths) in &rule.fields {
                    if rule.rule.field_pathset_is_refutable(paths) {
                        put!("
            ", field_name, ": None");
                        for path in paths {
                            put!(".or(_r");
                            for p in path {
                                put!(" .", p);
                            }
                            put!(")");
                        }
                        put!(".map(|node| Handle {
                node,
                parser,
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
                parser,
                _marker: PhantomData,
            },");
                    }
                }
                if rule.fields.is_empty() {
                    put!("
            _marker: PhantomData,");
                }
                put!("
        }
    }");
            }
            put!("
}

impl<'a, 'i, I: ::gll::runtime::Input> Handle<'a, 'i, I, ", name, "<'a, 'i, I>> {
    pub fn one(self) -> Result<", name, "<'a, 'i, I>, Ambiguity<Self>> {
        let mut iter = self.all();
        let first = iter.next().unwrap();
        if iter.next().is_none() {
            Ok(first)
        } else {
            Err(Ambiguity(self))
        }
    }
    pub fn all(self) -> impl Iterator<Item = ", name, "<'a, 'i, I>> {
        let _sppf = &self.parser.sppf;
        GenIter(move || {
            let node = self.node.unpack_alias();");
            if let Some(variants) = &variants {
                put!("
            for node in self.parser.sppf.all_choices(node) {
                match node.kind {");
                for (rule, variant, _) in variants {
                    put!("
                    ", rule.parse_node_kind(&parse_nodes), " => {
                        traverse!(_sppf, node, ", rule.generate_traverse_shape(false, &parse_nodes), ",
                            _r => yield ", name, "::", variant, "_from_sppf(self.parser, node, _r));
                    }");
                }
                put!("
                    _ => unreachable!(),
                }
            }");
            } else {
                put!("
            traverse!(_sppf, node, ", rule.rule.generate_traverse_shape(false, &parse_nodes), ",
                _r => yield ", name, "::from_sppf(self.parser, node, _r));");
            }
            put!("
        })
    }
    pub fn for_each(self, mut f: impl FnMut(", name, "<'a, 'i, I>)) {
        let _sppf = &self.parser.sppf;
        let node = self.node.unpack_alias();");
            if let Some(variants) = &variants {
                put!("
        for node in self.parser.sppf.all_choices(node) {
            match node.kind {");
                for (rule, variant, _) in variants {
                    put!("
                ", rule.parse_node_kind(&parse_nodes), " => {
                    traverse!(_sppf, node, ", rule.generate_traverse_shape(false, &parse_nodes), ",
                        _r => f(", name, "::", variant, "_from_sppf(self.parser, node, _r)));
                }");
                }
                put!("
                _ => unreachable!(),
            }
        }");
            } else {
                put!("
        traverse!(_sppf, node, ", rule.rule.generate_traverse_shape(false, &parse_nodes), ",
            _r => f(", name, "::from_sppf(self.parser, node, _r)));");
            }
            put!("
    }
}");
        }
        put!("
fn parse<I>(p: &mut ::gll::runtime::Parser<_P, _C, I>)
where I: ::gll::runtime::Input<Slice = ", Pat::rust_slice_ty() ,">
{
    while let Some(Call { callee: mut c, range: _range }) = p.threads.steal() {
        match c.code {");
        for (name, rule) in &self.rules {
            let parse_nodes = if rule.fields.is_empty() {
                None
            } else {
                Some(&parse_nodes)
            };
            let code_label = CodeLabel(name.clone());
            let parse_node_kind = ParseNodeKind(name.clone());
            let shape = if let Some(parse_nodes) = parse_nodes {
                ParseNodeShape::Alias(rule.rule.parse_node_kind(parse_nodes))
            } else {
                ParseNodeShape::Opaque
            };
            named_parse_nodes.push((parse_node_kind.clone(), shape));

            put!((
                reify_as(code_label.clone()) +
                rule.rule.clone().generate_parse(parse_nodes) +
                ret()
            )(Continuation {
                code_labels: &mut code_labels,
                fn_code_label: &mut code_label.clone(),
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
        let mut all_parse_nodes: Vec<_> = named_parse_nodes.into_iter().map(|(k, s)| {
            (k.clone(), s, Some(format!("{}<_>", k.0)))
        }).chain(parse_nodes.into_inner().into_iter().map(|(r, (k, s))| {
            (k, s.unwrap(), match &*r {
                Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => match &**rule {
                    Rule::Eat(_) => Some("[()]".to_string()),
                    Rule::Call(r) => Some(format!("[{}<_>]", r)),
                    _ => None,
                },
                _ => None,
            })
        })).collect();
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
        ", kind, " => $case(Handle::<_, ", ty, "> {
            node: $handle.node,
            parser: $handle.parser,
            _marker: PhantomData,
        }),");
            }
        }
        put!("
        _ => $case(Handle::<_, ()> {
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
        for (name, _) in &self.rules {
            put!("
    ", name, ",");
        }
        for (fn_label, &counter) in &code_labels {
            for i in 0..counter {
                put!("
    ", fn_label.0, "__", i, ",");
            }
        }
        put!("
}

impl CodeLabel for _C {
    fn enclosing_fn(self) -> Self {
        match self {");
        for (name, _) in &self.rules {
            put!("
            _C::", name, " => _C::", name, ",");
        }
        for (fn_label, &counter) in &code_labels {
            for i in 0..counter {
                let label = CodeLabel(format!("{}__{}", fn_label.0, i));
                put!("
            ", label, " => ", if code_labels.contains_key(&label) { &label } else { fn_label }, ",");
            }
        }
        put!("
        }
    }
}
");

        // HACK(eddyb) don't try to feed input to `rustfmt` without
        // knowing that it will at least try to read it.
        // *Somehow* (despite libstd ignoring it) we can get SIGPIPE.
        let has_rustfmt = Command::new("rustfmt")
            .arg("-V")
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .and_then(|child| child.wait_with_output().map(|o| o.status.success()))
            .unwrap_or(false);

        if !has_rustfmt {
            return out;
        }

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
    code_labels: &'a mut OrderMap<CodeLabel, usize>,
    fn_code_label: &'a mut CodeLabel,
    code_label_arms: &'a mut String,
    code: Code,
    nested_frames: Vec<Option<(CodeLabel, CodeLabel)>>,
}

#[derive(Clone)]
enum Code {
    Inline(String),
    Label(CodeLabel),
}

impl<'a> Continuation<'a> {
    fn next_code_label(&mut self) -> CodeLabel {
        let counter = self
            .code_labels
            .entry(self.fn_code_label.clone())
            .or_insert(0);
        let label = CodeLabel(format!("{}__{}", self.fn_code_label.0, counter));
        *counter += 1;
        label
    }

    fn clone(&mut self) -> Continuation {
        Continuation {
            code_labels: self.code_labels,
            fn_code_label: self.fn_code_label,
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
                p.threads.spawn(c, _range);",
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
            *cont.nested_frames.last_mut().unwrap() =
                Some((cont.to_label().clone(), cont.fn_code_label.clone()));
            *cont.fn_code_label = cont.next_code_label();
            cont.code_labels.insert(cont.fn_code_label.clone(), 0);
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
        if let Some((ret_label, outer_fn_label)) = cont.nested_frames.pop().unwrap() {
            let inner_fn_label = mem::replace(cont.fn_code_label, outer_fn_label);
            cont.reify_as(inner_fn_label);
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
                p.call(Call {{ callee: {}, range: _range }}, c);",
            cont.to_label(),
            callee
        ));
        cont
    })
}

fn ret() -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    thunk!(
        "
                p.ret(c, _range);"
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
        ", c.fn_input.subtract_suffix(_range), ",
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
            if let Some(Some((ret_label, outer_fn_label))) =
                child_cont.nested_frames.last().cloned()
            {
                if let None = nested_frames[child_cont.nested_frames.len() - 1] {
                    let inner_fn_label = mem::replace(child_cont.fn_code_label, outer_fn_label);
                    child_cont.reify_as(inner_fn_label);
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
        let outer_fn_label = mem::replace(cont.fn_code_label, label.clone());
        cont.code_labels.insert(label.clone(), 0);

        cont = (reify_as(label.clone()) + f(label) + ret())(cont);

        *cont.fn_code_label = outer_fn_label;
        cont.nested_frames = nested_frames;
        cont = call(mem::replace(cont.to_label(), ret_label))(cont);
        cont
    })
}

fn reify_as(label: CodeLabel) -> Thunk<impl FnOnce(Continuation) -> Continuation> {
    Thunk::new(|mut cont| {
        cont.reify_as(label);
        cont
    })
}

impl<Pat: Ord + Hash + MatchesEmpty + RustInputPat> Rule<Pat> {
    #[cfg_attr(rustfmt, rustfmt_skip)]
    fn generate_parse<'a>(
        self: &'a Rc<Self>,
        parse_nodes: Option<&'a RefCell<OrderMap<Rc<Rule<Pat>>, (ParseNodeKind, Option<ParseNodeShape<ParseNodeKind>>)>>>
    ) -> Thunk<impl FnOnce(Continuation) -> Continuation + 'a> {
        Thunk::new(move |cont| match (&**self, parse_nodes) {
            (Rule::Empty, _) => cont,
            (Rule::Eat(pat), _) => {
                check(&format!("let Some(_range) = p.input_consume_left(_range, {})", pat.rust_matcher()))(cont)
            }
            (Rule::NegativeLookahead(pat), _) => {
                check(&format!("p.input_consume_left(_range, {}).is_none()", pat.rust_matcher()))(cont)
            }
            (Rule::Call(r), _) => call(CodeLabel(r.clone()))(cont),
            (Rule::Concat([left, right]), None) => (
                left.generate_parse(None) +
                right.generate_parse(None)
            )(cont),
            (Rule::Concat([left, right]), Some(parse_nodes)) => (
                thunk!("
                assert_eq!(_range.start(), c.fn_input.start());") +
                left.generate_parse(Some(parse_nodes)) +
                push_state("c.fn_input.subtract_suffix(_range).len()") +
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
                assert_eq!(_range.start(), c.fn_input.start());") +
                parallel(ThunkIter(rules.iter().map(|rule| {
                    push_state(&format!("{}.to_usize()", rule.parse_node_kind(parse_nodes))) +
                    rule.generate_parse(Some(parse_nodes))
                }))) +
                pop_state(|state| sppf_add(&self.parse_node_kind(parse_nodes), state))
            )(cont),
            (Rule::Opt(rule), _) => opt(rule.generate_parse(parse_nodes))(cont),
            (Rule::RepeatMany(rule, None), None) => fix(|label| {
                opt(rule.generate_parse(None) + call(label))
            })(cont),
            (Rule::RepeatMany(rule, None), Some(parse_nodes)) => fix(|label| {
                let more = Rc::new(Rule::RepeatMore(rule.clone(), None));
                opt(
                    thunk!("
                assert_eq!(_range.start(), c.fn_input.start());") +
                    rule.generate_parse(Some(parse_nodes)) +
                    push_state("c.fn_input.subtract_suffix(_range).len()") +
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
                assert_eq!(_range.start(), c.fn_input.start());") +
                rule.generate_parse(Some(parse_nodes)) +
                push_state("c.fn_input.subtract_suffix(_range).len()") +
                opt(call(label)) +
                pop_state(|state| sppf_add(&self.parse_node_kind(parse_nodes), state))
            })(cont),
            (Rule::RepeatMore(elem, Some(sep)), Some(parse_nodes)) => fix(|label| {
                thunk!("
                assert_eq!(_range.start(), c.fn_input.start());") +
                elem.generate_parse(Some(parse_nodes)) +
                push_state("c.fn_input.subtract_suffix(_range).len()") +
                opt(
                    thunk!("
                assert_eq!(_range.start(), c.fn_input.start());") +
                    sep.generate_parse(None) +
                    push_state("c.fn_input.subtract_suffix(_range).len()") +
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
    fn generate_traverse_shape(
        &self,
        refutable: bool,
        parse_nodes: &RefCell<
            OrderMap<Rc<Rule<Pat>>, (ParseNodeKind, Option<ParseNodeShape<ParseNodeKind>>)>,
        >,
    ) -> String {
        match self {
            Rule::Empty
            | Rule::Eat(_)
            | Rule::NegativeLookahead(_)
            | Rule::Call(_)
            | Rule::RepeatMany(..)
            | Rule::RepeatMore(..) => {
                if refutable {
                    "?".to_string()
                } else {
                    "_".to_string()
                }
            }
            Rule::Concat([left, right]) => format!(
                "({}, {})",
                left.generate_traverse_shape(refutable, parse_nodes),
                right.generate_traverse_shape(refutable, parse_nodes)
            ),
            Rule::Or(rules) => {
                let mut s = String::from("{ ");
                for (i, rule) in rules.iter().enumerate() {
                    write!(
                        s,
                        "{}: {} => {},",
                        i,
                        rule.parse_node_kind(parse_nodes),
                        rule.generate_traverse_shape(true, parse_nodes)
                    );
                }
                write!(s, " }}");
                s
            }
            Rule::Opt(rule) => format!("[{}]", rule.generate_traverse_shape(true, parse_nodes)),
        }
    }
}
