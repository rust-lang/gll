use crate::high::{type_lambda, ExistsL, PairL};
use crate::input::{Input, Range};
use crate::parse_node::ParseNodeShape;
use indexing::{self, Container};
use std::collections::{BTreeSet, HashMap, VecDeque};
use std::fmt;
use std::hash::Hash;
use std::io::{self, Write};
use std::str;

/// A parse forest, in SPPF (Shared Packed Parse Forest) representation.
pub struct ParseForest<'i, P: ParseNodeKind, I: Input> {
    // HACK(eddyb) `pub(crate)` only for `runtime`.
    pub(crate) input: Container<'i, I::Container>,
    pub(crate) possible_choices: HashMap<ParseNode<'i, P>, BTreeSet<P>>,
    pub(crate) possible_splits: HashMap<ParseNode<'i, P>, BTreeSet<usize>>,
}

type_lambda! {
    pub type<'i> ParseForestL<P: ParseNodeKind, I: Input> = ParseForest<'i, P, I>;
    pub type<'i> ParseNodeL<P: ParseNodeKind> = ParseNode<'i, P>;
}

pub type OwnedParseForestAndNode<P, I> = ExistsL<PairL<ParseForestL<P, I>, ParseNodeL<P>>>;

#[derive(Debug)]
pub struct MoreThanOne;

impl<'i, P: ParseNodeKind, I: Input> ParseForest<'i, P, I> {
    pub fn input(&self, range: Range<'i>) -> &I::Slice {
        I::slice(&self.input, range)
    }

    pub fn source_info(&self, range: Range<'i>) -> I::SourceInfo {
        I::source_info(&self.input, range)
    }

    pub fn one_choice(&self, node: ParseNode<'i, P>) -> Result<ParseNode<'i, P>, MoreThanOne> {
        match node.kind.shape() {
            ParseNodeShape::Choice => {
                let choices = &self.possible_choices[&node];
                if choices.len() > 1 {
                    return Err(MoreThanOne);
                }
                let &choice = choices.iter().next().unwrap();
                Ok(ParseNode {
                    kind: choice,
                    range: node.range,
                })
            }
            shape => unreachable!("one_choice({}): non-choice shape {}", node, shape),
        }
    }

    pub fn all_choices<'a>(
        &'a self,
        node: ParseNode<'i, P>,
    ) -> impl Iterator<Item = ParseNode<'i, P>> + Clone + 'a {
        match node.kind.shape() {
            ParseNodeShape::Choice => self
                .possible_choices
                .get(&node)
                .into_iter()
                .flatten()
                .cloned()
                .map(move |kind| ParseNode {
                    kind,
                    range: node.range,
                }),
            shape => unreachable!("all_choices({}): non-choice shape {}", node, shape),
        }
    }

    pub fn one_split(
        &self,
        node: ParseNode<'i, P>,
    ) -> Result<(ParseNode<'i, P>, ParseNode<'i, P>), MoreThanOne> {
        match node.kind.shape() {
            ParseNodeShape::Split(left_kind, right_kind) => {
                let splits = &self.possible_splits[&node];
                if splits.len() > 1 {
                    return Err(MoreThanOne);
                }
                let &split = splits.iter().next().unwrap();
                let (left, right, _) = node.range.split_at(split);
                Ok((
                    ParseNode {
                        kind: left_kind,
                        range: Range(left),
                    },
                    ParseNode {
                        kind: right_kind,
                        range: Range(right),
                    },
                ))
            }
            shape => unreachable!("one_split({}): non-split shape {}", node, shape),
        }
    }

    pub fn all_splits<'a>(
        &'a self,
        node: ParseNode<'i, P>,
    ) -> impl Iterator<Item = (ParseNode<'i, P>, ParseNode<'i, P>)> + Clone + 'a {
        match node.kind.shape() {
            ParseNodeShape::Split(left_kind, right_kind) => self
                .possible_splits
                .get(&node)
                .into_iter()
                .flatten()
                .cloned()
                .map(move |i| {
                    let (left, right, _) = node.range.split_at(i);
                    (
                        ParseNode {
                            kind: left_kind,
                            range: Range(left),
                        },
                        ParseNode {
                            kind: right_kind,
                            range: Range(right),
                        },
                    )
                }),
            shape => unreachable!("all_splits({}): non-split shape {}", node, shape),
        }
    }

    pub fn dump_graphviz(&self, out: &mut dyn Write) -> io::Result<()> {
        writeln!(out, "digraph forest {{")?;
        let mut queue: VecDeque<_> = self
            .possible_choices
            .keys()
            .chain(self.possible_splits.keys())
            .cloned()
            .collect();
        let mut seen: BTreeSet<_> = queue.iter().cloned().collect();
        let mut p = 0;
        while let Some(source) = queue.pop_front() {
            writeln!(out, "    {:?} [shape=box]", source.to_string())?;
            let mut add_children = |children: &[(&str, ParseNode<'i, P>)]| -> io::Result<()> {
                writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                writeln!(out, "    {:?} -> p{}:n", source.to_string(), p)?;
                for &(port, child) in children {
                    writeln!(
                        out,
                        "    p{}:{} -> {:?}:n [dir=none]",
                        p,
                        port,
                        child.to_string()
                    )?;
                    if seen.insert(child) {
                        queue.push_back(child);
                    }
                }
                p += 1;
                Ok(())
            };
            match source.kind.shape() {
                ParseNodeShape::Opaque => {}

                ParseNodeShape::Alias(_) => {
                    add_children(&[("s", source.unpack_alias())])?;
                }

                ParseNodeShape::Opt(_) => {
                    if let Some(child) = source.unpack_opt() {
                        add_children(&[("s", child)])?;
                    }
                }

                ParseNodeShape::Choice => {
                    for child in self.all_choices(source) {
                        add_children(&[("s", child)])?;
                    }
                }

                ParseNodeShape::Split(..) => {
                    for (left, right) in self.all_splits(source) {
                        add_children(&[("sw", left), ("se", right)])?;
                    }
                }
            }
        }
        writeln!(out, "}}")
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ParseNode<'i, P: ParseNodeKind> {
    pub kind: P,
    pub range: Range<'i>,
}

impl<P: ParseNodeKind> ParseNode<'_, P> {
    pub fn unpack_alias(self) -> Self {
        match self.kind.shape() {
            ParseNodeShape::Alias(inner) => ParseNode {
                kind: inner,
                range: self.range,
            },
            shape => unreachable!("unpack_alias({}): non-alias shape {}", self, shape),
        }
    }

    pub fn unpack_opt(self) -> Option<Self> {
        match self.kind.shape() {
            ParseNodeShape::Opt(inner) => {
                if self.range.is_empty() {
                    None
                } else {
                    Some(ParseNode {
                        kind: inner,
                        range: self.range,
                    })
                }
            }
            shape => unreachable!("unpack_opt({}): non-opt shape {}", self, shape),
        }
    }
}

impl<P: ParseNodeKind> fmt::Display for ParseNode<'_, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} @ {}..{}",
            self.kind,
            self.range.start(),
            self.range.end()
        )
    }
}

impl<P: ParseNodeKind> fmt::Debug for ParseNode<'_, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} @ {}..{}",
            self.kind,
            self.range.start(),
            self.range.end()
        )
    }
}

pub trait ParseNodeKind: fmt::Display + Ord + Hash + Copy + 'static {
    fn shape(self) -> ParseNodeShape<Self>;
}

// FIXME(rust-lang/rust#54175) work around iterator adapter compile-time
// blowup issues by using a makeshift "non-determinism arrow toolkit".
pub mod nd {
    use std::iter;
    use std::marker::PhantomData;

    pub trait Arrow: Copy {
        type Input;
        type Output;
        type Iter: Iterator<Item = Self::Output> + Clone;
        fn apply(&self, x: Self::Input) -> Self::Iter;

        fn map<F: Fn(Self::Output) -> R, R>(self, f: F) -> Map<Self, F> {
            Map(self, f)
        }
        fn then<B: Arrow<Input = Self::Output>>(self, b: B) -> Then<Self, B> {
            Then(self, b)
        }
        fn pairs<B: Arrow>(self, b: B) -> Pairs<Self, B>
        where
            Self::Output: Copy,
            B::Input: Copy,
        {
            Pairs(self, b)
        }
    }

    macro_rules! derive_copy {
        ($name:ident<$($param:ident $(: $bound:ident)*),*>) => {
            impl<$($param $(: $bound)*),*> Copy for $name<$($param),*> {}
            impl<$($param $(: $bound)*),*> Clone for $name<$($param),*> {
                fn clone(&self) -> Self {
                    *self
                }
            }
        }
    }

    pub struct Id<T>(PhantomData<T>);
    derive_copy!(Id<T>);
    impl<T> Id<T> {
        pub fn new() -> Self {
            Id(PhantomData)
        }
    }
    impl<T: Clone> Arrow for Id<T> {
        type Input = T;
        type Output = T;
        type Iter = iter::Once<T>;
        fn apply(&self, x: T) -> Self::Iter {
            iter::once(x)
        }
    }

    pub struct FromIter<T, F>(F, PhantomData<T>);
    derive_copy!(FromIter<T, F: Copy>);
    impl<T, F> FromIter<T, F> {
        pub fn new(f: F) -> Self {
            FromIter(f, PhantomData)
        }
    }
    impl<T, F: Copy + Fn(T) -> I, I: Iterator + Clone> Arrow for FromIter<T, F> {
        type Input = T;
        type Output = I::Item;
        type Iter = I;
        fn apply(&self, x: T) -> I {
            self.0(x)
        }
    }

    pub struct FromIterK<K, T, F>(K, F, PhantomData<T>);
    derive_copy!(FromIterK<K: Copy, T, F: Copy>);
    impl<K, T, F> FromIterK<K, T, F> {
        pub fn new(k: K, f: F) -> Self {
            FromIterK(k, f, PhantomData)
        }
    }
    impl<K: Copy, T, F: Copy + Fn(K, T) -> I, I: Iterator + Clone> Arrow for FromIterK<K, T, F> {
        type Input = T;
        type Output = I::Item;
        type Iter = I;
        fn apply(&self, x: T) -> I {
            self.1(self.0, x)
        }
    }

    #[derive(Copy, Clone)]
    pub struct Map<A, F>(A, F);
    impl<A: Arrow, F: Copy + Fn(A::Output) -> R, R> Arrow for Map<A, F> {
        type Input = A::Input;
        type Output = R;
        type Iter = iter::Map<A::Iter, F>;
        fn apply(&self, x: Self::Input) -> Self::Iter {
            self.0.apply(x).map(self.1)
        }
    }

    #[derive(Clone)]
    pub struct ThenIter<A: Arrow, B: Arrow<Input = A::Output>> {
        a_iter: A::Iter,
        b_arrow: B,
        b_iter: Option<B::Iter>,
        // HACK(eddyb) this field is useless (never set to `Some`)
        // (see `match self.b_iter_backwards` below for more details).
        b_iter_backwards: Option<B::Iter>,
    }
    impl<A: Arrow, B: Arrow<Input = A::Output>> Iterator for ThenIter<A, B> {
        type Item = B::Output;
        fn next(&mut self) -> Option<Self::Item> {
            loop {
                if let Some(ref mut b_iter) = self.b_iter {
                    if let x @ Some(_) = b_iter.next() {
                        return x;
                    }
                }
                match self.a_iter.next() {
                    // HACK(eddyb) this never does anything, but without a *second*
                    // call to `B::Iter::next`, LLVM spends more time optimizing.
                    None => {
                        return match self.b_iter_backwards {
                            Some(ref mut b_iter) => b_iter.next(),
                            None => None,
                        }
                    }
                    Some(x) => self.b_iter = Some(self.b_arrow.apply(x)),
                }
            }
        }
    }

    #[derive(Copy, Clone)]
    pub struct Then<A, B>(A, B);
    impl<A: Arrow, B: Arrow<Input = A::Output>> Arrow for Then<A, B> {
        type Input = A::Input;
        type Output = B::Output;
        type Iter = ThenIter<A, B>;
        fn apply(&self, x: Self::Input) -> Self::Iter {
            ThenIter {
                a_iter: self.0.apply(x),
                b_arrow: self.1,
                b_iter: None,
                b_iter_backwards: None,
            }
        }
    }

    #[derive(Clone)]
    pub struct PairsIter<A: Arrow, B: Arrow>
    where
        A::Output: Copy,
        B::Input: Copy,
    {
        a_iter: A::Iter,
        b_iter0: B::Iter,
        a_output_b_iter: Option<(A::Output, B::Iter)>,
    }
    impl<A: Arrow, B: Arrow> Iterator for PairsIter<A, B>
    where
        A::Output: Copy,
        B::Input: Copy,
    {
        type Item = (A::Output, B::Output);
        fn next(&mut self) -> Option<Self::Item> {
            loop {
                if let Some((x, ref mut b_iter)) = self.a_output_b_iter {
                    if let Some(y) = b_iter.next() {
                        return Some((x, y));
                    }
                }
                match self.a_iter.next() {
                    None => return None,
                    Some(x) => {
                        self.a_output_b_iter = Some((x, self.b_iter0.clone()));
                    }
                }
            }
        }
    }

    #[derive(Copy, Clone)]
    pub struct Pairs<A, B>(A, B);
    impl<A: Arrow, B: Arrow> Arrow for Pairs<A, B>
    where
        A::Output: Copy,
        B::Input: Copy,
    {
        type Input = (A::Input, B::Input);
        type Output = (A::Output, B::Output);
        type Iter = PairsIter<A, B>;
        fn apply(&self, (x, y): Self::Input) -> Self::Iter {
            PairsIter {
                a_iter: self.0.apply(x),
                b_iter0: self.1.apply(y),
                a_output_b_iter: None,
            }
        }
    }
}

// HACK(eddyb) work around `macro_rules` not being `use`-able.
pub use crate::__forest_traverse as traverse;

#[macro_export]
macro_rules! __forest_traverse {
    (typeof($leaf:ty) _) => { $leaf };
    (typeof($leaf:ty) ?) => { Option<traverse!(typeof($leaf) _)> };
    (typeof($leaf:ty) ($l_shape:tt, $r_shape:tt)) => { (traverse!(typeof($leaf) $l_shape), traverse!(typeof($leaf) $r_shape)) };
    (typeof($leaf:ty) { $($i:tt $_i:ident: $kind:pat => $shape:tt,)* }) => { ($(traverse!(typeof($leaf) $shape),)*) };
    (typeof($leaf:ty) [$shape:tt]) => { (traverse!(typeof($leaf) $shape),) };

    (one($forest:ident, $node:ident) _) => {
        $node
    };
    (one($forest:ident, $node:ident) ?) => {
        Some($node)
    };
    (one($forest:ident, $node:ident) ($l_shape:tt, $r_shape:tt)) => {
        {
            let (left, right) = $forest.one_split($node)?;
            (
                traverse!(one($forest, left) $l_shape),
                traverse!(one($forest, right) $r_shape),
            )
        }
    };
    (one($forest:ident, $node:ident) { $($i:tt $_i:ident: $kind:pat => $shape:tt,)* }) => {
        {
            let node = $forest.one_choice($node)?;
            let mut r = <($(traverse!(typeof(_) $shape),)*)>::default();
            match node.kind {
                $($kind => r.$i = traverse!(one($forest, node) $shape),)*
                _ => unreachable!(),
            }
            r
        }
    };
    (one($forest:ident, $node:ident) [$shape:tt]) => {
        {
            let mut r = <(traverse!(typeof(_) $shape),)>::default();
            if let Some(node) = $node.unpack_opt() {
                r.0 = traverse!(one($forest, node) $shape);
            }
            r
        }
    };

    (all($forest:ident) _) => {
        $crate::forest::nd::Id::new()
    };
    (all($forest:ident) ?) => {
        $crate::forest::nd::Id::new().map(Some)
    };
    (all($forest:ident) ($l_shape:tt, $r_shape:tt)) => {
        $crate::forest::nd::FromIterK::new($forest, $crate::forest::ParseForest::all_splits)
            .then(traverse!(all($forest) $l_shape).pairs(traverse!(all($forest) $r_shape)))
    };
    (all($forest:ident) { $($i:tt $_i:ident: $kind:pat => $shape:tt,)* }) => {
        $crate::forest::nd::FromIter::new(move |node| {
            #[derive(Clone)]
            enum Iter<$($_i),*> {
                $($_i($_i)),*
            }
            impl<$($_i: Iterator),*> Iterator for Iter<$($_i),*>
                where $($_i::Item: Default),*
            {
                type Item = ($($_i::Item),*);
                fn next(&mut self) -> Option<Self::Item> {
                    let mut r = Self::Item::default();
                    match self {
                        $(Iter::$_i(iter) => r.$i = iter.next()?),*
                    }
                    Some(r)
                }
            }
            $forest.all_choices(node).flat_map(move |node| {
                match node.kind {
                    $($kind => Iter::$_i(traverse!(all($forest) $shape).apply(node)),)*
                    _ => unreachable!(),
                }
            })
        })
    };
    (all($forest:ident) [$shape:tt]) => {
        $crate::forest::nd::FromIter::new(move |node| {
            match $crate::forest::ParseNode::unpack_opt(node) {
                Some(node) => {
                    Some(traverse!(all($forest) $shape).apply(node).map(|x| (x,)))
                        .into_iter().flatten().chain(None)
                }
                None => {
                    None.into_iter().flatten().chain(Some(<_>::default()))
                }
            }
        })
    }
}
