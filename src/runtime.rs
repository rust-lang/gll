use grammer::forest::{GrammarReflector, Node, OwnedParseForestAndNode};
use grammer::input::{Input, InputMatch, Range};
use grammer::parser::{ParseResult, Parser};
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, BinaryHeap, HashMap};
use std::fmt;
use std::hash::Hash;
use std::io::{self, Write};

pub struct Runtime<'a, 'i, C: CodeLabel, I: Input, Pat> {
    parser: Parser<'a, 'i, C::GrammarReflector, I, Pat>,
    state: &'a mut RuntimeState<'i, C>,
    current: C,
    saved: Option<Node<'i, C::GrammarReflector>>,
}

struct RuntimeState<'i, C: CodeLabel> {
    threads: Threads<'i, C>,
    gss: GraphStack<'i, C>,
    memoizer: Memoizer<'i, C>,
}

impl<'i, G, C, I: Input, Pat: Ord> Runtime<'_, 'i, C, I, Pat>
where
    G: GrammarReflector,
    G::NodeKind: Ord,
    C: CodeStep<I, Pat, GrammarReflector = G>,
{
    pub fn parse(
        grammar: G,
        input: I,
        callee: C,
        kind: G::NodeKind,
    ) -> ParseResult<I::SourceInfoPoint, Pat, OwnedParseForestAndNode<G, I>> {
        Parser::parse_with(grammar, input, |mut parser| {
            let call = Call {
                callee,
                range: parser.remaining(),
            };
            let mut state = RuntimeState {
                threads: Threads {
                    queue: BinaryHeap::new(),
                    seen: BTreeSet::new(),
                },
                gss: GraphStack {
                    returns: HashMap::new(),
                },
                memoizer: Memoizer {
                    lengths: HashMap::new(),
                },
            };

            // Start with one thread, at the provided entry-point.
            state.threads.spawn(
                Continuation {
                    code: call.callee,
                    saved: None,
                    result: Range(call.range.frontiers().0),
                },
                call.range,
            );

            // Run all threads to completion.
            while let Some(next) = state.threads.steal() {
                let Call {
                    callee:
                        Continuation {
                            code,
                            saved,
                            result,
                        },
                    range,
                } = next;
                code.step(Runtime {
                    parser: parser.with_result_and_remaining(result, range),
                    state: &mut state,
                    current: code,
                    saved,
                });
            }

            // If the function call we started with ever returned,
            // we will find an entry for it in the memoizer, from
            // which we pick the longest match.
            state
                .memoizer
                .longest_result(call)
                .map(|range| Node { kind, range })
        })
    }

    pub fn input_consume_left<'a, SpecificPat: Into<Pat>>(
        &'a mut self,
        pat: SpecificPat,
    ) -> Option<Runtime<'a, 'i, C, I, Pat>>
    where
        I::Slice: InputMatch<SpecificPat>,
    {
        match self.parser.input_consume_left(pat) {
            Some(parser) => Some(Runtime {
                parser,
                state: self.state,
                current: self.current,
                saved: self.saved,
            }),
            None => None,
        }
    }

    pub fn input_consume_right<'a, SpecificPat: Into<Pat>>(
        &'a mut self,
        pat: SpecificPat,
    ) -> Option<Runtime<'a, 'i, C, I, Pat>>
    where
        I::Slice: InputMatch<SpecificPat>,
    {
        match self.parser.input_consume_right(pat) {
            Some(parser) => Some(Runtime {
                parser,
                state: self.state,
                current: self.current,
                saved: self.saved,
            }),
            None => None,
        }
    }

    // FIXME(eddyb) maybe specialize this further, for `forest_add_split`?
    pub fn save(&mut self, kind: G::NodeKind) {
        let old_saved = self.saved.replace(Node {
            kind,
            range: self.parser.take_result(),
        });
        assert_eq!(old_saved, None);
    }

    pub fn take_saved(&mut self) -> Node<'i, G> {
        self.saved.take().unwrap()
    }

    // FIXME(eddyb) safeguard this against misuse.
    pub fn forest_add_choice(&mut self, kind: G::NodeKind, choice: usize) {
        self.parser.forest_add_choice(kind, choice);
    }

    // FIXME(eddyb) safeguard this against misuse.
    pub fn forest_add_split(&mut self, kind: G::NodeKind, left: Node<'i, G>) {
        self.parser.forest_add_split(kind, left);
    }

    pub fn spawn(&mut self, next: C) {
        self.state.threads.spawn(
            Continuation {
                code: next,
                saved: self.saved,
                result: self.parser.result(),
            },
            self.parser.remaining(),
        );
    }

    pub fn call(&mut self, callee: C, next: C) {
        let call = Call {
            callee,
            range: self.parser.remaining(),
        };
        let next = Continuation {
            code: next,
            saved: self.saved,
            result: self.parser.result(),
        };
        let returns = self.state.gss.returns.entry(call).or_default();
        if returns.insert(next) {
            if returns.len() > 1 {
                if let Some(lengths) = self.state.memoizer.lengths.get(&call) {
                    for &len in lengths {
                        let (call_result, remaining, _) = call.range.split_at(len);
                        self.state.threads.spawn(
                            Continuation {
                                result: Range(next.result.join(call_result).unwrap()),
                                ..next
                            },
                            Range(remaining),
                        );
                    }
                }
            } else {
                self.state.threads.spawn(
                    Continuation {
                        code: call.callee,
                        saved: None,
                        result: Range(call.range.frontiers().0),
                    },
                    call.range,
                );
            }
        }
    }

    pub fn ret(&mut self) {
        let call_result = self.parser.result();
        let remaining = self.parser.remaining();
        let call = Call {
            callee: self.current.enclosing_fn(),
            range: Range(call_result.join(remaining.0).unwrap()),
        };
        if self
            .state
            .memoizer
            .lengths
            .entry(call)
            .or_default()
            .insert(call_result.len())
        {
            if let Some(returns) = self.state.gss.returns.get(&call) {
                for &next in returns {
                    self.state.threads.spawn(
                        Continuation {
                            result: Range(next.result.join(call_result.0).unwrap()),
                            ..next
                        },
                        remaining,
                    );
                }
            }
        }
    }
}

struct Threads<'i, C: CodeLabel> {
    queue: BinaryHeap<Call<'i, Continuation<'i, C>>>,
    seen: BTreeSet<Call<'i, Continuation<'i, C>>>,
}

impl<'i, C: CodeLabel> Threads<'i, C>
where
    <C::GrammarReflector as GrammarReflector>::NodeKind: Ord,
{
    fn spawn(&mut self, next: Continuation<'i, C>, range: Range<'i>) {
        let t = Call {
            callee: next,
            range,
        };
        if self.seen.insert(t) {
            self.queue.push(t);
        }
    }
    fn steal(&mut self) -> Option<Call<'i, Continuation<'i, C>>> {
        if let Some(t) = self.queue.pop() {
            loop {
                let old = self.seen.iter().rev().next().cloned();
                if let Some(old) = old {
                    // TODO also check end point for proper "t.range includes old.range".
                    let new_includes_old = t.range.contains(old.range.start()).is_some();
                    if !new_includes_old {
                        self.seen.remove(&old);
                        continue;
                    }
                }
                break;
            }
            Some(t)
        } else {
            self.seen.clear();
            None
        }
    }
}

struct Continuation<'i, C: CodeLabel> {
    code: C,
    saved: Option<Node<'i, C::GrammarReflector>>,
    // FIXME(eddyb) for GC purposes, this would also need to be a `Node`,
    // except that's not always the case? But `Node | Range` seems likely
    // to be a deoptimization, especially if `Node` stops containing a
    // `Range` (e.g. if it's an index in a node array).
    result: Range<'i>,
}

// FIXME(eddyb) can't derive these on `Continuation<C>` because that puts
// bounds on `C` (and worse, `C::GrammarReflector`).
impl<C: CodeLabel> Copy for Continuation<'_, C> {}
impl<C: CodeLabel> Clone for Continuation<'_, C> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<C: CodeLabel> PartialEq for Continuation<'_, C> {
    fn eq(&self, other: &Self) -> bool {
        (self.code, self.saved, self.result) == (other.code, other.saved, other.result)
    }
}
impl<C: CodeLabel> Eq for Continuation<'_, C> {}
impl<C: CodeLabel> PartialOrd for Continuation<'_, C>
where
    <C::GrammarReflector as GrammarReflector>::NodeKind: Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.code, self.saved, self.result).partial_cmp(&(other.code, other.saved, other.result))
    }
}
impl<C: CodeLabel> Ord for Continuation<'_, C>
where
    <C::GrammarReflector as GrammarReflector>::NodeKind: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (self.code, self.saved, self.result).cmp(&(other.code, other.saved, other.result))
    }
}

// TODO(eddyb) figure out if `Call<Continuation<C>>` can be optimized,
// based on the fact that `result.end == range.start` should always hold.
// (Also, `range.end` is constant across a whole parse)
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct Call<'i, C> {
    callee: C,
    range: Range<'i>,
}

impl<C: fmt::Display> fmt::Display for Call<'_, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({}..{})",
            self.callee,
            self.range.start(),
            self.range.end()
        )
    }
}

impl<C: PartialOrd> PartialOrd for Call<'_, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (Reverse(self.range), &self.callee).partial_cmp(&(Reverse(other.range), &other.callee))
    }
}

impl<C: Ord> Ord for Call<'_, C> {
    fn cmp(&self, other: &Self) -> Ordering {
        (Reverse(self.range), &self.callee).cmp(&(Reverse(other.range), &other.callee))
    }
}

struct GraphStack<'i, C: CodeLabel> {
    returns: HashMap<Call<'i, C>, BTreeSet<Continuation<'i, C>>>,
}

impl<C: CodeLabel> GraphStack<'_, C>
where
    <C::GrammarReflector as GrammarReflector>::NodeKind: Ord,
{
    // FIXME(eddyb) figure out what to do here, now that
    // the GSS is no longer exposed in the public API.
    #[allow(unused)]
    fn dump_graphviz(&self, out: &mut dyn Write) -> io::Result<()> {
        writeln!(out, "digraph gss {{")?;
        writeln!(out, "    graph [rankdir=RL]")?;
        for (call, returns) in &self.returns {
            for next in returns {
                writeln!(
                    out,
                    r#"    "{:?}" -> "{:?}" [label="{:?}"]"#,
                    call,
                    Call {
                        callee: next.code.enclosing_fn(),
                        range: Range(next.result.join(call.range.0).unwrap()),
                    },
                    next.code
                )?;
            }
        }
        writeln!(out, "}}")
    }
}

struct Memoizer<'i, C: CodeLabel> {
    lengths: HashMap<Call<'i, C>, BTreeSet<usize>>,
}

impl<'i, C: CodeLabel> Memoizer<'i, C>
where
    <C::GrammarReflector as GrammarReflector>::NodeKind: Ord,
{
    fn results<'a>(&'a self, call: Call<'i, C>) -> impl DoubleEndedIterator<Item = Range<'i>> + 'a {
        self.lengths
            .get(&call)
            .into_iter()
            .flat_map(move |lengths| {
                lengths
                    .iter()
                    .map(move |&len| Range(call.range.split_at(len).0))
            })
    }
    fn longest_result(&self, call: Call<'i, C>) -> Option<Range<'i>> {
        self.results(call).rev().next()
    }
}

pub trait CodeLabel: fmt::Debug + Ord + Hash + Copy + 'static {
    type GrammarReflector: GrammarReflector;

    fn enclosing_fn(self) -> Self;
}

pub trait CodeStep<I: Input, Pat>: CodeLabel {
    fn step<'i>(self, rt: Runtime<'_, 'i, Self, I, Pat>);
}

// HACK(eddyb) iterator replacement for the `traverse!` macro.
pub mod cursor {
    pub trait Cursor<T: ?Sized> {
        fn read(&self, out: &mut T);
        fn advance(&mut self) -> bool;
    }

    #[derive(Clone)]
    pub struct FlattenIter<I: Iterator> {
        iter: I,
        cur: I::Item,
    }

    impl<I: Iterator> FlattenIter<I> {
        pub fn new(mut iter: I) -> Self {
            let cur = iter.next().unwrap();
            FlattenIter { iter, cur }
        }
    }

    impl<I: Iterator, T: ?Sized> Cursor<T> for FlattenIter<I>
    where
        I::Item: Cursor<T>,
    {
        fn read(&self, out: &mut T) {
            self.cur.read(out);
        }
        fn advance(&mut self) -> bool {
            self.cur.advance() || self.iter.next().map(|next| self.cur = next).is_some()
        }
    }

    #[derive(Clone)]
    pub enum Either<A, B> {
        Left(A),
        Right(B),
    }

    impl<A, B, T: ?Sized> Cursor<T> for Either<A, B>
    where
        A: Cursor<T>,
        B: Cursor<T>,
    {
        fn read(&self, out: &mut T) {
            match self {
                Either::Left(a) => a.read(out),
                Either::Right(b) => b.read(out),
            }
        }
        fn advance(&mut self) -> bool {
            match self {
                Either::Left(a) => a.advance(),
                Either::Right(b) => b.advance(),
            }
        }
    }

    #[derive(Clone)]
    pub struct Product<A, B> {
        a: A,
        b0: B,
        b: B,
    }

    impl<A, B: Clone> Product<A, B> {
        pub fn new(a: A, b: B) -> Self {
            Product {
                a,
                b0: b.clone(),
                b,
            }
        }
    }

    impl<A, B, T: ?Sized> Cursor<T> for Product<A, B>
    where
        A: Cursor<T>,
        B: Cursor<T> + Clone,
    {
        fn read(&self, out: &mut T) {
            self.a.read(out);
            self.b.read(out);
        }
        fn advance(&mut self) -> bool {
            self.b.advance() || {
                self.b = self.b0.clone();
                self.a.advance()
            }
        }
    }
}

pub mod traverse {
    use grammer::forest::{GrammarReflector, MoreThanOne, Node, ParseForest};
    use grammer::input::Input;

    use super::cursor::*;

    pub trait FromShape<Forest: Copy, Node: Copy>: Sized {
        type Shape: Shape<Forest, Node>;
        // FIXME(eddyb) use an array length const here instead when that works.
        type Fields: Default + AsMut<[Option<Node>]>;

        const SHAPE: Self::Shape;

        fn from_shape(forest: Forest, fields: Self::Fields) -> Self;

        fn one(forest: Forest, node: Node) -> Result<Self, MoreThanOne> {
            let mut fields = Self::Fields::default();
            Self::SHAPE.one(forest, node, fields.as_mut())?;
            Ok(Self::from_shape(forest, fields))
        }

        fn all(forest: Forest, node: Node) -> FromShapeAll<Self, Forest, Node> {
            FromShapeAll {
                forest,
                cur: Some(Self::SHAPE.all(forest, node)),
            }
        }
    }

    impl<Forest: Copy, Node: Copy> FromShape<Forest, Node> for () {
        type Shape = ty!(_);
        type Fields = [Option<Node>; 0];

        const SHAPE: Self::Shape = new!(_);

        fn from_shape(_: Forest, []: Self::Fields) {}
    }

    pub struct FromShapeAll<T: FromShape<Forest, Node>, Forest: Copy, Node: Copy> {
        forest: Forest,
        cur: Option<<T::Shape as Shape<Forest, Node>>::All>,
    }

    impl<T, Forest: Copy, Node: Copy> Iterator for FromShapeAll<T, Forest, Node>
    where
        T: FromShape<Forest, Node>,
    {
        type Item = T;

        fn next(&mut self) -> Option<T> {
            let cur = self.cur.as_mut()?;
            let mut fields = T::Fields::default();
            cur.read(fields.as_mut());
            if !cur.advance() {
                self.cur.take();
            }
            Some(T::from_shape(self.forest, fields))
        }
    }

    pub trait Shape<Forest: Copy, Node: Copy>: Copy {
        fn one(
            self,
            forest: Forest,
            node: Node,
            out: &mut [Option<Node>],
        ) -> Result<(), MoreThanOne>;

        type All: Cursor<[Option<Node>]>;
        fn all(self, forest: Forest, node: Node) -> Self::All;
    }

    #[derive(Copy, Clone)]
    pub struct Leaf(pub Option<usize>);

    impl<Forest: Copy, Node: Copy> Shape<Forest, Node> for Leaf {
        fn one(self, _: Forest, node: Node, out: &mut [Option<Node>]) -> Result<(), MoreThanOne> {
            if let Some(i) = self.0 {
                out[i] = Some(node);
            }
            Ok(())
        }

        type All = LeafCursor<Node>;
        fn all(self, _: Forest, node: Node) -> Self::All {
            LeafCursor(self.0, node)
        }
    }

    #[derive(Clone)]
    pub struct LeafCursor<Node>(Option<usize>, Node);

    impl<Node: Copy> Cursor<[Option<Node>]> for LeafCursor<Node> {
        fn read(&self, out: &mut [Option<Node>]) {
            if let Some(i) = self.0 {
                out[i] = Some(self.1);
            }
        }
        fn advance(&mut self) -> bool {
            false
        }
    }

    // HACK(eddyb) this is only because of dynamic dispatch / boxing:
    pub trait IteratorCloneHack<'a>: 'a + Iterator {
        fn clone_to_box(&self) -> Box<dyn IteratorCloneHack<'a, Item = Self::Item>>;
    }

    impl<'a, I: 'a + Iterator + Clone> IteratorCloneHack<'a> for I {
        fn clone_to_box(&self) -> Box<dyn IteratorCloneHack<'a, Item = Self::Item>> {
            Box::new(self.clone())
        }
    }

    impl<'a, T: 'a> Clone for Box<dyn IteratorCloneHack<'a, Item = T>> {
        fn clone(&self) -> Self {
            (**self).clone_to_box()
        }
    }

    #[derive(Copy, Clone)]
    pub struct Split<A, B>(pub A, pub B);

    impl<'a, 'i, G: GrammarReflector, I: Input, A, B> Shape<&'a ParseForest<'i, G, I>, Node<'i, G>>
        for Split<A, B>
    where
        A: Shape<&'a ParseForest<'i, G, I>, Node<'i, G>>,
        B: Shape<&'a ParseForest<'i, G, I>, Node<'i, G>>,
        B::All: Clone,

        // HACK(eddyb) these are only because of dynamic dispatch / boxing:
        A: 'a,
        B: 'a,
        G: 'a,
    {
        fn one(
            self,
            forest: &'a ParseForest<'i, G, I>,
            node: Node<'i, G>,
            out: &mut [Option<Node<'i, G>>],
        ) -> Result<(), MoreThanOne> {
            let (left, right) = forest.one_split(node)?;
            self.0.one(forest, left, out)?;
            self.1.one(forest, right, out)
        }

        type All = FlattenIter<Box<dyn IteratorCloneHack<'a, Item = Product<A::All, B::All>>>>;
        fn all(self, forest: &'a ParseForest<'i, G, I>, node: Node<'i, G>) -> Self::All {
            FlattenIter::new(Box::new(forest.all_splits(node).map(move |(left, right)| {
                Product::new(self.0.all(forest, left), self.1.all(forest, right))
            }))
                as Box<dyn IteratorCloneHack<'_, Item = Product<A::All, B::All>>>)
        }
    }

    #[derive(Copy, Clone)]
    pub struct Choice<A, M>(pub A, pub M);

    impl<'a, 'i, G: GrammarReflector, I: Input, A, M> Shape<&'a ParseForest<'i, G, I>, Node<'i, G>>
        for Choice<A, M>
    where
        A: Shape<&'a ParseForest<'i, G, I>, Node<'i, G>>,
        A::All: Clone,
        M: Shape<&'a ParseForest<'i, G, I>, Node<'i, G>>,

        // HACK(eddyb) these are only because of dynamic dispatch / boxing:
        A: 'a,
        M: 'a,
        G: 'a,
    {
        fn one(
            self,
            forest: &'a ParseForest<'i, G, I>,
            node: Node<'i, G>,
            out: &mut [Option<Node<'i, G>>],
        ) -> Result<(), MoreThanOne> {
            let node = forest.one_choice(node)?;
            self.1.one(forest, node, out)?;
            self.0.one(forest, node, out)
        }

        // HACK(eddyb) `A` is after `M` because `Product<X, Y>` keeps two copies
        // of `Y` (so that it can reset the `Y` when `X` advances), and we don't
        // want two copies of `M` (a dedicated reset mechanism might be better?).
        type All = FlattenIter<Box<dyn IteratorCloneHack<'a, Item = Product<M::All, A::All>>>>;
        fn all(self, forest: &'a ParseForest<'i, G, I>, node: Node<'i, G>) -> Self::All {
            FlattenIter::new(Box::new(
                forest.all_choices(node).map(move |node| {
                    Product::new(self.1.all(forest, node), self.0.all(forest, node))
                }),
            )
                as Box<dyn IteratorCloneHack<'_, Item = Product<M::All, A::All>>>)
        }
    }

    #[derive(Copy, Clone)]
    pub struct MatchCons<P, A, Tail>(pub P, pub A, pub Tail);

    impl<'i, Forest: Copy, G: GrammarReflector, A, Tail> Shape<Forest, Node<'i, G>>
        for MatchCons<G::NodeKind, A, Tail>
    where
        A: Shape<Forest, Node<'i, G>>,
        Tail: Shape<Forest, Node<'i, G>>,
    {
        fn one(
            self,
            forest: Forest,
            node: Node<'i, G>,
            out: &mut [Option<Node<'i, G>>],
        ) -> Result<(), MoreThanOne> {
            if node.kind == self.0 {
                self.1.one(forest, node, out)
            } else {
                self.2.one(forest, node, out)
            }
        }

        type All = Either<A::All, Tail::All>;
        fn all(self, forest: Forest, node: Node<'i, G>) -> Self::All {
            if node.kind == self.0 {
                Either::Left(self.1.all(forest, node))
            } else {
                Either::Right(self.2.all(forest, node))
            }
        }
    }

    #[derive(Copy, Clone)]
    pub struct MatchNil;

    impl<Forest: Copy, Node: Copy> Shape<Forest, Node> for MatchNil {
        fn one(self, _: Forest, _: Node, _: &mut [Option<Node>]) -> Result<(), MoreThanOne> {
            unreachable!()
        }

        type All = MatchNil;
        fn all(self, _: Forest, _: Node) -> Self::All {
            unreachable!()
        }
    }

    impl<T: ?Sized> Cursor<T> for MatchNil {
        fn read(&self, _: &mut T) {
            unreachable!()
        }
        fn advance(&mut self) -> bool {
            unreachable!()
        }
    }

    #[derive(Copy, Clone)]
    pub struct Opt<A>(pub A);

    impl<'a, 'i, G: GrammarReflector, I: Input, A> Shape<&'a ParseForest<'i, G, I>, Node<'i, G>>
        for Opt<A>
    where
        A: Shape<&'a ParseForest<'i, G, I>, Node<'i, G>>,
    {
        fn one(
            self,
            forest: &'a ParseForest<'i, G, I>,
            node: Node<'i, G>,
            out: &mut [Option<Node<'i, G>>],
        ) -> Result<(), MoreThanOne> {
            if let Some(node) = forest.unpack_opt(node) {
                self.0.one(forest, node, out)?;
            }
            Ok(())
        }

        type All = Either<A::All, LeafCursor<Node<'i, G>>>;
        fn all(self, forest: &'a ParseForest<'i, G, I>, node: Node<'i, G>) -> Self::All {
            match forest.unpack_opt(node) {
                Some(node) => Either::Left(self.0.all(forest, node)),
                None => Either::Right(LeafCursor(None, node)),
            }
        }
    }

    // HACK(eddyb) work around `macro_rules` not being `use`-able.
    pub use crate::__runtime_traverse_ty as ty;

    #[macro_export]
    macro_rules! __runtime_traverse_ty {
        (_) => {
            $crate::runtime::traverse::Leaf
        };
        ($i:literal) => {
            $crate::runtime::traverse::Leaf
        };
        (($l_shape:tt, $r_shape:tt)) => {
            $crate::runtime::traverse::Split<
                $crate::runtime::traverse::ty!($l_shape),
                $crate::runtime::traverse::ty!($r_shape),
            >
        };
        ({ $kind_ty:ty; $at_shape:tt @ $($kind:expr => $shape:tt,)* }) => {
            $crate::runtime::traverse::Choice<
                $crate::runtime::traverse::ty!($at_shape),
                $crate::runtime::traverse::ty!(match($kind_ty) { $($shape,)* }),
            >
        };
        (match($kind_ty:ty) { $shape0:tt, $($shape:tt,)* }) => {
            $crate::runtime::traverse::MatchCons<
                $kind_ty,
                $crate::runtime::traverse::ty!($shape0),
                $crate::runtime::traverse::ty!(match($kind_ty) { $($shape,)* }),
            >
        };
        (match($kind_ty:ty) {}) => { $crate::runtime::traverse::MatchNil };
        ([$shape:tt]) => {
            $crate::runtime::traverse::Opt<
                $crate::runtime::traverse::ty!($shape),
            >
        }
    }

    // HACK(eddyb) work around `macro_rules` not being `use`-able.
    pub use crate::__runtime_traverse_new as new;

    #[macro_export]
    macro_rules! __runtime_traverse_new {
        (_) => {
            $crate::runtime::traverse::Leaf(None)
        };
        ($i:literal) => {
            $crate::runtime::traverse::Leaf(Some($i))
        };
        (($l_shape:tt, $r_shape:tt)) => {
            $crate::runtime::traverse::Split(
                $crate::runtime::traverse::new!($l_shape),
                $crate::runtime::traverse::new!($r_shape),
            )
        };
        ({ $kind_ty:ty; $at_shape:tt @ $($kind:expr => $shape:tt,)* }) => {
            $crate::runtime::traverse::Choice(
                $crate::runtime::traverse::new!($at_shape),
                $crate::runtime::traverse::new!(match { $($kind => $shape,)* }),
            )
        };
        (match { $kind0:expr => $shape0:tt, $($kind:expr => $shape:tt,)* }) => {
            $crate::runtime::traverse::MatchCons(
                $kind0,
                $crate::runtime::traverse::new!($shape0),
                $crate::runtime::traverse::new!(match { $($kind => $shape,)* }),
            )
        };
        (match {}) => { $crate::runtime::traverse::MatchNil };
        ([$shape:tt]) => {
            $crate::runtime::traverse::Opt(
                $crate::runtime::traverse::new!($shape),
            )
        }
    }
}
