pub use crate::parse_node::ParseNodeShape;

use crate::high::{type_lambda, ErasableL, ExistsL, PairL};
use crate::indexing_str;
use indexing::container_traits::Trustworthy;
use indexing::{self, Container, Index, Unknown};
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, BinaryHeap, HashMap, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::{self, Write};
use std::ops::{self, Deref, RangeInclusive};
use std::str;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Range<'i>(pub indexing::Range<'i>);

impl<'i> Deref for Range<'i> {
    type Target = indexing::Range<'i>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PartialOrd for Range<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.start(), self.end()).partial_cmp(&(other.start(), other.end()))
    }
}

impl Ord for Range<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.start(), self.end()).cmp(&(other.start(), other.end()))
    }
}

impl Hash for Range<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.start(), self.end()).hash(state);
    }
}

impl Range<'_> {
    pub fn subtract_suffix(self, other: Self) -> Self {
        assert_eq!(self.end(), other.end());
        Range(self.split_at(other.start() - self.start()).0)
    }
}

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineColumn {
    pub line: usize,
    pub column: usize,
}

impl fmt::Debug for LineColumn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", 1 + self.line, 1 + self.column)
    }
}

impl LineColumn {
    fn count(prefix: &str) -> Self {
        let (line, column) = prefix
            .split('\n')
            .enumerate()
            .last()
            .map_or((0, 0), |(i, s)| (i, s.chars().count()));
        LineColumn { line, column }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineColumnRange {
    pub start: LineColumn,
    pub end: LineColumn,
}

impl fmt::Debug for LineColumnRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}-{:?}", self.start, self.end)
    }
}

pub trait Input: Sized {
    type Container: Trustworthy;
    type Slice: ?Sized;
    type SourceInfo: fmt::Debug;
    // FIXME(eddyb) remove - replace with `SourceInfo` for the affected range
    type SourceInfoPoint: fmt::Debug;
    fn to_container(self) -> Self::Container;
    fn slice<'a, 'i>(
        input: &'a Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> &'a Self::Slice;
    fn source_info<'i>(
        input: &Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> Self::SourceInfo;
    fn source_info_point<'i>(
        input: &Container<'i, Self::Container>,
        index: Index<'i, Unknown>,
    ) -> Self::SourceInfoPoint;
}

impl<T> Input for &[T] {
    type Container = Self;
    type Slice = [T];
    type SourceInfo = ops::Range<usize>;
    type SourceInfoPoint = usize;
    fn to_container(self) -> Self::Container {
        self
    }
    fn slice<'b, 'i>(
        input: &'b Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> &'b Self::Slice {
        &input[range.0]
    }
    fn source_info<'i>(_: &Container<'i, Self::Container>, range: Range<'i>) -> Self::SourceInfo {
        range.as_range()
    }
    fn source_info_point<'i>(
        _: &Container<'i, Self::Container>,
        index: Index<'i, Unknown>,
    ) -> Self::SourceInfoPoint {
        index.integer()
    }
}

impl<'a> Input for &'a str {
    type Container = &'a indexing_str::Str;
    type Slice = str;
    type SourceInfo = LineColumnRange;
    type SourceInfoPoint = LineColumn;
    fn to_container(self) -> Self::Container {
        self.into()
    }
    fn slice<'b, 'i>(
        input: &'b Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> &'b Self::Slice {
        indexing_str::Str::slice(input, range.0)
    }
    fn source_info<'i>(
        input: &Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> Self::SourceInfo {
        let start = Self::source_info_point(input, range.first());
        // HACK(eddyb) add up `LineColumn`s to avoid counting twice.
        // Ideally we'd cache around a line map, like rustc's `SourceMap`.
        let mut end = LineColumn::count(Self::slice(input, range));
        end.line += start.line;
        if end.line == start.line {
            end.column += start.column;
        }
        LineColumnRange { start, end }
    }
    fn source_info_point<'i>(
        input: &Container<'i, Self::Container>,
        index: Index<'i, Unknown>,
    ) -> Self::SourceInfoPoint {
        let prefix_range = Range(input.split_at(index).0);
        LineColumn::count(Self::slice(input, prefix_range))
    }
}

pub trait InputMatch<Pat> {
    fn match_left(&self, pat: &'static Pat) -> Option<usize>;
    fn match_right(&self, pat: &'static Pat) -> Option<usize>;
}

impl<T: PartialEq> InputMatch<&'static [T]> for [T] {
    fn match_left(&self, pat: &&[T]) -> Option<usize> {
        if self.starts_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
    fn match_right(&self, pat: &&[T]) -> Option<usize> {
        if self.ends_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
}

impl<T: PartialOrd> InputMatch<RangeInclusive<T>> for [T] {
    fn match_left(&self, pat: &RangeInclusive<T>) -> Option<usize> {
        let x = self.first()?;
        if pat.start() <= x && x <= pat.end() {
            Some(1)
        } else {
            None
        }
    }
    fn match_right(&self, pat: &RangeInclusive<T>) -> Option<usize> {
        let x = self.last()?;
        if pat.start() <= x && x <= pat.end() {
            Some(1)
        } else {
            None
        }
    }
}

impl InputMatch<&'static str> for str {
    fn match_left(&self, pat: &&str) -> Option<usize> {
        if self.starts_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
    fn match_right(&self, pat: &&str) -> Option<usize> {
        if self.ends_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
}

impl InputMatch<RangeInclusive<char>> for str {
    fn match_left(&self, pat: &RangeInclusive<char>) -> Option<usize> {
        let c = self.chars().next()?;
        if *pat.start() <= c && c <= *pat.end() {
            Some(c.len_utf8())
        } else {
            None
        }
    }
    fn match_right(&self, pat: &RangeInclusive<char>) -> Option<usize> {
        let c = self.chars().rev().next()?;
        if *pat.start() <= c && c <= *pat.end() {
            Some(c.len_utf8())
        } else {
            None
        }
    }
}

pub struct Parser<'a, 'i, C: CodeLabel, I: Input> {
    state: &'a mut ParserState<'i, C, I>,
    current: Continuation<'i, C>,
    remaining: Range<'i>,
}

struct ParserState<'i, C: CodeLabel, I: Input> {
    threads: Threads<'i, C>,
    gss: GraphStack<'i, C>,
    memoizer: Memoizer<'i, C>,
    forest: ParseForest<'i, C::ParseNodeKind, I>,
    last_input_pos: Index<'i, Unknown>,
    expected_pats: Vec<&'static dyn fmt::Debug>,
}

#[derive(Debug)]
pub struct ParseError<A> {
    pub at: A,
    pub expected: Vec<&'static dyn fmt::Debug>,
}

pub type ParseResult<A, T> = Result<T, ParseError<A>>;

type_lambda! {
    pub type<'i> ParseForestL<P: ParseNodeKind, I: Input> = ParseForest<'i, P, I>;
    pub type<'i> ParseNodeL<P: ParseNodeKind> = ParseNode<'i, P>;
}

pub type OwnedParseForestAndNode<P, I> = ExistsL<PairL<ParseForestL<P, I>, ParseNodeL<P>>>;

impl<'i, C: CodeStep<I>, I: Input> Parser<'_, 'i, C, I> {
    pub fn parse(
        input: I,
        callee: C,
        kind: C::ParseNodeKind,
    ) -> ParseResult<I::SourceInfoPoint, OwnedParseForestAndNode<C::ParseNodeKind, I>> {
        ErasableL::indexing_scope(input.to_container(), |lifetime, input| {
            let call = Call {
                callee,
                range: Range(input.range()),
            };
            let mut state = ParserState {
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
                forest: ParseForest {
                    input,
                    possible_choices: HashMap::new(),
                    possible_splits: HashMap::new(),
                },
                last_input_pos: call.range.first(),
                expected_pats: vec![],
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
            while let Some(Call { callee, range }) = state.threads.steal() {
                callee.code.step(Parser {
                    state: &mut state,
                    current: callee,
                    remaining: range,
                });
            }

            // If the function call we started with ever returned,
            // we will find an entry for it in the memoizer, from
            // which we pick the longest match, which is only a
            // successful parse if it's as long as the input.
            let error = ParseError {
                at: I::source_info_point(&state.forest.input, state.last_input_pos),
                expected: state.expected_pats,
            };
            match state.memoizer.longest_result(call) {
                None => Err(error),
                Some(range) => {
                    if range == call.range {
                        Ok(OwnedParseForestAndNode::pack(
                            lifetime,
                            (state.forest, ParseNode { kind, range }),
                        ))
                    } else {
                        Err(error)
                    }
                }
            }
        })
    }

    pub fn input_consume_left<'a, Pat: fmt::Debug>(
        &'a mut self,
        pat: &'static Pat,
    ) -> Option<Parser<'a, 'i, C, I>>
    where
        I::Slice: InputMatch<Pat>,
    {
        let start = self.remaining.first();
        if start > self.state.last_input_pos {
            self.state.last_input_pos = start;
            self.state.expected_pats.clear();
        }
        match self.state.forest.input(self.remaining).match_left(pat) {
            Some(n) => {
                let (matching, after, _) = self.remaining.split_at(n);
                if n > 0 {
                    self.state.last_input_pos = after.first();
                    self.state.expected_pats.clear();
                }
                Some(Parser {
                    state: self.state,
                    current: Continuation {
                        result: Range(self.current.result.join(matching).unwrap()),
                        ..self.current
                    },
                    remaining: Range(after),
                })
            }
            None => {
                if start == self.state.last_input_pos {
                    self.state.expected_pats.push(pat);
                }
                None
            }
        }
    }

    pub fn input_consume_right<'a, Pat>(
        &'a mut self,
        pat: &'static Pat,
    ) -> Option<Parser<'a, 'i, C, I>>
    where
        I::Slice: InputMatch<Pat>,
    {
        // FIXME(eddyb) implement error reporting support like in `input_consume_left`
        match self.state.forest.input(self.remaining).match_right(pat) {
            Some(n) => {
                let (before, matching, _) = self.remaining.split_at(self.remaining.len() - n);
                Some(Parser {
                    state: self.state,
                    current: Continuation {
                        result: Range(matching.join(self.current.result.0).unwrap()),
                        ..self.current
                    },
                    remaining: Range(before),
                })
            }
            None => None,
        }
    }

    // FIXME(eddyb) maybe specialize this further, for `forest_add_split`?
    pub fn save(&mut self, kind: C::ParseNodeKind) {
        let old_saved = self.current.saved.replace(ParseNode {
            kind,
            range: self.current.result,
        });
        assert_eq!(old_saved, None);
    }

    pub fn take_saved(&mut self) -> ParseNode<'i, C::ParseNodeKind> {
        self.current.saved.take().unwrap()
    }

    pub fn forest_add_choice(&mut self, kind: C::ParseNodeKind, choice: C::ParseNodeKind) {
        self.state
            .forest
            .possible_choices
            .entry(ParseNode {
                kind,
                range: self.current.result,
            })
            .or_default()
            .insert(choice);
    }

    // FIXME(eddyb) safeguard this against misuse.
    pub fn forest_add_split(
        &mut self,
        kind: C::ParseNodeKind,
        left: ParseNode<'i, C::ParseNodeKind>,
    ) {
        self.state
            .forest
            .possible_splits
            .entry(ParseNode {
                kind,
                range: self.current.result,
            })
            .or_default()
            .insert(left.range.len());
    }

    pub fn spawn(&mut self, next: C) {
        self.state.threads.spawn(
            Continuation {
                code: next,
                ..self.current
            },
            self.remaining,
        );
    }

    pub fn call(&mut self, callee: C, next: C) {
        let call = Call {
            callee,
            range: self.remaining,
        };
        let next = Continuation {
            code: next,
            ..self.current
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
        let call_result = self.current.result;
        let remaining = self.remaining;
        let call = Call {
            callee: self.current.code.enclosing_fn(),
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

impl<'i, C: CodeLabel> Threads<'i, C> {
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

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Continuation<'i, C: CodeLabel> {
    code: C,
    saved: Option<ParseNode<'i, C::ParseNodeKind>>,
    // FIXME(eddyb) for GC purposes, this would also need to be a `ParseNode`,
    // except that's not always the case? But `ParseNode | Range` seems likely
    // to be a deoptimization, especially if `ParseNode` stops containing a
    // `Range` (e.g. if it's an index in a node array).
    result: Range<'i>,
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

impl<C: CodeLabel> GraphStack<'_, C> {
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

impl<'i, C: CodeLabel> Memoizer<'i, C> {
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

/// A parse forest, in SPPF (Shared Packed Parse Forest) representation.
pub struct ParseForest<'i, P: ParseNodeKind, I: Input> {
    input: Container<'i, I::Container>,
    possible_choices: HashMap<ParseNode<'i, P>, BTreeSet<P>>,
    possible_splits: HashMap<ParseNode<'i, P>, BTreeSet<usize>>,
}

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

pub trait CodeLabel: fmt::Debug + Ord + Hash + Copy + 'static {
    type ParseNodeKind: ParseNodeKind;

    fn enclosing_fn(self) -> Self;
}

pub trait CodeStep<I: Input>: CodeLabel {
    fn step<'i>(self, p: Parser<'_, 'i, Self, I>);
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
pub use crate::__runtime_traverse as traverse;

#[macro_export]
macro_rules! __runtime_traverse {
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
        $crate::runtime::nd::Id::new()
    };
    (all($forest:ident) ?) => {
        $crate::runtime::nd::Id::new().map(Some)
    };
    (all($forest:ident) ($l_shape:tt, $r_shape:tt)) => {
        $crate::runtime::nd::FromIterK::new($forest, $crate::runtime::ParseForest::all_splits)
            .then(traverse!(all($forest) $l_shape).pairs(traverse!(all($forest) $r_shape)))
    };
    (all($forest:ident) { $($i:tt $_i:ident: $kind:pat => $shape:tt,)* }) => {
        $crate::runtime::nd::FromIter::new(move |node| {
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
        $crate::runtime::nd::FromIter::new(move |node| {
            match $crate::runtime::ParseNode::unpack_opt(node) {
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
