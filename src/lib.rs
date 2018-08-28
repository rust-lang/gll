#![feature(
    arbitrary_self_types,
    decl_macro,
    fn_traits,
    from_ref,
    nll,
    range_contains,
    slice_patterns,
    str_escape,
    try_from,
    unboxed_closures
)]

extern crate indexing;
extern crate ordermap;

use indexing::container_traits::{Contiguous, Trustworthy};
use indexing::{scope, Container};
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, BinaryHeap, HashMap, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::{self, Write};
use std::ops::{Deref, RangeInclusive};
use std::str;

pub mod grammar;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Range<'i>(pub indexing::Range<'i>);

impl<'i> Deref for Range<'i> {
    type Target = indexing::Range<'i>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'i> PartialOrd for Range<'i> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.start(), self.end()).partial_cmp(&(other.start(), other.end()))
    }
}

impl<'i> Ord for Range<'i> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.start(), self.end()).cmp(&(other.start(), other.end()))
    }
}

impl<'i> Hash for Range<'i> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.start(), self.end()).hash(state);
    }
}

impl<'i> Range<'i> {
    pub fn subtract_suffix(self, other: Self) -> Self {
        assert_eq!(self.end(), other.end());
        Range(self.split_at(other.start() - self.start()).0)
    }
}

pub struct Str(str);

unsafe impl Trustworthy for Str {
    type Item = u8;
    fn base_len(&self) -> usize {
        self.0.len()
    }
}

unsafe impl Contiguous for Str {
    fn begin(&self) -> *const Self::Item {
        self.0.as_ptr()
    }
    fn end(&self) -> *const Self::Item {
        unsafe { self.begin().offset(self.0.len() as isize) }
    }
    fn as_slice(&self) -> &[Self::Item] {
        self.0.as_bytes()
    }
}

pub trait InputSlice: Sized {
    type Slice: ?Sized;
    fn slice<'a, 'i>(input: &'a Container<'i, Self>, range: Range<'i>) -> &'a Self::Slice;
}

impl<'a, T> InputSlice for &'a [T] {
    type Slice = [T];
    fn slice<'b, 'i>(input: &'b Container<'i, Self>, range: Range<'i>) -> &'b Self::Slice {
        &input[range.0]
    }
}

impl<'a> InputSlice for &'a Str {
    type Slice = str;
    fn slice<'b, 'i>(input: &'b Container<'i, Self>, range: Range<'i>) -> &'b Self::Slice {
        unsafe { str::from_utf8_unchecked(&input[range.0]) }
    }
}

pub trait InputMatch<Pat> {
    fn match_left(&self, pat: Pat) -> Option<usize>;
    fn match_right(&self, pat: Pat) -> Option<usize>;
}

impl<'a, T: PartialEq> InputMatch<&'a [T]> for [T] {
    fn match_left(&self, pat: &[T]) -> Option<usize> {
        if self.starts_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
    fn match_right(&self, pat: &[T]) -> Option<usize> {
        if self.ends_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
}

impl<T: PartialOrd> InputMatch<RangeInclusive<T>> for [T] {
    fn match_left(&self, pat: RangeInclusive<T>) -> Option<usize> {
        if pat.contains(self.first()?) {
            Some(1)
        } else {
            None
        }
    }
    fn match_right(&self, pat: RangeInclusive<T>) -> Option<usize> {
        if pat.contains(self.last()?) {
            Some(1)
        } else {
            None
        }
    }
}

impl<'a> InputMatch<&'a str> for str {
    fn match_left(&self, pat: &str) -> Option<usize> {
        if self.starts_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
    fn match_right(&self, pat: &str) -> Option<usize> {
        if self.ends_with(pat) {
            Some(pat.len())
        } else {
            None
        }
    }
}

impl InputMatch<RangeInclusive<char>> for str {
    fn match_left(&self, pat: RangeInclusive<char>) -> Option<usize> {
        let c = self.chars().next()?;
        if pat.contains(&c) {
            Some(c.len_utf8())
        } else {
            None
        }
    }
    fn match_right(&self, pat: RangeInclusive<char>) -> Option<usize> {
        let c = self.chars().rev().next()?;
        if pat.contains(&c) {
            Some(c.len_utf8())
        } else {
            None
        }
    }
}

pub struct Parser<'i, P: ParseNodeKind, C: CodeLabel, I> {
    input: Container<'i, I>,
    pub gss: CallGraph<'i, C>,
    pub sppf: ParseGraph<'i, P>,
}

impl<'i, P: ParseNodeKind, C: CodeLabel, I: Trustworthy> Parser<'i, P, C, I> {
    pub fn with<R>(input: I, f: impl for<'i2> FnOnce(Parser<'i2, P, C, I>, Range<'i2>) -> R) -> R {
        scope(input, |input| {
            let range = input.range();
            f(
                Parser {
                    input,
                    gss: CallGraph {
                        threads: Threads {
                            queue: BinaryHeap::new(),
                            seen: BTreeSet::new(),
                        },
                        calls: HashMap::new(),
                    },
                    sppf: ParseGraph {
                        children: HashMap::new(),
                    },
                },
                Range(range),
            )
        })
    }
    pub fn input(&self, range: Range<'i>) -> &I::Slice
    where
        I: InputSlice,
    {
        I::slice(&self.input, range)
    }
    pub fn input_consume_left<Pat>(&self, range: Range<'i>, pat: Pat) -> Option<Range<'i>>
    where
        I: InputSlice,
        I::Slice: InputMatch<Pat>,
    {
        self.input(range)
            .match_left(pat)
            .map(|n| Range(range.split_at(n).1))
    }
    pub fn input_consume_right<Pat>(&self, range: Range<'i>, pat: Pat) -> Option<Range<'i>>
    where
        I: InputSlice,
        I::Slice: InputMatch<Pat>,
    {
        self.input(range)
            .match_right(pat)
            .map(|n| Range(range.split_at(range.len() - n).0))
    }
}

impl<'a, 'i, P: ParseNodeKind, C: CodeLabel> Parser<'i, P, C, &'a Str> {
    pub fn with_str<R>(
        input: &'a str,
        f: impl for<'i2> FnOnce(Parser<'i2, P, C, &'a Str>, Range<'i2>) -> R,
    ) -> R {
        let input = unsafe { &*(input as *const _ as *const Str) };
        Parser::with(input, f)
    }
}

pub struct Threads<'i, C: CodeLabel> {
    queue: BinaryHeap<Call<'i, Continuation<'i, C>>>,
    seen: BTreeSet<Call<'i, Continuation<'i, C>>>,
}

impl<'i, C: CodeLabel> Threads<'i, C> {
    pub fn spawn(&mut self, next: Continuation<'i, C>, range: Range<'i>) {
        let t = Call {
            callee: next,
            range,
        };
        if self.seen.insert(t) {
            self.queue.push(t);
        }
    }
    pub fn steal(&mut self) -> Option<Call<'i, Continuation<'i, C>>> {
        if let Some(t) = self.queue.pop() {
            loop {
                let old = self.seen.iter().rev().next().cloned();
                if let Some(old) = old {
                    // TODO also check end point for proper "t.range includes old.range".
                    if !t.range.contains(old.range.start()).is_some() {
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
pub struct Continuation<'i, C: CodeLabel> {
    pub code: C,
    pub frame: Call<'i, C>,
    pub state: usize,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Call<'i, C> {
    pub callee: C,
    pub range: Range<'i>,
}

impl<'i, C: fmt::Display> fmt::Display for Call<'i, C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}({}..{})",
            self.callee,
            self.range.start(),
            self.range.end()
        )
    }
}

impl<'i, C: PartialOrd> PartialOrd for Call<'i, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (Reverse(self.range), &self.callee).partial_cmp(&(Reverse(other.range), &other.callee))
    }
}

impl<'i, C: Ord> Ord for Call<'i, C> {
    fn cmp(&self, other: &Self) -> Ordering {
        (Reverse(self.range), &self.callee).cmp(&(Reverse(other.range), &other.callee))
    }
}

pub struct CallNode<'i, C: CodeLabel> {
    returns: BTreeSet<Continuation<'i, C>>,
    lengths: BTreeSet<usize>,
}

impl<'i, C: CodeLabel> CallNode<'i, C> {
    pub fn new() -> Self {
        CallNode {
            returns: BTreeSet::new(),
            lengths: BTreeSet::new(),
        }
    }
}

pub struct CallGraph<'i, C: CodeLabel> {
    pub threads: Threads<'i, C>,
    pub calls: HashMap<Call<'i, C>, CallNode<'i, C>>,
}

impl<'i, C: CodeLabel> CallGraph<'i, C> {
    pub fn print(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph gss {{")?;
        writeln!(out, "    graph [rankdir=RL]")?;
        for (call, node) in &self.calls {
            for next in &node.returns {
                writeln!(
                    out,
                    r#"    "{:?}" -> "{:?}" [label="{:?}"]"#,
                    call, next.frame, next.code
                )?;
            }
        }
        writeln!(out, "}}")
    }
    pub fn results<'a>(
        &'a self,
        call: Call<'i, C>,
    ) -> impl DoubleEndedIterator<Item = Range<'i>> + 'a {
        self.calls.get(&call).into_iter().flat_map(move |node| {
            node.lengths
                .iter()
                .map(move |&len| Range(call.range.split_at(len).0))
        })
    }
    pub fn longest_result(&self, call: Call<'i, C>) -> Option<Range<'i>> {
        self.results(call).rev().next()
    }
    pub fn call(&mut self, call: Call<'i, C>, next: Continuation<'i, C>) {
        let node = self.calls.entry(call).or_insert(CallNode::new());
        if node.returns.insert(next) {
            if node.returns.len() > 1 {
                for &len in &node.lengths {
                    self.threads.spawn(next, Range(call.range.split_at(len).1));
                }
            } else {
                self.threads.spawn(
                    Continuation {
                        code: call.callee,
                        frame: call,
                        state: 0,
                    },
                    call.range,
                );
            }
        }
    }
    pub fn ret(&mut self, call: Call<'i, C>, remaining: Range<'i>) {
        let node = self.calls.entry(call).or_insert(CallNode::new());
        if node
            .lengths
            .insert(call.range.subtract_suffix(remaining).len())
        {
            for &next in &node.returns {
                self.threads.spawn(next, remaining);
            }
        }
    }
}

pub struct ParseGraph<'i, P: ParseNodeKind> {
    pub children: HashMap<ParseNode<'i, P>, BTreeSet<usize>>,
}

impl<'i, P: ParseNodeKind> ParseGraph<'i, P> {
    pub fn add(&mut self, kind: P, range: Range<'i>, child: usize) {
        self.children
            .entry(ParseNode { kind, range })
            .or_insert(BTreeSet::new())
            .insert(child);
    }

    pub fn unary_children<'a>(
        &'a self,
        node: ParseNode<'i, P>,
    ) -> impl Iterator<Item = ParseNode<'i, P>> + 'a {
        let (child0, child1, choice_children) = match node.kind.shape() {
            ParseNodeShape::Alias(kind) => (Some(kind), None, None),
            ParseNodeShape::Choice => (
                None,
                None,
                self.children
                    .get(&node)
                    .map(|children| children.iter().map(|&i| P::from_usize(i))),
            ),
            ParseNodeShape::Opt { none, some } => {
                let has_some = self
                    .children
                    .get(&ParseNode {
                        kind: match some.shape() {
                            // TODO: unpack aliases?
                            ParseNodeShape::Choice | ParseNodeShape::Binary(..) => some,
                            _ => node.kind,
                        },
                        range: node.range,
                    }).map_or(false, |children| !children.is_empty());
                (
                    if node.range.is_empty() {
                        Some(none)
                    } else {
                        None
                    },
                    if has_some { Some(some) } else { None },
                    None,
                )
            }
            shape => unreachable!("unary_children({}): non-unary shape {}", node, shape),
        };
        choice_children
            .into_iter()
            .flatten()
            .chain(child0)
            .chain(child1)
            .map(move |kind| ParseNode {
                kind,
                range: node.range,
            })
    }

    pub fn binary_children<'a>(
        &'a self,
        node: ParseNode<'i, P>,
    ) -> impl Iterator<Item = (ParseNode<'i, P>, ParseNode<'i, P>)> + 'a {
        match node.kind.shape() {
            ParseNodeShape::Binary(left_kind, right_kind) => self
                .children
                .get(&node)
                .into_iter()
                .flatten()
                .map(move |&i| {
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
            shape => unreachable!("binary_children({}): non-binary shape {}", node, shape),
        }
    }

    pub fn print(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph sppf {{")?;
        let mut queue: VecDeque<_> = self.children.keys().cloned().collect();
        let mut seen: BTreeSet<_> = queue.iter().cloned().collect();
        let mut p = 0;
        while let Some(source) = queue.pop_front() {
            let mut enqueue = |child| {
                if seen.insert(child) {
                    queue.push_back(child);
                }
            };
            writeln!(out, "    {:?} [shape=box]", source.to_string())?;
            match source.kind.shape() {
                ParseNodeShape::Opaque => {}

                ParseNodeShape::Alias(_) | ParseNodeShape::Choice | ParseNodeShape::Opt { .. } => {
                    for child in self.unary_children(source) {
                        enqueue(child);
                        writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                        writeln!(out, "    {:?} -> p{}:n", source.to_string(), p)?;
                        writeln!(out, "    p{}:s -> {:?}:n [dir=none]", p, child.to_string())?;
                        p += 1;
                    }
                }

                ParseNodeShape::Binary(..) => {
                    for (left, right) in self.binary_children(source) {
                        enqueue(left);
                        enqueue(right);
                        writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                        writeln!(out, "    {:?} -> p{}:n", source.to_string(), p)?;
                        writeln!(out, "    p{}:sw -> {:?}:n [dir=none]", p, left.to_string())?;
                        writeln!(out, "    p{}:se -> {:?}:n [dir=none]", p, right.to_string())?;
                        p += 1;
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

impl<'i, P: ParseNodeKind> fmt::Display for ParseNode<'i, P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} @ {}..{}",
            self.kind,
            self.range.start(),
            self.range.end()
        )
    }
}

impl<'i, P: ParseNodeKind> fmt::Debug for ParseNode<'i, P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} @ {}..{}",
            self.kind,
            self.range.start(),
            self.range.end()
        )
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ParseNodeShape<P> {
    Opaque,
    Alias(P),
    Choice,
    Opt { none: P, some: P },
    Binary(P, P),
}

impl<P: fmt::Display> fmt::Display for ParseNodeShape<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseNodeShape::Opaque => write!(f, "Opaque"),
            ParseNodeShape::Alias(inner) => write!(f, "Alias({})", inner),
            ParseNodeShape::Choice => write!(f, "Choice"),
            ParseNodeShape::Opt { none, some } => {
                write!(f, "Opt {{ none: {}, some: {} }}", none, some)
            }
            ParseNodeShape::Binary(left, right) => write!(f, "Binary({}, {})", left, right),
        }
    }
}

pub trait ParseNodeKind: fmt::Display + Ord + Hash + Copy + 'static {
    fn shape(self) -> ParseNodeShape<Self>;
    fn from_usize(i: usize) -> Self;
    fn to_usize(self) -> usize;
}

pub trait CodeLabel: fmt::Debug + Ord + Hash + Copy + 'static {}
