pub use grammar::ParseNodeShape;

use indexing::container_traits::{Contiguous, Trustworthy};
use indexing::{self, scope, Container};
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

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct LineColumn {
    pub line: usize,
    pub column: usize,
}

impl fmt::Debug for LineColumn {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", 1 + self.line, 1 + self.column)
    }
}

impl LineColumn {
    fn count(prefix: &str) -> Self {
        let (line, column) = prefix
            .split("\n")
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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}-{:?}", self.start, self.end)
    }
}

pub struct Str(str);

impl<'a> From<&'a str> for &'a Str {
    fn from(s: &'a str) -> Self {
        unsafe { &*(s as *const str as *const Str) }
    }
}

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

pub trait Input: Sized {
    type Container: Trustworthy;
    type Slice: ?Sized;
    type SourceInfo: fmt::Debug;
    fn to_container(self) -> Self::Container;
    fn slice<'a, 'i>(
        input: &'a Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> &'a Self::Slice;
    fn source_info<'i>(
        input: &Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> Self::SourceInfo;
}

impl<'a, T> Input for &'a [T] {
    type Container = Self;
    type Slice = [T];
    type SourceInfo = ops::Range<usize>;
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
}

impl<'a> Input for &'a str {
    type Container = &'a Str;
    type Slice = str;
    type SourceInfo = LineColumnRange;
    fn to_container(self) -> Self::Container {
        self.into()
    }
    fn slice<'b, 'i>(
        input: &'b Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> &'b Self::Slice {
        unsafe { str::from_utf8_unchecked(&input[range.0]) }
    }
    fn source_info<'i>(
        input: &Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> Self::SourceInfo {
        let prefix_range = Range(input.range().split_at(range.start()).0);
        let start = LineColumn::count(Self::slice(input, prefix_range));
        // HACK(eddyb) add up `LineColumn`s to avoid counting twice.
        // Ideally we'd cache around a line map, like rustc's `SourceMap`.
        let mut end = LineColumn::count(Self::slice(input, range));
        end.line += start.line;
        if end.line == start.line {
            end.column += start.column;
        }
        LineColumnRange { start, end }
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

pub struct Parser<'i, P: ParseNodeKind, C: CodeLabel, I: Input> {
    input: Container<'i, I::Container>,
    pub threads: Threads<'i, C>,
    pub gss: GraphStack<'i, C>,
    pub memoizer: Memoizer<'i, C>,
    pub sppf: ParseForest<'i, P>,
}

impl<'i, P: ParseNodeKind, C: CodeLabel, I: Input> Parser<'i, P, C, I> {
    pub fn with<R>(input: I, f: impl for<'i2> FnOnce(Parser<'i2, P, C, I>, Range<'i2>) -> R) -> R {
        scope(input.to_container(), |input| {
            let range = input.range();
            f(
                Parser {
                    input,
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
                    sppf: ParseForest {
                        possibilities: HashMap::new(),
                    },
                },
                Range(range),
            )
        })
    }
    pub fn input(&self, range: Range<'i>) -> &I::Slice {
        I::slice(&self.input, range)
    }
    pub fn source_info(&self, range: Range<'i>) -> I::SourceInfo {
        I::source_info(&self.input, range)
    }
    pub fn input_consume_left<Pat>(&self, range: Range<'i>, pat: Pat) -> Option<Range<'i>>
    where
        I::Slice: InputMatch<Pat>,
    {
        self.input(range)
            .match_left(pat)
            .map(|n| Range(range.split_at(n).1))
    }
    pub fn input_consume_right<Pat>(&self, range: Range<'i>, pat: Pat) -> Option<Range<'i>>
    where
        I::Slice: InputMatch<Pat>,
    {
        self.input(range)
            .match_right(pat)
            .map(|n| Range(range.split_at(range.len() - n).0))
    }
    pub fn call(&mut self, call: Call<'i, C>, next: Continuation<'i, C>) {
        let returns = self.gss.returns.entry(call).or_default();
        if returns.insert(next) {
            if returns.len() > 1 {
                if let Some(lengths) = self.memoizer.lengths.get(&call) {
                    for &len in lengths {
                        self.threads.spawn(next, Range(call.range.split_at(len).1));
                    }
                }
            } else {
                self.threads.spawn(
                    Continuation {
                        code: call.callee,
                        fn_input: call.range,
                        state: 0,
                    },
                    call.range,
                );
            }
        }
    }
    pub fn ret(&mut self, from: Continuation<'i, C>, remaining: Range<'i>) {
        let call = Call {
            callee: from.code.enclosing_fn(),
            range: from.fn_input,
        };
        if self
            .memoizer
            .lengths
            .entry(call)
            .or_default()
            .insert(call.range.subtract_suffix(remaining).len())
        {
            if let Some(returns) = self.gss.returns.get(&call) {
                for &next in returns {
                    self.threads.spawn(next, remaining);
                }
            }
        }
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
    pub fn_input: Range<'i>,
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

pub struct GraphStack<'i, C: CodeLabel> {
    returns: HashMap<Call<'i, C>, BTreeSet<Continuation<'i, C>>>,
}

impl<'i, C: CodeLabel> GraphStack<'i, C> {
    pub fn dump_graphviz(&self, out: &mut Write) -> io::Result<()> {
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
                        range: next.fn_input
                    },
                    next.code
                )?;
            }
        }
        writeln!(out, "}}")
    }
}

pub struct Memoizer<'i, C: CodeLabel> {
    lengths: HashMap<Call<'i, C>, BTreeSet<usize>>,
}

impl<'i, C: CodeLabel> Memoizer<'i, C> {
    pub fn results<'a>(
        &'a self,
        call: Call<'i, C>,
    ) -> impl DoubleEndedIterator<Item = Range<'i>> + 'a {
        self.lengths
            .get(&call)
            .into_iter()
            .flat_map(move |lengths| {
                lengths
                    .iter()
                    .map(move |&len| Range(call.range.split_at(len).0))
            })
    }
    pub fn longest_result(&self, call: Call<'i, C>) -> Option<Range<'i>> {
        self.results(call).rev().next()
    }
}

pub struct ParseForest<'i, P: ParseNodeKind> {
    pub possibilities: HashMap<ParseNode<'i, P>, BTreeSet<usize>>,
}

impl<'i, P: ParseNodeKind> ParseForest<'i, P> {
    pub fn add(&mut self, kind: P, range: Range<'i>, possibility: usize) {
        self.possibilities
            .entry(ParseNode { kind, range })
            .or_default()
            .insert(possibility);
    }

    pub fn all_choices<'a>(
        &'a self,
        node: ParseNode<'i, P>,
    ) -> impl Iterator<Item = ParseNode<'i, P>> + 'a {
        match node.kind.shape() {
            ParseNodeShape::Choice => self
                .possibilities
                .get(&node)
                .into_iter()
                .flatten()
                .cloned()
                .map(move |i| ParseNode {
                    kind: P::from_usize(i),
                    range: node.range,
                }),
            shape => unreachable!("all_choices({}): non-choice shape {}", node, shape),
        }
    }

    pub fn all_splits<'a>(
        &'a self,
        node: ParseNode<'i, P>,
    ) -> impl Iterator<Item = (ParseNode<'i, P>, ParseNode<'i, P>)> + 'a {
        match node.kind.shape() {
            ParseNodeShape::Split(left_kind, right_kind) => self
                .possibilities
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

    pub fn dump_graphviz(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph sppf {{")?;
        let mut queue: VecDeque<_> = self.possibilities.keys().cloned().collect();
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

impl<'i, P: ParseNodeKind> ParseNode<'i, P> {
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

pub trait ParseNodeKind: fmt::Display + Ord + Hash + Copy + 'static {
    fn shape(self) -> ParseNodeShape<Self>;
    fn from_usize(i: usize) -> Self;
    fn to_usize(self) -> usize;
}

pub trait CodeLabel: fmt::Debug + Ord + Hash + Copy + 'static {
    fn enclosing_fn(self) -> Self;
}

pub macro traverse {
    (typeof($leaf:ty) _) => { $leaf },
    (typeof($leaf:ty) ?) => { Option<traverse!(typeof($leaf) _)> },
    (typeof($leaf:ty) ($l_shape:tt, $r_shape:tt)) => { (traverse!(typeof($leaf) $l_shape), traverse!(typeof($leaf) $r_shape)) },
    (typeof($leaf:ty) { $($i:tt: $kind:pat => $shape:tt,)* }) => { ($(traverse!(typeof($leaf) $shape),)*) },
    (typeof($leaf:ty) [$shape:tt]) => { (traverse!(typeof($leaf) $shape),) },

    ($sppf:ident, $node:ident, _, $result:pat => $cont:expr) => {
        match $node { $result => $cont }
    },
    ($sppf:ident, $node:ident, ?, $result:pat => $cont:expr) => {
        match Some($node) { $result => $cont }
    },
    ($sppf:ident, $node:ident, ($l_shape:tt, $r_shape:tt), $result:pat => $cont:expr) => {
        for (left, right) in $sppf.all_splits($node) {
            traverse!($sppf, left, $l_shape, left =>
               traverse!($sppf, right, $r_shape, right => match (left, right) { $result => $cont }))
        }
    },
    ($sppf:ident, $node:ident, { $($i:tt: $kind:pat => $shape:tt,)* }, $result:pat => $cont:expr) => {
        for node in $sppf.all_choices($node) {
            let tuple_template = <($(traverse!(typeof(_) $shape),)*)>::default();
            match node.kind {
                $($kind => traverse!($sppf, node, $shape, x => {
                    let mut r = tuple_template;
                    r.$i = x;
                    match r { $result => $cont }
                }),)*
                _ => unreachable!(),
            }
        }
    },
    ($sppf:ident, $node:ident, [$shape:tt], $result:pat => $cont:expr) => {
        {
            let tuple_template = <(traverse!(typeof(_) $shape),)>::default();
            match $node.unpack_opt() {
                Some(node) => {
                    traverse!($sppf, node, $shape, x => {
                        let mut r = tuple_template;
                        r.0 = x;
                        match r { $result => $cont }
                    })
                }
                None => {
                    match tuple_template { $result => $cont }
                }
            }
        }
    }
}
