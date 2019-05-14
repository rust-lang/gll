use crate::indexing_str;
use indexing::container_traits::Trustworthy;
use indexing::{self, Container, Index, Unknown};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
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
