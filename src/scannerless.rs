use grammar::{MatchesEmpty, MaybeKnown};
use std::char;
use std::convert::TryFrom;
use std::ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

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
