use crate::input::{Input, InputMatch, Range};
use crate::proc_macro::{flatten, FlatToken, FlatTokenPat, Span, TokenStream};
use indexing::{proof::Provable, Container, Index, Unknown};
use std::ops;

impl Input for TokenStream {
    type Container = Vec<FlatToken>;
    type Slice = [FlatToken];
    type SourceInfo = ops::Range<Span>;
    type SourceInfoPoint = Span;
    fn to_container(self) -> Self::Container {
        let mut out = vec![];
        flatten(self, &mut out);
        out
    }
    fn slice<'b, 'i>(
        input: &'b Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> &'b Self::Slice {
        &input[range.0]
    }
    fn source_info<'i>(
        input: &Container<'i, Self::Container>,
        range: Range<'i>,
    ) -> Self::SourceInfo {
        // FIXME(eddyb) should be joining up spans, but the API
        // for that is still "semver-exempt" in `proc-macro2`.
        let last = range
            .nonempty()
            .map(|r| r.last().no_proof())
            .unwrap_or(range.past_the_end());
        Self::source_info_point(input, range.first())..Self::source_info_point(input, last)
    }
    fn source_info_point<'i>(
        input: &Container<'i, Self::Container>,
        index: Index<'i, Unknown>,
    ) -> Self::SourceInfoPoint {
        // Try to get as much information as possible.
        let (before, after) = input.split_at(index);
        let before = &input[before];
        let after = &input[after];
        if let Some(first) = after.first() {
            first.span()
        } else if let Some(last) = before.last() {
            // Not correct but we're at the end of the input anyway.
            last.span()
        } else {
            // HACK(eddyb) last resort, make a span up
            // (a better option should exist)
            Span::call_site()
        }
    }
}

impl InputMatch<&'static [FlatTokenPat<&'static str>]> for [FlatToken] {
    fn match_left(&self, &pat: &&[FlatTokenPat<&str>]) -> Option<usize> {
        if self
            .iter()
            .zip(pat)
            .take_while(|(t, p)| t.matches_pat(p))
            .count()
            == pat.len()
        {
            Some(pat.len())
        } else {
            None
        }
    }
    fn match_right(&self, &pat: &&[FlatTokenPat<&str>]) -> Option<usize> {
        if self
            .iter()
            .zip(pat)
            .rev()
            .take_while(|(t, p)| t.matches_pat(p))
            .count()
            == pat.len()
        {
            Some(pat.len())
        } else {
            None
        }
    }
}
