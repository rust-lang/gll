use crate::generate::rust::RustInputPat;
use crate::generate::src::{quotable_to_src, quote, Src, ToSrc};
use crate::grammar::{self, call, eat, MatchesEmpty, MaybeKnown};
use indexing::Container;
pub use proc_macro2::{
    Delimiter, Ident, LexError, Literal, Punct, Spacing, Span, TokenStream, TokenTree,
};
use crate::runtime::{Input, InputMatch, Range};
use crate::scannerless::Pat as SPat;
use std::{ops, str::FromStr};

pub type Grammar = grammar::Grammar<Pat>;

pub fn builtin() -> Grammar {
    let mut g = Grammar::new();

    let ident = eat(Pat(vec![FlatTokenPat::Ident(None)]));
    g.define("IDENT", ident.clone());

    let punct = eat(Pat(vec![FlatTokenPat::Punct {
        ch: None,
        joint: None,
    }]));
    g.define("PUNCT", punct.clone());

    let literal = eat(Pat(vec![FlatTokenPat::Literal]));
    g.define("LITERAL", literal.clone());

    let delim = |c| eat(FlatTokenPat::Delim(c));
    let group = |open, close| delim(open) + call("TOKEN_TREE").repeat_many(None) + delim(close);
    g.define(
        "TOKEN_TREE",
        ident | punct | literal | group('(', ')') | group('[', ']') | group('{', '}'),
    );

    g
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pat(pub Vec<FlatTokenPat<String>>);

impl FromStr for Pat {
    type Err = LexError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Handle lone delimiters first, as they won't lex.
        let mut chars = s.chars();
        if let (Some(ch), None) = (chars.next(), chars.next()) {
            if "()[]{}".contains(ch) {
                return Ok(FlatTokenPat::Delim(ch).into());
            }
        }

        let mut tokens = vec![];
        flatten(s.parse()?, &mut tokens);
        Ok(Pat(tokens.into_iter().map(|tt| tt.extract_pat()).collect()))
    }
}

impl From<FlatTokenPat<String>> for Pat {
    fn from(pat: FlatTokenPat<String>) -> Self {
        Pat(vec![pat])
    }
}

impl From<SPat> for Pat {
    fn from(pat: SPat) -> Self {
        match pat {
            SPat::String(s) => s.parse().unwrap(),
            SPat::Range(..) => unimplemented!("char ranges are unsupported"),
        }
    }
}

impl MatchesEmpty for Pat {
    fn matches_empty(&self) -> MaybeKnown<bool> {
        MaybeKnown::Known(self.0.is_empty())
    }
}

impl RustInputPat for Pat {
    fn rust_slice_ty() -> Src {
        quote!([crate::gll::proc_macro::FlatToken])
    }
    fn rust_matcher(&self) -> Src {
        let pats = self.0.iter();
        quote!(&[#(#pats),*])
    }
}

pub enum FlatToken {
    Delim(char, Span),
    Ident(Ident),
    Punct(Punct),
    Literal(Literal),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FlatTokenPat<S: AsRef<str>> {
    Delim(char),
    Ident(Option<S>),
    Punct {
        ch: Option<char>,
        joint: Option<bool>,
    },
    Literal,
}

impl ToSrc for FlatTokenPat<String> {
    fn to_src(&self) -> Src {
        let variant = match self {
            FlatTokenPat::Delim(c) => quote!(Delim(#c)),
            FlatTokenPat::Ident(s) => {
                let s = s
                    .as_ref()
                    .map_or_else(|| quote!(None), |x| quote!(Some(#x)));
                quote!(Ident(#s))
            }
            FlatTokenPat::Punct { ch, joint } => {
                let ch = ch.map_or_else(|| quote!(None), |x| quote!(Some(#x)));
                let joint = joint.map_or_else(|| quote!(None), |x| quote!(Some(#x)));
                quote!(Punct { ch: #ch, joint: #joint })
            }
            FlatTokenPat::Literal => quote!(Literal),
        };
        quote!(crate::gll::proc_macro::FlatTokenPat::#variant)
    }
}
quotable_to_src!(FlatTokenPat<String>);

impl FlatToken {
    pub fn span(&self) -> Span {
        match self {
            &FlatToken::Delim(_, span) => span,
            FlatToken::Ident(tt) => tt.span(),
            FlatToken::Punct(tt) => tt.span(),
            FlatToken::Literal(tt) => tt.span(),
        }
    }

    pub fn extract_pat(&self) -> FlatTokenPat<String> {
        match self {
            &FlatToken::Delim(delim, _) => FlatTokenPat::Delim(delim),
            FlatToken::Ident(tt) => FlatTokenPat::Ident(Some(tt.to_string())),
            FlatToken::Punct(tt) => FlatTokenPat::Punct {
                ch: Some(tt.as_char()),
                joint: if tt.spacing() == Spacing::Joint {
                    Some(true)
                } else {
                    None
                },
            },
            FlatToken::Literal(tt) => {
                unimplemented!(
                    "matching specific literals is not supported, \
                     use `LITERAL` instead of `{}`",
                    tt.to_string(),
                );
            }
        }
    }

    pub fn matches_pat(&self, pat: &FlatTokenPat<impl AsRef<str>>) -> bool {
        match (self, pat) {
            (FlatToken::Delim(a, _), FlatTokenPat::Delim(b)) => a == b,
            (FlatToken::Ident(_), FlatTokenPat::Ident(None)) => true,
            (FlatToken::Ident(a), FlatTokenPat::Ident(Some(b))) => a == b.as_ref(),
            (FlatToken::Punct(a), FlatTokenPat::Punct { ch, joint }) => {
                ch.map_or(true, |b| a.as_char() == b)
                    && joint.map_or(true, |b| (a.spacing() == Spacing::Joint) == b)
            }
            (FlatToken::Literal(_), FlatTokenPat::Literal) => true,
            _ => false,
        }
    }
}

fn flatten(stream: TokenStream, out: &mut Vec<FlatToken>) {
    for tt in stream {
        let flat = match tt {
            TokenTree::Group(tt) => {
                let delim = tt.delimiter();
                // FIXME(eddyb) use proper delim span here.
                let span = tt.span();
                let stream = tt.stream();
                let (open, close) = match delim {
                    Delimiter::Parenthesis => ('(', ')'),
                    Delimiter::Brace => ('{', '}'),
                    Delimiter::Bracket => ('[', ']'),
                    Delimiter::None => {
                        // FIXME(eddyb) maybe encode implicit delimiters somehow?
                        // One way could be to have an opaque `FlatToken` variant,
                        // containing the entire group, instead of exposing its contents.
                        flatten(stream, out);
                        continue;
                    }
                };
                out.push(FlatToken::Delim(open, span));
                flatten(stream, out);
                FlatToken::Delim(close, span)
            }
            TokenTree::Ident(tt) => FlatToken::Ident(tt),
            TokenTree::Punct(tt) => FlatToken::Punct(tt),
            TokenTree::Literal(tt) => FlatToken::Literal(tt),
        };
        out.push(flat);
    }
}

impl Input for TokenStream {
    type Container = Vec<FlatToken>;
    type Slice = [FlatToken];
    type SourceInfo = ops::Range<Span>;
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
        // Try to get as much information as possible.
        let (before_start, after_start, _) = input.range().split_at(range.start());
        let before_start = &input[before_start];
        let after_start = &input[after_start];
        if let Some(first) = after_start.first() {
            // FIXME(eddyb) should be joining up spans, but the API
            // for that is still "semver-exempt" in `proc-macro2`.
            first.span()..input[range.0].last().unwrap_or(first).span()
        } else if let Some(last) = before_start.last() {
            // Not correct but we're at the end of the input anyway.
            let span = last.span();
            span..span
        } else {
            // HACK(eddyb) last resort, make a span up
            // (a better option should exist)
            let span = Span::call_site();
            span..span
        }
    }
}

impl<'a> InputMatch<&'a [FlatTokenPat<&'a str>]> for [FlatToken] {
    fn match_left(&self, pat: &[FlatTokenPat<&str>]) -> Option<usize> {
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
    fn match_right(&self, pat: &[FlatTokenPat<&str>]) -> Option<usize> {
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
