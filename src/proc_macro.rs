use crate::generate::rust::RustInputPat;
use crate::generate::src::{quote, Src};
use crate::scannerless::Pat as SPat;
use grammer::rule::{call, eat, MatchesEmpty, MaybeKnown};
pub use proc_macro2::{
    Delimiter, Ident, LexError, Literal, Punct, Spacing, Span, TokenStream, TokenTree,
};
use std::str::FromStr;

pub type Context = grammer::context::Context<Pat>;

pub fn builtin(cx: &mut Context) -> grammer::Grammar {
    let mut g = grammer::Grammar::new();

    let ident = eat(Pat(vec![FlatTokenPat::Ident(None)])).finish(cx);
    g.define(cx.intern("IDENT"), ident.clone());

    g.define(
        cx.intern("LIFETIME"),
        eat(Pat(vec![
            FlatTokenPat::Punct {
                ch: Some('\''),
                joint: Some(true),
            },
            FlatTokenPat::Ident(None),
        ]))
        .finish(cx),
    );

    let punct = eat(Pat(vec![FlatTokenPat::Punct {
        ch: None,
        joint: None,
    }]))
    .finish(cx);
    g.define(cx.intern("PUNCT"), punct.clone());

    let literal = eat(Pat(vec![FlatTokenPat::Literal])).finish(cx);
    g.define(cx.intern("LITERAL"), literal.clone());

    let delim = |c| eat(FlatTokenPat::Delim(c));
    let group = |open, close| delim(open) + call("TOKEN_TREE").repeat_many() + delim(close);
    g.define(
        cx.intern("TOKEN_TREE"),
        (ident | punct | literal | group('(', ')') | group('[', ']') | group('{', '}')).finish(cx),
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

// FIXME(eddyb) perhaps support `TryFrom`/`TryInto` directly in `grammer`?
impl From<&str> for Pat {
    fn from(s: &str) -> Self {
        s.parse().unwrap()
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
            SPat::String(s) => s[..].into(),
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
        quote!([gll::proc_macro::FlatToken])
    }
    fn rust_matcher(&self) -> Src {
        let pats_src = self.0.iter().map(|pat| pat.to_src());
        quote!(&[#(#pats_src),*] as &[_])
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

impl FlatTokenPat<String> {
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
        quote!(gll::proc_macro::FlatTokenPat::#variant)
    }
}

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

pub(crate) fn flatten(stream: TokenStream, out: &mut Vec<FlatToken>) {
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
