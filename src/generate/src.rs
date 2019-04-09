use proc_macro2::{Delimiter, Ident, LexError, Literal, Spacing, Span, TokenStream, TokenTree};
use proc_quote::ToTokens;
use std::fmt;
use std::io::Write;
use std::mem;
use std::ops::{Add, AddAssign};
use std::process::{Command, Stdio};
use std::str::FromStr;

/// Abstracted representation of (generated) "source code",
/// using `proc-macro2` tokens and `proc-quote` quasi-quoting,
/// with some conveniences on top (mainly basic pretty-printing).
#[derive(Clone, Default)]
pub struct Src {
    tokens: TokenStream,
}

impl Src {
    pub fn new(x: impl ToTokens) -> Src {
        Src {
            tokens: x.into_token_stream(),
        }
    }

    pub fn ident(name: impl AsRef<str>) -> Src {
        Src::new(Ident::new(name.as_ref(), Span::call_site()))
    }

    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    /// "Pretty"-print the tokens, without whitespace heuristics.
    ///
    /// Note: use `to_pretty_string` (or `to_rustfmt_or_pretty_string`)
    /// instead, if you want the outpu to be somewhat more readable..
    pub fn to_ugly_string(&self) -> String {
        self.tokens.to_string()
    }

    /// Pretty-print the tokens, approximating whitespace
    /// placement as well as possible (without parsing).
    pub fn to_pretty_string(&self) -> String {
        self.pretty_print().to_string()
    }

    /// Pretty-print the tokens (see `to_pretty_string`),
    /// then try to pass them through `rustfmt`.
    /// If `rustfmt` is missing or otherwise errors, the
    /// pretty-printed string will be returned instead.
    pub fn to_rustfmt_or_pretty_string(&self) -> String {
        let pretty = self.to_pretty_string();

        // HACK(eddyb) don't try to feed input to `rustfmt` without
        // knowing that it will at least try to read it.
        // *Somehow* (despite libstd ignoring it) we can get SIGPIPE.
        let has_rustfmt = Command::new("rustfmt")
            .arg("-V")
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .and_then(|child| child.wait_with_output().map(|o| o.status.success()))
            .unwrap_or(false);

        if !has_rustfmt {
            return pretty;
        }

        let rustfmt = Command::new("rustfmt")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn();

        if let Ok(mut rustfmt) = rustfmt {
            let stdin_result = {
                let stdin = rustfmt.stdin.as_mut().unwrap();
                stdin.write_all(pretty.as_bytes())
            };

            if let Ok(output) = rustfmt.wait_with_output() {
                if output.status.success() {
                    stdin_result.unwrap();
                    return String::from_utf8_lossy(&output.stdout).to_string();
                }
            }
        }

        pretty
    }
}

impl FromStr for Src {
    type Err = LexError;

    fn from_str(s: &str) -> Result<Src, LexError> {
        Ok(Src { tokens: s.parse()? })
    }
}

impl AddAssign for Src {
    fn add_assign(&mut self, other: Src) {
        self.tokens.extend(other.tokens);
    }
}

impl Add for Src {
    type Output = Src;
    fn add(mut self, other: Src) -> Src {
        self += other;
        self
    }
}

impl ToTokens for Src {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.tokens.to_tokens(tokens);
    }
    fn into_token_stream(self) -> TokenStream {
        self.tokens
    }
}

pub trait ToSrc {
    fn to_src(&self) -> Src;
}

pub use crate::__generate_src_quotable_to_src as quotable_to_src;
#[macro_export]
macro_rules! __generate_src_quotable_to_src {
    ($ty:ty) => {
        impl ::proc_quote::ToTokens for $ty {
            fn to_tokens(&self, tokens: &mut ::proc_macro2::TokenStream) {
                self.to_src().to_tokens(tokens);
            }
            fn into_token_stream(self) -> ::proc_macro2::TokenStream {
                self.to_src().into_token_stream()
            }
        }
    };
}

pub use crate::__generate_src_quote as quote;
#[macro_export]
macro_rules! __generate_src_quote {
    ($($t:tt)*) => { $crate::generate::src::Src::new(::proc_quote::quote!($($t)*)) };
}

// Pretty-printing support.

#[derive(Clone, Debug)]
enum Elem {
    Char(char, Spacing),
    Ident(Ident),
    Literal(Literal),
}

impl fmt::Display for Elem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Elem::Char(c, _) => c.fmt(f),
            Elem::Ident(i) => i.fmt(f),
            Elem::Literal(l) => l.fmt(f),
        }
    }
}

impl Elem {
    fn try_from_tt(tt: TokenTree) -> Result<Elem, (Delimiter, TokenStream)> {
        Ok(match tt {
            TokenTree::Group(g) => return Err((g.delimiter(), g.stream())),
            TokenTree::Ident(i) => Elem::Ident(i),
            TokenTree::Literal(l) => Elem::Literal(l),
            TokenTree::Punct(p) => Elem::Char(p.as_char(), p.spacing()),
        })
    }

    /// Returns `true` if the `a` and `b` token trees (in the representation
    /// returned by `try_from_tt`) should be printed with no space in between.
    fn should_join(a: &Result<Elem, (Delimiter, TokenStream)>, b: &Result<Elem, (Delimiter, TokenStream)>) -> bool {
        let join_symmetrical = |a: &_, b: &_| match (a, b) {
            (Ok(Elem::Char('.', _)), _) => true,

            // FIXME(eddyb) this only makes sense in type syntax.
            (Ok(Elem::Char('<', _)), _) => true,

            _ => false,
        };
        match (a, b) {
            // This is the only mandatory rule, everything else can return
            // `false` conservatively, and use `true` where safe, to make the
            // output prettier (as much as possible without parsing Rust).
            (Ok(Elem::Char(_, Spacing::Joint)), _) => true,

            (Ok(Elem::Literal(_)), Ok(Elem::Char('.', _))) => false,

            (a, b) | (b, a) if join_symmetrical(a, b) => true,

            (Ok(Elem::Char(':', _)), Ok(Elem::Char(':', _))) => false,

            (_, Err((Delimiter::Parenthesis, _)))
            | (_, Err((Delimiter::Bracket, _)))
            | (_, Ok(Elem::Char(',', _)))
            | (_, Ok(Elem::Char(';', _)))
            | (_, Ok(Elem::Char(':', _)))
            | (_, Ok(Elem::Char('?', _)))
            | (Ok(Elem::Char('.', _)), _)
            | (Ok(Elem::Char('!', _)), _) => true,

            // FIXME(eddyb) these only make sense in type syntax.
            (_, Ok(Elem::Char('>', _))) => true,

            // FIXME(eddyb) this only makes sense when used as an unary operator.
            (Ok(Elem::Char('&', _)), _) => true,

            _ => false,
        }
    }
}

#[derive(Default)]
struct Line {
    indent: usize,
    elems: Vec<Elem>,
}

impl fmt::Display for Line {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for _ in 0..self.indent {
            write!(f, "    ")?;
        }
        for elem in &self.elems {
            elem.fmt(f)?;
        }
        Ok(())
    }
}

#[derive(Default)]
pub struct Fragment {
    before: Vec<Elem>,
    lines: Vec<Line>,
}

impl fmt::Display for Fragment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for elem in &self.before {
            elem.fmt(f)?;
        }
        for line in &self.lines {
            write!(f, "\n{}", line)?;
        }
        Ok(())
    }
}

impl Fragment {
    fn last(&self) -> &[Elem] {
        self.lines.last().map_or(&self.before, |line| &line.elems)
    }

    fn last_mut(&mut self) -> &mut Vec<Elem> {
        self.lines
            .last_mut()
            .map_or(&mut self.before, |line| &mut line.elems)
    }

    fn push(&mut self, elem: Elem) {
        self.last_mut().push(elem);
    }

    fn append(&mut self, other: Fragment) {
        self.last_mut().extend(other.before);
        self.lines.extend(other.lines);
    }
}

impl Src {
    pub fn pretty_print(&self) -> Fragment {
        self.pretty_print_in_group(Delimiter::None)
    }

    fn pretty_print_in_group(&self, outer_delim: Delimiter) -> Fragment {
        let mut frag = Fragment::default();
        let mut prev = None;
        for elem in self.tokens.clone().into_iter().map(Elem::try_from_tt) {
            if let Some(prev) = prev.replace(elem.clone()) {
                if !Elem::should_join(&prev, &elem) {
                    let new_line = match (&prev, &elem) {
                        (Err((Delimiter::Brace, _)), Ok(Elem::Ident(_)))
                        | (Ok(Elem::Char(';', _)), _) => true,
                        (Ok(Elem::Char(',', _)), _) => outer_delim == Delimiter::Brace,
                        _ => false,
                    };
                    if new_line {
                        frag.lines.push(Line::default());
                    } else {
                        if !frag.last().is_empty() {
                            frag.push(Elem::Char(' ', Spacing::Alone));
                        }
                    }
                }
            }
            match elem {
                Err((Delimiter::None, stream)) => {
                    frag.append(Src::new(stream).pretty_print());
                }
                Err((delim, stream)) => {
                    let (open, close) = match delim {
                        Delimiter::Parenthesis => ('(', ')'),
                        Delimiter::Bracket => ('[', ']'),
                        Delimiter::Brace => ('{', '}'),
                        Delimiter::None => unreachable!(),
                    };
                    frag.push(Elem::Char(open, Spacing::Alone));

                    let mut inner = Src::new(stream).pretty_print_in_group(delim);

                    // Turn `{a\n  b\n  ...}` into `{\n  a\n  b\n  ...\n}`,
                    // and also `(...)` and `[...]`, but only if multi-line.
                    if delim == Delimiter::Brace || !inner.lines.is_empty() {
                        if !inner.before.is_empty() {
                            inner.lines.insert(
                                0,
                                Line {
                                    indent: 0,
                                    elems: mem::replace(&mut inner.before, vec![]),
                                },
                            );
                        }
                    }
                    for line in &mut inner.lines {
                        line.indent += 1;
                    }
                    if !inner.lines.is_empty() {
                        inner.lines.push(Line::default());
                    }
                    frag.append(inner);

                    frag.push(Elem::Char(close, Spacing::Alone));
                }
                Ok(elem) => frag.push(elem),
            }
        }
        frag
    }
}
