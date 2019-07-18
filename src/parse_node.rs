use std::fmt;

// HACK(eddyb) moved here so bootstrap (build.rs) doesn't need
// to include the runtime.

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ParseNodeShape<P> {
    Opaque,
    Alias(P),
    Choice,
    Opt(P),
    Split(P, P),
}

impl<P: fmt::Display> fmt::Display for ParseNodeShape<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseNodeShape::Opaque => write!(f, "Opaque"),
            ParseNodeShape::Alias(inner) => write!(f, "Alias({})", inner),
            ParseNodeShape::Choice => write!(f, "Choice"),
            ParseNodeShape::Opt(inner) => write!(f, "Opt({})", inner),
            ParseNodeShape::Split(left, right) => write!(f, "Split({}, {})", left, right),
        }
    }
}

impl<P> ParseNodeShape<P> {
    pub fn map<Q>(self, mut f: impl FnMut(P) -> Q) -> ParseNodeShape<Q> {
        match self {
            ParseNodeShape::Opaque => ParseNodeShape::Opaque,
            ParseNodeShape::Alias(inner) => ParseNodeShape::Alias(f(inner)),
            ParseNodeShape::Choice => ParseNodeShape::Choice,
            ParseNodeShape::Opt(inner) => ParseNodeShape::Opt(f(inner)),
            ParseNodeShape::Split(left, right) => ParseNodeShape::Split(f(left), f(right)),
        }
    }
}
