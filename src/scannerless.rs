use grammer::{self, MatchesEmpty, MaybeKnown};
use std::char;
use std::ops::{self, Bound, RangeBounds};

// HACK(eddyb) we want e.g. `.parse::<scannerless::Grammar>()` to keep working,
// but `Grammar` comes from the `grammer` crate now - so we wrap it in order to
// implement `FromStr` on the wrapper and use `Deref` to make it more seamless.
// Also, it's here, and not in `parse_grammar`, so it exists during bootstrap.
pub struct WrapperHack<T>(pub T);

impl<T> std::ops::Deref for WrapperHack<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> std::ops::DerefMut for WrapperHack<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

pub type Grammar<S = String> = WrapperHack<grammer::Grammar<Pat<S>>>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Pat<S = String, C = char> {
    String(S),
    Range(C, C),
}

impl<'a, C> From<&'a str> for Pat<&'a str, C> {
    fn from(s: &'a str) -> Self {
        Pat::String(s)
    }
}

impl<C> From<&str> for Pat<String, C> {
    fn from(s: &str) -> Self {
        Pat::String(s.to_string())
    }
}

impl<C> From<String> for Pat<String, C> {
    fn from(s: String) -> Self {
        Pat::String(s)
    }
}

// HACK(eddyb) this should be generic over `RangeBounds<char>`,
// but that errors with: "upstream crates may add new impl of trait
// `std::ops::RangeBounds<char>` for type `&str` in future versions"
impl<'a, S> From<(Bound<&'a char>, Bound<&'a char>)> for Pat<S> {
    fn from(range: (Bound<&char>, Bound<&char>)) -> Self {
        let start = match range.start_bound() {
            Bound::Included(&c) => c,
            Bound::Excluded(&c) => {
                char::from_u32(c as u32 + 1).expect("excluded lower char bound too high")
            }
            Bound::Unbounded => '\0',
        };
        let end = match range.end_bound() {
            Bound::Included(&c) => c,
            Bound::Excluded(&c) => {
                char::from_u32(c as u32 - 1).expect("excluded upper char bound too low")
            }
            Bound::Unbounded => char::MAX,
        };
        Pat::Range(start, end)
    }
}

macro_rules! range_impls {
    ($($ty:ty),*) => {
        $(impl<S> From<$ty> for Pat<S> {
            fn from(range: $ty) -> Self {
                Self::from((range.start_bound(), range.end_bound()))
            }
        })*
    }
}
range_impls! {
    (Bound<char>, Bound<char>),
    ops::RangeTo<char>,
    ops::Range<char>,
    ops::RangeInclusive<char>,
    ops::RangeFull,
    ops::RangeFrom<char>,
    ops::RangeToInclusive<char>
}

impl<S: AsRef<str>> MatchesEmpty for Pat<S> {
    fn matches_empty(&self) -> MaybeKnown<bool> {
        MaybeKnown::Known(match self {
            Pat::String(s) => s.as_ref().is_empty(),
            Pat::Range(..) => false,
        })
    }
}
