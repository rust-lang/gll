#![forbid(unsafe_code)]
#![deny(rust_2018_idioms)]

/// Reexport of the `grammer` crate.
///
/// Primarily used by the generated code, to avoid requiring
/// an explicit dependency on both `gll` and `grammer`.
pub use grammer;

pub mod generate;
pub mod runtime;

mod parse_grammar;

pub use parse_grammar::parse_grammar;
