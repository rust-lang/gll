#![deny(unsafe_code)]
#![deny(rust_2018_idioms)]

// NOTE only these two modules can and do contain unsafe code.
#[allow(unsafe_code)]
mod high;
#[allow(unsafe_code)]
mod indexing_str;

#[forbid(unsafe_code)]
pub mod forest;
#[forbid(unsafe_code)]
pub mod generate;
#[forbid(unsafe_code)]
pub mod input;
#[forbid(unsafe_code)]
pub mod parse_node;
#[forbid(unsafe_code)]
pub mod parser;
#[forbid(unsafe_code)]
pub mod proc_macro;
#[forbid(unsafe_code)]
pub mod runtime;
#[forbid(unsafe_code)]
pub mod scannerless;

// HACK(eddyb) this contains impls for types in `proc_macro`, which depend on
// `input`. Those parts of `input` should be moved to `grammer::input`.
#[forbid(unsafe_code)]
mod proc_macro_input;

#[forbid(unsafe_code)]
mod parse_grammar;

pub use parse_grammar::parse_grammar;
