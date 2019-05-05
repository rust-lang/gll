#![deny(unsafe_code)]
#![deny(rust_2018_idioms)]

// NOTE only these two modules can and do contain unsafe code.
#[allow(unsafe_code)]
mod high;
#[allow(unsafe_code)]
mod indexing_str;

#[forbid(unsafe_code)]
pub mod generate;
#[forbid(unsafe_code)]
pub mod grammar;
#[forbid(unsafe_code)]
pub mod proc_macro;
#[forbid(unsafe_code)]
pub mod runtime;
#[forbid(unsafe_code)]
pub mod scannerless;

#[forbid(unsafe_code)]
mod parse_grammar;
