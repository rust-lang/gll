#![deny(unsafe_code)]

extern crate indexing;
extern crate ordermap;
extern crate proc_macro2;
extern crate proc_quote;

// NOTE only this module can and does contain unsafe code.
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

// HACK(eddyb) needed for bootstrapping `parse_grammar`.
mod gll {
    pub(crate) use runtime;
}
#[forbid(unsafe_code)]
mod parse_grammar;
