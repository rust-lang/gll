#![feature(
    arbitrary_self_types,
    decl_macro,
    fn_traits,
    nll,
    range_contains,
    slice_patterns,
    str_escape,
    try_from,
    unboxed_closures
)]
// HACK(eddyb) needed for bootstrapping `parse_grammar`.
#![feature(generators, generator_trait)]

extern crate indexing;
extern crate ordermap;

pub mod generate;
pub mod grammar;
pub mod runtime;
pub mod scannerless;

// HACK(eddyb) needed for bootstrapping `parse_grammar`.
mod gll {
    pub(crate) use runtime;
}
mod parse_grammar;
