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

extern crate indexing;
extern crate ordermap;

pub mod generate;
pub mod grammar;
pub mod runtime;
