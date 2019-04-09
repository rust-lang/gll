extern crate indexing;
extern crate ordermap;
extern crate proc_macro2;
extern crate proc_quote;

pub mod generate;
pub mod grammar;
pub mod proc_macro;
pub mod runtime;
pub mod scannerless;

// HACK(eddyb) needed for bootstrapping `parse_grammar`.
mod gll {
    pub(crate) use runtime;
}
mod parse_grammar;
