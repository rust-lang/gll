#![deny(rust_2018_idioms)]

extern crate proc_macro;

use proc_macro::TokenStream;
use proc_quote::ToTokens as _;

#[proc_macro]
pub fn scannerless_parser(input: TokenStream) -> TokenStream {
    let grammar: gll::scannerless::Grammar = gll::parse_grammar(input.into()).unwrap();
    gll::generate::rust::generate(&grammar)
        .into_token_stream()
        .into()
}

#[proc_macro]
pub fn proc_macro_parser(input: TokenStream) -> TokenStream {
    let mut grammar = gll::proc_macro::builtin();
    grammar.extend(gll::parse_grammar(input.into()).unwrap());
    gll::generate::rust::generate(&grammar)
        .into_token_stream()
        .into()
}
