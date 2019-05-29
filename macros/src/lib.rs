#![deny(rust_2018_idioms)]

extern crate proc_macro;

use proc_macro::TokenStream;
use proc_quote::ToTokens as _;

#[proc_macro]
pub fn scannerless_parser(input: TokenStream) -> TokenStream {
    let mut cx = gll::scannerless::Context::new();
    let grammar = gll::parse_grammar(&mut cx, input.into()).unwrap();
    gll::generate::rust::generate(&mut cx, &grammar)
        .into_token_stream()
        .into()
}

#[proc_macro]
pub fn proc_macro_parser(input: TokenStream) -> TokenStream {
    let mut cx = gll::proc_macro::Context::new();
    let mut grammar = gll::proc_macro::builtin(&mut cx);
    grammar.extend(gll::parse_grammar(&mut cx, input.into()).unwrap());
    gll::generate::rust::generate(&mut cx, &grammar)
        .into_token_stream()
        .into()
}
