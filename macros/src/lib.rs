#![deny(rust_2018_idioms)]

use proc_macro::TokenStream;
use proc_quote::ToTokens as _;

#[proc_macro]
pub fn scannerless_parser(input: TokenStream) -> TokenStream {
    let cx = gll::grammer::scannerless::Context::new();
    let grammar = gll::parse_grammar(&cx, input.into()).unwrap();
    gll::generate::rust::generate(&cx, &grammar)
        .into_token_stream()
        .into()
}

#[proc_macro]
pub fn proc_macro_parser(input: TokenStream) -> TokenStream {
    let cx = gll::grammer::proc_macro::Context::new();
    let mut grammar = gll::grammer::proc_macro::builtin(&cx);
    grammar.extend(gll::parse_grammar(&cx, input.into()).unwrap());
    gll::generate::rust::generate(&cx, &grammar)
        .into_token_stream()
        .into()
}
