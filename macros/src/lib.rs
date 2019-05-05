#![deny(rust_2018_idioms)]

extern crate proc_macro;

use proc_macro::TokenStream;
use proc_quote::ToTokens as _;

#[proc_macro]
pub fn scannerless_parser(input: TokenStream) -> TokenStream {
    // FIXME(eddyb) parse the `proc_macro` tokens instead of strings.
    input
        .to_string()
        .parse::<gll::scannerless::Grammar>()
        .unwrap()
        .generate_rust()
        .into_token_stream()
        .into()
}

#[proc_macro]
pub fn proc_macro_parser(input: TokenStream) -> TokenStream {
    // FIXME(eddyb) parse the `proc_macro` tokens instead of strings.
    let mut grammar = gll::proc_macro::builtin();
    grammar.extend(input.to_string().parse().unwrap());
    grammar.generate_rust().into_token_stream().into()
}
