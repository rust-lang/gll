extern crate gll;
extern crate proc_macro;

use gll::generate::rust::Options;
use proc_macro::TokenStream;

fn options() -> Options {
    let mut options = Options::default();
    options.no_macros = true;
    options
}

#[proc_macro]
pub fn scannerless_parser(input: TokenStream) -> TokenStream {
    // FIXME(eddyb) parse the `proc_macro` tokens instead of strings.
    // Also, avoid running `rustfmt` here, it's wasteful and unnecessary.
    input
        .to_string()
        .parse::<gll::scannerless::Grammar>()
        .unwrap()
        .generate_rust_with_options(options())
        .parse()
        .unwrap()
}

#[proc_macro]
pub fn proc_macro_parser(input: TokenStream) -> TokenStream {
    // FIXME(eddyb) parse the `proc_macro` tokens instead of strings.
    // Also, avoid running `rustfmt` here, it's wasteful and unnecessary.
    let mut grammar = gll::proc_macro::builtin();
    grammar.extend(input.to_string().parse().unwrap());
    grammar
        .generate_rust_with_options(options())
        .parse()
        .unwrap()
}
