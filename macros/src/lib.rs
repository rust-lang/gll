extern crate gll;
extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro]
pub fn scannerless_parser(input: TokenStream) -> TokenStream {
    // FIXME(eddyb) parse the `proc_macro` tokens instead of strings.
    // Also, avoid running `rustfmt` here, it's wasteful and unnecessary.
    input
        .to_string()
        .parse::<gll::grammar::Grammar<gll::scannerless::Pat<String, char>>>()
        .unwrap()
        .generate_rust()
        .parse()
        .unwrap()
}
