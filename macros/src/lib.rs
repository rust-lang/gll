extern crate gll;
extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro]
pub fn scannerless_parser(input: TokenStream) -> TokenStream {
    // FIXME(eddyb) parse the `proc_macro` tokens instead of strings.
    // Also, avoid running `rustfmt` here, it's wasteful and unnecessary.
    input
        .to_string()
        .parse::<gll::scannerless::Grammar>()
        .unwrap()
        .generate_rust()
        .parse()
        .unwrap()
}

#[proc_macro]
pub fn proc_macro_parser(input: TokenStream) -> TokenStream {
    // FIXME(eddyb) parse the `proc_macro` tokens instead of strings.
    // Also, avoid running `rustfmt` here, it's wasteful and unnecessary.
    let mut grammar = gll::proc_macro::builtin();
    grammar.extend(input.to_string().parse().unwrap());
    grammar.generate_rust().parse().unwrap()
}
