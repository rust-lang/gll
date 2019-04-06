# GLL parsing framework

[![Build Status](https://travis-ci.com/rust-lang/gll.svg?branch=master)](https://travis-ci.com/rust-lang/gll)
[![Latest Version](https://img.shields.io/crates/v/gll.svg)](https://crates.io/crates/gll)
[![Rust Documentation](https://img.shields.io/badge/api-rustdoc-blue.svg)](https://docs.rs/gll)

## Usage

Easiest way to get started is through `gll-macros`:
```toml
[dependencies]
gll = "0.0.2"
gll-macros = "0.0.2"
proc-macro2 = "0.4.20"
```
```rust
extern crate gll;
extern crate gll_macros;
extern crate proc_macro2;
```

As an example, this is what you might write for a JSON-like syntax,
that uses plain identifiers instead of string literals for field names,
and allows values to be parenthesized Rust expressions:
```rust
mod json_like {
    ::gll_macros::proc_macro_parser! {
        Value =
            | Null:"null"
            | False:"false"
            | True:"true"
            | Literal:LITERAL
            | Array:{ "[" elems:Value* % "," "]" }
            | Object:{ "{" fields:Field* % "," "}" }
            | InterpolateRust:{ "(" TOKEN_TREE+ ")" }
            ;
        Field = name:IDENT ":" value:Value;
    }
}
```
You can also use a build script to generate the parser (**TODO**: document).

To parse a string with that grammar:
```rust
use proc_macro2::TokenStream;

let tokens: TokenStream = string.parse().unwrap();
json_like::Value::parse_with(tokens, |parser, result| {
    let value = result.unwrap();
    // ...
});
```

## Grammar

All grammars contain a set of named rules, with the syntax `Name = rule;`.
(the order between the rules doesn't matter)

Rules are made out of:
* **grouping**, using `{...}`
* **string literals**, matching input characters / tokens exactly
* **character ranges**: `'a'..='d'` is equivalent to `"a"|"b"|"c"|"d"`
  * only in scannerless mode
* **builtin rules**: `IDENT`, `PUNCT`, `LITERAL`, `TOKEN_TREE`
  * only in proc macro mode
* **named rules**, referred to by their name
* **concatenation**: `A B` - "`A` followed by `B`"
* **alternation**: `A | B` - "either `A` or `B`"
* **optionals**: `A?` - "either `A` or nothing"
* **lists**: `A*` - "zero or more `A`s", `A+` - "one or more `A`s"
  * optional separator: `A* % ","` - "comma-separated `A`s"

Parts of a rule can be labeled with **field names**, to allow later access to them:

`LetDecl = "let" pat:Pat { "=" init:Expr }? ";";` produces:
```rust
// Note: generic parameters omitted for brevity.
struct LetDecl {
    pat: Handle<Pat>,
    init: Option<Handle<Expr>>,
}
```
One Rust-specific convention is that alternation fields are enum variants.

`Expr = Lit:LITERAL | Add:{ a:Expr "+" b:Expr };` produces:
```rust
enum Expr {
    Lit(Handle<LITERAL>),
    Add {
        a: Handle<Expr>,
        b: Handle<Expr>,
    },
}
```

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
