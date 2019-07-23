#![deny(rust_2018_idioms)]

// HACK(eddyb) bootstrap by including a subset of the `gll` crate.
#[path = "src/generate/mod.rs"]
mod generate;

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let cx = grammer::proc_macro::Context::new();
    let mut grammar = grammer::proc_macro::builtin(&cx);
    grammar.extend(grammer::grammar_grammar(&cx));

    fs::write(
        &out_dir.join("parse_grammar.rs"),
        generate::rust::generate(&cx, &grammar).to_rustfmt_or_pretty_string(),
    )
    .unwrap();
}
