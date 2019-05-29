#![deny(rust_2018_idioms)]

// HACK(eddyb) bootstrap by including a subset of the `gll` crate.
#[path = "src/generate/mod.rs"]
mod generate;
#[path = "src/parse_node.rs"]
mod parse_node;
#[path = "src/proc_macro.rs"]
pub mod proc_macro;
#[path = "src/scannerless.rs"]
pub mod scannerless;

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let mut cx = proc_macro::Context::new();
    let mut grammar = proc_macro::builtin(&mut cx);
    grammar.extend(grammer::grammar_grammar(&mut cx));

    fs::write(
        &out_dir.join("parse_grammar.rs"),
        generate::rust::generate(&mut cx, &grammar).to_rustfmt_or_pretty_string(),
    )
    .unwrap();
}
