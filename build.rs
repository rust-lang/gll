extern crate grammer;
extern crate indexing;
extern crate ordermap;
extern crate proc_macro2;
extern crate proc_quote;

// HACK(eddyb) bootstrap by including a subset of the `gll` crate.
#[path = "src/generate/mod.rs"]
mod generate;
#[path = "src/parse_node.rs"]
mod parse_node;
#[path = "src/scannerless.rs"]
pub mod scannerless;

use std::env;
use std::fs;
use std::path::PathBuf;

// FIXME(eddyb) use `scannerless::Grammar` when that wrapper hack is fixed.
type Grammar = grammer::Grammar<scannerless::Pat<&'static str>>;
fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let grammar: Grammar = grammer::grammar_grammar();

    fs::write(
        &out_dir.join("parse_grammar.rs"),
        generate::rust::generate(&grammar).to_rustfmt_or_pretty_string(),
    )
    .unwrap();
}
