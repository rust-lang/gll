#![feature(decl_macro)]

extern crate gll;

use gll::grammar::grammar;
use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    type Grammar = gll::grammar::Grammar<gll::scannerless::Pat<&'static str, char>>;

    let gll10_g0: Grammar = grammar!{
        S = {
            X:{ a:A s:S d:"d" } |
            Y:{ b:B s:S } |
            Z:{}
        };

        A = {
            A:"a" |
            C:"c"
        };

        B = {
            A:"a" |
            B:"b"
        };
    };
    fs::write(&out_dir.join("gll10_g0.rs"), gll10_g0.generate_rust()).unwrap();

    let gll10_g0_opaque: Grammar = grammar!{
        S = {
            { a:A s:S "d" } |
            { b:B s:S } |
            {}
        };
        A = { "a" | "c" };
        B = { "a" | "b" };
    };
    fs::write(
        &out_dir.join("gll10_g0_opaque.rs"),
        gll10_g0_opaque.generate_rust(),
    ).unwrap();

    let gll13_g1: Grammar = grammar!{
        S = {
            X:{ a:"a" s:S b:"b" } |
            Y:{ "d" } |
            Z:{ a:"a" d:"d" b:"b" }
        };
    };
    fs::write(&out_dir.join("gll13_g1.rs"), gll13_g1.generate_rust()).unwrap();

    let gll15_g0: Grammar = grammar!{
        A = {
            X:{ a:"a" x:A b:"b" } |
            Y:{ a:"a" x:A c:"c" } |
            Z:{ "a" }
        };
    };
    fs::write(&out_dir.join("gll15_g0.rs"), gll15_g0.generate_rust()).unwrap();

    let gll15_g0_nested: Grammar = grammar!{
        A = {
            X:{ a:"a" { x:A b:"b" } } |
            Y:{ a:"a" x:A c:"c" } |
            Z:{ "a" "" }
        };
    };
    fs::write(
        &out_dir.join("gll15_g0_nested.rs"),
        gll15_g0_nested.generate_rust(),
    ).unwrap();
}
