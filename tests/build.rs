#![feature(decl_macro)]

extern crate gll;

use gll::grammar::grammar;
use std::env;
use std::fs::File;
use std::path::PathBuf;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let mut gamma0 = grammar!{
        Gamma0;
        A = X { 'a' A 'b' }
          | Y { 'a' A 'c' }
          | Z { 'a' };
    };
    gamma0
        .generate(&mut File::create(&out_dir.join("gamma0.rs")).unwrap())
        .unwrap();
}
