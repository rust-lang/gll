#![feature(decl_macro)]

extern crate gll;

use gll::grammar::grammar;
use std::env;
use std::fs::File;
use std::path::PathBuf;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let mut gll10_g0 = grammar!{
        S = S0 { A S 'd' }
          | S1 { B S }
          | S2 {};

        A = A1 { 'a' }
          | A2 { 'c' };

        B = B1 { 'a' }
          | B2 { 'b' };
    };
    gll10_g0
        .generate(&mut File::create(&out_dir.join("gll10_g0.rs")).unwrap())
        .unwrap();

    let mut gll13_g1 = grammar!{
        S = X { 'a' S 'b' }
          | Y { 'd' }
          | Z { 'a' 'd' 'b' };
    };
    gll13_g1
        .generate(&mut File::create(&out_dir.join("gll13_g1.rs")).unwrap())
        .unwrap();

    let mut gll15_g0 = grammar!{
        A = X { 'a' A 'b' }
          | Y { 'a' A 'c' }
          | Z { 'a' };
    };
    gll15_g0
        .generate(&mut File::create(&out_dir.join("gll15_g0.rs")).unwrap())
        .unwrap();
}
