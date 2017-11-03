#![feature(decl_macro)]

extern crate gll;

use gll::grammar::grammar;
use std::fs::File;

#[test]
fn gamma_0() {
    let mut g = grammar!{
        Gamma0;
        A {
            X { 'a' A 'b' }
            Y { 'a' A 'c' }
            Z { 'a' }
        }
    };

    g.generate(&mut File::create("tests/gamma0.rs").unwrap())
        .unwrap();
}
