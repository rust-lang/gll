#![feature(decl_macro)]

extern crate gll;

use gll::grammar::grammar;
use std::env;
use std::fs::File;
use std::path::PathBuf;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let mut gll10_g0 = grammar!{
        S = { {a: A} {s0: S} {d: "d"} }
          | { {b: B} {s1: S} }
          | {};

        A = {a: "a"}
          | {c: "c"};

        B = {a: "a"}
          | {b: "b"};
    };
    gll10_g0.generate(&mut File::create(&out_dir.join("gll10_g0.rs")).unwrap());

    let mut gll10_g0_opaque = grammar!{
        S = { {a: A} {s0: S} "d" }
          | { {b: B} {s1: S} }
          | {};
        A = "a" | "c";
        B = "a" | "b";
    };
    gll10_g0_opaque.generate(&mut File::create(&out_dir.join("gll10_g0_opaque.rs")).unwrap());

    let mut gll13_g1 = grammar!{
        S = { {a0: "a"} {s: S} {b0: "b"} }
          | {d0: "d"}
          | { {a1: "a"} {d1: "d"} {b1: "b"} };
    };
    gll13_g1.generate(&mut File::create(&out_dir.join("gll13_g1.rs")).unwrap());

    let mut gll15_g0 = grammar!{
        A = { {a0: "a"} {a1: A} {b: "b"} }
          | { {a2: "a"} {a3: A} {c: "c"} }
          | {a4: "a"};
    };
    gll15_g0.generate(&mut File::create(&out_dir.join("gll15_g0.rs")).unwrap());

    let mut gll15_g0_nested = grammar!{
        A = { {a0: "a"} { {a1: A} {b: "b"} } }
          | { {a2: "a"} {a3: A} {c: "c"} }
          | {a4: "a"};
    };
    gll15_g0_nested.generate(&mut File::create(&out_dir.join("gll15_g0_nested.rs")).unwrap());
}
