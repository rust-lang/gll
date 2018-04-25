#![feature(conservative_impl_trait, decl_macro)]

use std::fs::File;

macro_rules! testcase {
    ($name: ident:: $rule: ident($input: expr) => $expected: expr) => {
        pub mod $name {
            include!(concat!(env!("OUT_DIR"), "/", stringify!($name), ".rs"));
        }

        #[test]
        fn $name() {
            $name::Parser::with($input, |mut parser| {
                let result = format!("{:#?}", $name::$rule::parse(&mut parser).unwrap());
                assert!(
                    result == $expected,
                    "mismatched output, expected:\n{}\n\nfound:\n{}",
                    $expected,
                    result
                );
                parser
                    .gss
                    .print(
                        &mut File::create(concat!(env!("CARGO_MANIFEST_DIR"), "/../target/", stringify!($name), "-gss.dot"))
                            .unwrap(),
                    )
                    .unwrap();
                parser
                    .sppf
                    .print(
                        &mut File::create(concat!(env!("CARGO_MANIFEST_DIR"), "/../target/", stringify!($name), "-sppf.dot"))
                            .unwrap(),
                    )
                    .unwrap();
            });
        }
    };
}

testcase!(gll10_g0::S(b"aad") => "\
0..3 => S {
    S0: 0..3 => S0 {
        a: 0..1 => A {
            A1: 0..1 => A1
        },
        s: 1..2 => S {
            S1: 1..2 => S1 {
                b: 1..2 => B {
                    B1: 1..2 => B1
                },
                s: 2..2 => S {
                    S2: 2..2 => S2
                }
            }
        },
        d: 2..3
    }
} | S {
    S1: 0..3 => S1 {
        b: 0..1 => B {
            B1: 0..1 => B1
        },
        s: 1..3 => S {
            S0: 1..3 => S0 {
                a: 1..2 => A {
                    A1: 1..2 => A1
                },
                s: 2..2 => S {
                    S2: 2..2 => S2
                },
                d: 2..3
            }
        }
    }
}");
testcase!(gll13_g1::S(b"adb") => "\
0..3 => S {
    X: 0..3 => X {
        s: 1..2 => S {
            Y: 1..2 => Y
        }
    }
} | S {
    Z: 0..3 => Z
}");
testcase!(gll15_g0::A(b"aac") => "\
0..3 => A {
    Y: 0..3 => Y {
        a: 1..2 => A {
            Z: 1..2 => Z
        }
    }
}");
