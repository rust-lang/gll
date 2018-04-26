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
    s0: 0..3 => S0 {
        a: 0..1 => A {
            a1: 0..1 => A1
        },
        s: 1..2 => S {
            s1: 1..2 => S1 {
                b: 1..2 => B {
                    b1: 1..2 => B1
                },
                s: 2..2 => S {
                    s2: 2..2 => S2
                }
            }
        },
        d: 2..3
    }
} | S {
    s1: 0..3 => S1 {
        b: 0..1 => B {
            b1: 0..1 => B1
        },
        s: 1..3 => S {
            s0: 1..3 => S0 {
                a: 1..2 => A {
                    a1: 1..2 => A1
                },
                s: 2..2 => S {
                    s2: 2..2 => S2
                },
                d: 2..3
            }
        }
    }
}");
testcase!(gll13_g1::S(b"adb") => "\
0..3 => S {
    x: 0..3 => X {
        s: 1..2 => S {
            y: 1..2 => Y
        }
    }
} | S {
    z: 0..3 => Z
}");
testcase!(gll15_g0::A(b"aac") => "\
0..3 => A {
    y: 0..3 => Y {
        a: 1..2 => A {
            z: 1..2 => Z
        }
    }
}");
