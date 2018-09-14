#![feature(decl_macro)]

use std::fs::File;

macro_rules! testcase {
    ($name:ident:: $rule:ident($input:expr) => $expected:expr) => {
        pub mod $name {
            include!(concat!(env!("OUT_DIR"), "/", stringify!($name), ".rs"));
        }

        #[test]
        fn $name() {
            $name::Parser::with_str($input, |mut parser, range| {
                let result = format!("{:#?}", $name::$rule::parse(&mut parser, range).unwrap());
                assert!(
                    result == $expected,
                    "mismatched output, expected:\n{}\n\nfound:\n{}",
                    $expected,
                    result
                );
                parser
                    .gss
                    .print(
                        &mut File::create(concat!(
                            env!("CARGO_MANIFEST_DIR"),
                            "/../target/",
                            stringify!($name),
                            "-gss.dot"
                        )).unwrap(),
                    ).unwrap();
                parser
                    .sppf
                    .print(
                        &mut File::create(concat!(
                            env!("CARGO_MANIFEST_DIR"),
                            "/../target/",
                            stringify!($name),
                            "-sppf.dot"
                        )).unwrap(),
                    ).unwrap();
            });
        }
    };
}

testcase!(gll10_g0::S("aad") => "\
0..3 => S::X {
    a: 0..1 => A::A(
        0..1
    ),
    s: 1..2 => S::Y {
        s: 2..2 => S::Z(
            2..2
        ),
        b: 1..2 => B::A(
            1..2
        )
    },
    d: 2..3
} | S::Y {
    s: 1..3 => S::X {
        a: 1..2 => A::A(
            1..2
        ),
        s: 2..2 => S::Z(
            2..2
        ),
        d: 2..3
    },
    b: 0..1 => B::A(
        0..1
    )
}");
testcase!(gll10_g0_opaque::S("aad") => "\
0..3 => S {
    a: 0..1,
    s: 1..2 => S {
        s: 2..2 => S,
        b: 1..2
    }
} | S {
    s: 1..3 => S {
        a: 1..2,
        s: 2..2 => S
    },
    b: 0..1
}");
testcase!(gll13_g1::S("adb") => "\
0..3 => S::Z {
    a: 0..1,
    b: 2..3,
    d: 1..2
} | S::X {
    a: 0..1,
    s: 1..2 => S::Y(
        1..2
    ),
    b: 2..3
}");
testcase!(gll15_g0::A("aac") => "\
0..3 => A::Y {
    a: 0..1,
    x: 1..2 => A::Z(
        1..2
    ),
    c: 2..3
}");
testcase!(gll15_g0_nested::A("aab") => "\
0..3 => A::X {
    a: 0..1,
    x: 1..2 => A::Z(
        1..2
    ),
    b: 2..3
}");
