#![feature(decl_macro, generators, generator_trait)]

extern crate gll;

use std::fs::File;

macro_rules! testcase {
    ($name:ident:: $rule:ident($input:expr) => $expected:expr) => {
        pub mod $name {
            include!(concat!(env!("OUT_DIR"), "/", stringify!($name), ".rs"));
        }

        #[test]
        fn $name() {
            $name::$rule::parse_with($input, |parser, result| {
                let result = format!("{:#?}", result.unwrap());
                assert!(
                    result == $expected,
                    "mismatched output, expected:\n{}\n\nfound:\n{}",
                    $expected,
                    result
                );
                parser
                    .gss
                    .dump_graphviz(
                        &mut File::create(concat!(
                            env!("CARGO_MANIFEST_DIR"),
                            "/../target/",
                            stringify!($name),
                            "-gss.dot"
                        )).unwrap(),
                    ).unwrap();
                parser
                    .sppf
                    .dump_graphviz(
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
1:1-1:4 => S::X {
    a: 1:1-1:2 => A::A(
        1:1-1:2
    ),
    s: 1:2-1:3 => S::Y {
        s: 1:3-1:3 => S::Z(
            1:3-1:3
        ),
        b: 1:2-1:3 => B::A(
            1:2-1:3
        )
    },
    d: 1:3-1:4
} | S::Y {
    s: 1:2-1:4 => S::X {
        a: 1:2-1:3 => A::A(
            1:2-1:3
        ),
        s: 1:3-1:3 => S::Z(
            1:3-1:3
        ),
        d: 1:3-1:4
    },
    b: 1:1-1:2 => B::A(
        1:1-1:2
    )
}");
testcase!(gll10_g0_opaque::S("aad") => "\
1:1-1:4 => S {
    a: 1:1-1:2,
    s: 1:2-1:3 => S {
        s: 1:3-1:3 => S,
        b: 1:2-1:3
    }
} | S {
    s: 1:2-1:4 => S {
        a: 1:2-1:3,
        s: 1:3-1:3 => S
    },
    b: 1:1-1:2
}");
testcase!(gll13_g1::S("adb") => "\
1:1-1:4 => S::Z {
    a: 1:1-1:2,
    b: 1:3-1:4,
    d: 1:2-1:3
} | S::X {
    a: 1:1-1:2,
    s: 1:2-1:3 => S::Y(
        1:2-1:3
    ),
    b: 1:3-1:4
}");
testcase!(gll15_g0::A("aac") => "\
1:1-1:4 => A::Y {
    a: 1:1-1:2,
    x: 1:2-1:3 => A::Z(
        1:2-1:3
    ),
    c: 1:3-1:4
}");
testcase!(gll15_g0_nested::A("aab") => "\
1:1-1:4 => A::X {
    a: 1:1-1:2,
    x: 1:2-1:3 => A::Z(
        1:2-1:3
    ),
    b: 1:3-1:4
}");
