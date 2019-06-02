#![deny(rust_2018_idioms)]

use std::fs::File;

macro_rules! testcases {
    ($($name:ident { $($grammar:tt)* }: $($rule:ident($input:expr) => $expected:expr),* ;)*) => {
        $(mod $name {
            ::gll_macros::scannerless_parser!($($grammar)*);
        }
        #[test]
        fn $name() {$(
            let result = $name::$rule::parse($input);
            if let Ok(result) = &result {
                result.with(|result| {
                    // FIXME(eddyb) find a way to do this, given that
                    // the GSS is no longer exposed in the public API.
                    /*gss
                        .dump_graphviz(
                            &mut File::create(concat!(
                                env!("CARGO_MANIFEST_DIR"),
                                "/../target/",
                                stringify!($name),
                                "-gss.dot"
                            )).unwrap(),
                        ).unwrap();*/
                    result.forest
                        .dump_graphviz(
                            &mut File::create(concat!(
                                env!("CARGO_MANIFEST_DIR"),
                                "/../target/",
                                stringify!($name),
                                "-forest.dot"
                            )).unwrap(),
                        ).unwrap();
                });
            }

            let result = match &result {
                Ok(result) => format!("{:#?}", result),
                Err(gll::parser::ParseError {
                    at,
                    expected,
                }) => {
                    format!("{:?}: error: expected {:?}", at, expected)
                }
            };
            // FIXME(eddyb) Remove this trailing-comma-ignoring hack
            // once rust-lang/rust#59076 reaches the stable channel.
            let normalize = |s: &str| {
                s.replace(",\n", "\n")
            };
            assert!(
                normalize(&result) == normalize($expected),
                "mismatched output, expected:\n{}\n\nfound:\n{}",
                $expected,
                result
            );
        )*})*
    };
}

testcases![
    gll10_g0 {
        S = X:{ a:A s:S d:"d" } |
            Y:{ b:B s:S } |
            Z:{};

        A = A:"a" |
            C:"c";

        B = A:"a" |
            B:"b";
    }:
    S("aad") => "\
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
}",
// FIXME(eddyb) get replace quotes with backticks and pretify the `expected` list.
    S("aax") => r#"1:3: error: expected ["d", "d", "a", "b", "a", "c"]"#;

    gll10_g0_opaque {
        S = { a:A s:S "d" } |
            { b:B s:S } |
            {};
        A = "a" | "c";
        B = "a" | "b";
    }:
    S("aad") => "\
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
}";

    gll13_g1 {
        S = X:{ a:"a" s:S b:"b" } |
            Y:{ "d" } |
            Z:{ a:"a" d:"d" b:"b" };
    }:
    S("adb") => "\
1:1-1:4 => S::X {
    a: 1:1-1:2,
    s: 1:2-1:3 => S::Y(
        1:2-1:3
    ),
    b: 1:3-1:4
} | S::Z {
    a: 1:1-1:2,
    b: 1:3-1:4,
    d: 1:2-1:3
}";

    gll15_g0 {
        A = X:{ a:"a" x:A b:"b" } |
            Y:{ a:"a" x:A c:"c" } |
            Z:{ "a" };
    }:
    A("aac") => "\
1:1-1:4 => A::Y {
    a: 1:1-1:2,
    x: 1:2-1:3 => A::Z(
        1:2-1:3
    ),
    c: 1:3-1:4
}";

    gll15_g0_nested {
        A = X:{ a:"a" { x:A b:"b" } } |
            Y:{ a:"a" x:A c:"c" } |
            Z:{ "a" "" };
    }:
    A("aab") => "\
1:1-1:4 => A::X {
    a: 1:1-1:2,
    x: 1:2-1:3 => A::Z(
        1:2-1:3
    ),
    b: 1:3-1:4
}";

    repeat_many_trailing {
        A = elems:"a"* %% "b";
    }:
    A("abab") => "\
1:1-1:5 => A {
    elems: 1:1-1:5 => [
        1:1-1:2,
        1:2-1:3,
        1:3-1:4,
        1:4-1:5,
    ],
}",
    A("aba") => "\
1:1-1:4 => A {
    elems: 1:1-1:4 => [
        1:1-1:2,
        1:2-1:3,
        1:3-1:4,
    ],
}",
    A("b") => r#"1:1: error: expected ["a"]"#;

    nested_or {
        A = x:"x" { a:"a" | b:"b" };
    }:
    A("xa") => "\
1:1-1:3 => A {
    x: 1:1-1:2,
    a: 1:2-1:3,
}";
];
