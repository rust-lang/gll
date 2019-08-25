#![deny(rust_2018_idioms)]

mod json_like {
    gll_macros::proc_macro_parser! {
        Value =
            | Null:"null"
            | False:"false"
            | True:"true"
            | Literal:LITERAL
            | Array:{ "[" elems:Value* % "," "]" }
            | Object:{ "{" fields:Field* % "," "}" }
            | InterpolateRust:{ "(" TOKEN_TREE+ ")" }
            ;
        Field = name:IDENT ":" value:Value;
    }
}

fn json_like_testcase(input: &str, expected: &str) {
    let tokens = input
        .parse::<gll::grammer::proc_macro::TokenStream>()
        .unwrap();

    let result = json_like::Value::parse(tokens);
    let result = match &result {
        Ok(result) => format!("{:#?}", result),
        Err(gll::grammer::parser::ParseError { at, expected }) => {
            format!("{:?}: error: expected {:?}", at, expected)
        }
    };

    // HACK(eddyb) clean up the result, as we have no span info.
    let result = result
        .replace("Span", "?")
        .replace("?..? => ", "")
        .replace("?..?", "?");

    assert!(
        result == expected,
        "mismatched output, expected:\n{}\n\nfound:\n{}",
        expected,
        result
    );
}

#[test]
fn json_like_success() {
    let input = stringify! {
        // Example from `serde_json`.
        {
            name: "John Doe",
            age: 43,
            address: {
                street: "10 Downing Street",
                city: "London"
            },
            phones: [
                "+44 1234567",
                "+44 2345678"
            ],

            test: [null, false, true, (format!("{:?}", Some(1 + 2)))]
        }
    };

    let expected = "\
Value::Object {
    fields: [
        Field {
            name: ?,
            value: Value::Literal(
                ?,
            ),
        },
        Field {
            name: ?,
            value: Value::Literal(
                ?,
            ),
        },
        Field {
            name: ?,
            value: Value::Object {
                fields: [
                    Field {
                        name: ?,
                        value: Value::Literal(
                            ?,
                        ),
                    },
                    Field {
                        name: ?,
                        value: Value::Literal(
                            ?,
                        ),
                    },
                ],
            },
        },
        Field {
            name: ?,
            value: Value::Array {
                elems: [
                    Value::Literal(
                        ?,
                    ),
                    Value::Literal(
                        ?,
                    ),
                ],
            },
        },
        Field {
            name: ?,
            value: Value::Array {
                elems: [
                    Value::Null(
                        ?,
                    ),
                    Value::False(
                        ?,
                    ),
                    Value::True(
                        ?,
                    ),
                    Value::InterpolateRust(
                        ?,
                    ),
                ],
            },
        },
    ],
}";

    json_like_testcase(input, expected);
}

#[test]
fn json_like_error() {
    let input = stringify! {
        stray_identifier
    };

    let expected = r#"?: error: expected ["(", "[", "{", "false", "null", "true", LITERAL]"#;

    json_like_testcase(input, expected);
}
