#![feature(
    arbitrary_self_types,
    decl_macro,
    fn_traits,
    macro_literal_matcher,
    slice_patterns,
    str_escape,
    try_from,
    unboxed_closures
)]

extern crate indexing;
extern crate ordermap;

// HACK(eddyb) bootstrap by including a subset of the `gll` crate.
#[path = "src/generate/mod.rs"]
mod generate;
#[path = "src/grammar.rs"]
mod grammar;
#[path = "src/scannerless.rs"]
mod scannerless;

use grammar::{call, eat, negative_lookahead};
use std::env;
use std::fs;
use std::path::PathBuf;

type Grammar = scannerless::Grammar<&'static str>;

// HACK(eddyb) more explicit subset of the grammar, for bootstrapping.
macro_rules! rule {
    ($pat:literal) => {
        eat($pat)
    };
    (..) => {
        eat(..)
    };
    ({ $start:literal ..= $end:literal }) => {
        eat($start..=$end)
    };
    ({ ! $pat:literal }) => {
        negative_lookahead($pat)
    };
    ({ ! $start:literal ..= $end:literal }) => {
        negative_lookahead($start..=$end)
    };
    ($rule:ident) => {
        call(stringify!($rule))
    };
    ({ $name:ident : $rule:tt }) => {
        rule!($rule).field(stringify!($name))
    };
    ({ $rule:tt ? }) => {
        rule!($rule).opt()
    };
    ({ $elem:tt * }) => {
        rule!($elem).repeat_many(None)
    };
    ({ $elem:tt + }) => {
        rule!($elem).repeat_more(None)
    };
    ({ $elem:tt + % $sep:tt }) => {
        rule!($elem).repeat_more(Some(rule!($sep)))
    };
    ({ $rule0:tt $(| $rule:tt)+ }) => {
        rule!($rule0) $(| rule!($rule))+
    };
    ({ $rule0:tt $($rule:tt)* }) => {
        rule!($rule0) $(+ rule!($rule))*
    };
}

macro_rules! grammar {
    ($($rule_name:ident = $($rule:tt)|+;)*) => ({
        let mut grammar = Grammar::new();
        $(grammar.define(stringify!($rule_name), rule!({ $($rule)|+ }));)*
        grammar
    })
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let mut grammar = grammar!{
        // Lexical grammar.
        Whitespace = {
            {{
                " " | "\t" | "\n" | "\r" |
                { "//" {{ {!"\n"} .. }*} "\n" } |
                { "/*" {{ {!"*/"} .. }*} "*/" }
            }*}
            {!" "} {!"\t"} {!"\n"} {!"\r"} {!"//"} {!"/*"}
        };
        Shebang = { "#!" {{ {!"\n"} .. }*} "\n" };

        IdentStart = {'a'..='z'} | {'A'..='Z'} | "_";
        IdentCont = IdentStart | {'0'..='9'};
        NotIdent = { {!'a'..='z'} {!'A'..='Z'} {!"_"} {!'0'..='9'} };
        Ident = { IdentStart {IdentCont*} NotIdent };

        StrLit = { "\"" {{ { {!"\\"} {!"\""} .. } | { "\\" Escape } }*} "\"" };
        CharLit = { "'" { { {!"\\"} {!"'"} .. } | { "\\" Escape } } "'" };
        Escape = "t" | "n" | "r" | "\\" | "'" | "\"";
    };

    grammar.extend(
        grammar!{
            // Main grammar.
            Grammar = { {Shebang?} {rules:{RuleDef*}} Whitespace };
            RuleDef = { {name:Ident} "=" {rule:Or} ";" };
            Or = {rules:{Concat+ % "|"}};
            Concat = {rules:{Rule+}};
            Rule = { {{ {field:Ident} ":" }?} {rule:Primary} {{modifier:Modifier}?} };
            Primary =
                {Eat:Pattern} |
                {NegativeLookahead:{ "!" {pat:Pattern} }} |
                {Call:Ident} |
                {Group:{ "{" {{or:Or}?} "}" }};
            Modifier =
                {Opt:"?"} |
                {Repeat:{ {repeat:Repeat} {{ "%" {sep:Primary} }?} }};
            Repeat =
                {Many:"*"} |
                {More:"+"};
            Pattern =
                {Str:StrLit} |
                {CharRange:{ {{start:CharLit}?} ".." {{end:CharLit}?} }} |
                {CharRangeInclusive:{ {{start:CharLit}?} "..=" {end:CharLit} }};
        }
        .insert_whitespace(grammar::call("Whitespace")),
    );

    fs::write(&out_dir.join("parse_grammar.rs"), grammar.generate_rust()).unwrap();
}
