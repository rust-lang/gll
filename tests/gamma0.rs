extern crate gll;

use self::gll::{Candidate, Label, ParseNode, Parser, StackNode};
use std::fmt;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Gamma0 {
    _0,
    _1,
    _2,
    _3,
    _4,
    _5,
    _6,
    _7,
    _8,
    _9,
    _10,
    _11,
}

macro_rules! L {
    ("L₀") => (Gamma0::_0);
    ("A") => (Gamma0::_1);
    ("A.X ::=·'a' A 'b'") => (Gamma0::_2);
    ("A.X ::= 'a'·A 'b'") => (Gamma0::_3);
    ("A.X ::= 'a' A·'b'") => (Gamma0::_4);
    ("A.X ::= 'a' A 'b'·") => (Gamma0::_5);
    ("A.Y ::=·'a' A 'c'") => (Gamma0::_6);
    ("A.Y ::= 'a'·A 'c'") => (Gamma0::_7);
    ("A.Y ::= 'a' A·'c'") => (Gamma0::_8);
    ("A.Y ::= 'a' A 'c'·") => (Gamma0::_9);
    ("A.Z ::=·'a'") => (Gamma0::_10);
    ("A.Z ::= 'a'·") => (Gamma0::_11);
}

impl Default for Gamma0 {
    fn default() -> Gamma0 {
        L!("L₀")
    }
}

impl fmt::Display for Gamma0 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match *self {
            L!("L₀") => "L₀",
            L!("A") => "A",
            L!("A.X ::=·'a' A 'b'") => "A.X ::=·'a' A 'b'",
            L!("A.X ::= 'a'·A 'b'") => "A.X ::= 'a'·A 'b'",
            L!("A.X ::= 'a' A·'b'") => "A.X ::= 'a' A·'b'",
            L!("A.X ::= 'a' A 'b'·") => "A.X ::= 'a' A 'b'·",
            L!("A.Y ::=·'a' A 'c'") => "A.Y ::=·'a' A 'c'",
            L!("A.Y ::= 'a'·A 'c'") => "A.Y ::= 'a'·A 'c'",
            L!("A.Y ::= 'a' A·'c'") => "A.Y ::= 'a' A·'c'",
            L!("A.Y ::= 'a' A 'c'·") => "A.Y ::= 'a' A 'c'·",
            L!("A.Z ::=·'a'") => "A.Z ::=·'a'",
            L!("A.Z ::= 'a'·") => "A.Z ::= 'a'·",
        };
        write!(f, "{}", s)
    }
}

impl Label for Gamma0 {
    fn nonterminal_before_dot(&self) -> Option<Gamma0> {
        match *self {
            L!("A.X ::= 'a' A·'b'") => Some(L!("A")),
            L!("A.Y ::= 'a' A·'c'") => Some(L!("A")),
            _ => None,
        }
    }
}

pub fn parse(input: &str) -> Parser<Gamma0> {
    let mut p = Parser::default();
    let mut c = Candidate {
        l: L!("A"),
        u: StackNode { l: L!("A"), i: 0 },
        i: 0,
        w: ParseNode::DUMMY,
    };
    loop {
        match c.l {
            L!("L₀") => if let Some(next) = p.candidates.remove() {
                c = next;
            } else {
                return p;
            },
            L!("A") => {
                p.candidates
                    .add(L!("A.X ::=·'a' A 'b'"), c.u, c.i, ParseNode::DUMMY);
                p.candidates
                    .add(L!("A.Y ::=·'a' A 'c'"), c.u, c.i, ParseNode::DUMMY);
                p.candidates
                    .add(L!("A.Z ::=·'a'"), c.u, c.i, ParseNode::DUMMY);
                c.l = L!("L₀");
            }
            L!("A.X ::=·'a' A 'b'") => if input[c.i..].starts_with("a") {
                let j = c.i + "a".len();
                let c_r = ParseNode::terminal(c.i, j);
                c.i = j;
                c.w = p.sppf.add_packed(L!("A.X ::= 'a'·A 'b'"), c.w, c_r);
                c.l = L!("A.X ::= 'a'·A 'b'");
            } else {
                c.l = L!("L₀");
            },
            L!("A.X ::= 'a'·A 'b'") => {
                c.u = p.create(L!("A.X ::= 'a' A·'b'"), c.u, c.i, c.w);
                c.l = L!("A");
            }
            L!("A.X ::= 'a' A·'b'") => if input[c.i..].starts_with("b") {
                let j = c.i + "b".len();
                let c_r = ParseNode::terminal(c.i, j);
                c.i = j;
                c.w = p.sppf.add_packed(L!("A.X ::= 'a' A 'b'·"), c.w, c_r);
                c.l = L!("A.X ::= 'a' A 'b'·");
            } else {
                c.l = L!("L₀");
            },
            L!("A.X ::= 'a' A 'b'·") => {
                c.w = p.sppf.add_packed(L!("A"), ParseNode::DUMMY, c.w);
                p.pop(c.u, c.i, c.w);
                c.l = L!("L₀");
            }
            L!("A.Y ::=·'a' A 'c'") => if input[c.i..].starts_with("a") {
                let j = c.i + "a".len();
                let c_r = ParseNode::terminal(c.i, j);
                c.i = j;
                c.w = p.sppf.add_packed(L!("A.Y ::= 'a'·A 'c'"), c.w, c_r);
                c.l = L!("A.Y ::= 'a'·A 'c'");
            } else {
                c.l = L!("L₀");
            },
            L!("A.Y ::= 'a'·A 'c'") => {
                c.u = p.create(L!("A.Y ::= 'a' A·'c'"), c.u, c.i, c.w);
                c.l = L!("A");
            }
            L!("A.Y ::= 'a' A·'c'") => if input[c.i..].starts_with("c") {
                let j = c.i + "c".len();
                let c_r = ParseNode::terminal(c.i, j);
                c.i = j;
                c.w = p.sppf.add_packed(L!("A.Y ::= 'a' A 'c'·"), c.w, c_r);
                c.l = L!("A.Y ::= 'a' A 'c'·");
            } else {
                c.l = L!("L₀");
            },
            L!("A.Y ::= 'a' A 'c'·") => {
                c.w = p.sppf.add_packed(L!("A"), ParseNode::DUMMY, c.w);
                p.pop(c.u, c.i, c.w);
                c.l = L!("L₀");
            }
            L!("A.Z ::=·'a'") => if input[c.i..].starts_with("a") {
                let j = c.i + "a".len();
                let c_r = ParseNode::terminal(c.i, j);
                c.i = j;
                c.w = p.sppf.add_packed(L!("A.Z ::= 'a'·"), c.w, c_r);
                c.l = L!("A.Z ::= 'a'·");
            } else {
                c.l = L!("L₀");
            },
            L!("A.Z ::= 'a'·") => {
                c.w = p.sppf.add_packed(L!("A"), ParseNode::DUMMY, c.w);
                p.pop(c.u, c.i, c.w);
                c.l = L!("L₀");
            }
        }
    }
}
