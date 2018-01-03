#![feature(decl_macro, rustc_private, str_escape)]

extern crate ordermap;
extern crate syntax;

use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, BinaryHeap, HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::io::{self, Write};

pub mod grammar;

pub struct Parser<L: Label, I> {
    pub input: I,
    pub candidates: Candidates<L>,
    pub gss: StackGraph<L>,
    pub sppf: ParseGraph<L>,
}

#[derive(Default)]
pub struct Candidates<L: Label> {
    queue: BinaryHeap<Candidate<L>>,
    attempted: BTreeSet<Candidate<L>>,
}

impl<L: Label> Candidates<L> {
    pub fn add(&mut self, l: L, u: Call<L>, i: usize, w: ParseNode<L>) {
        let c = Candidate { l, u, i, w };
        if self.attempted.insert(c) {
            self.queue.push(c);
        }
    }
    pub fn remove(&mut self) -> Option<Candidate<L>> {
        if let Some(c) = self.queue.pop() {
            loop {
                let old = self.attempted.iter().rev().next().cloned();
                if let Some(old) = old {
                    if old.i < c.i {
                        self.attempted.remove(&old);
                        continue;
                    }
                }
                break;
            }
            Some(c)
        } else {
            self.attempted.clear();
            None
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Candidate<L: Label> {
    pub l: L,
    pub u: Call<L>,
    pub i: usize,
    pub w: ParseNode<L>,
}

impl<L: Label> PartialOrd for Candidate<L> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<L: Label> Ord for Candidate<L> {
    fn cmp(&self, other: &Self) -> Ordering {
        (Reverse(self.i), &self.l, &self.u, &self.w)
            .cmp(&(Reverse(other.i), &other.l, &other.u, &other.w))
    }
}

#[derive(Default)]
pub struct StackGraph<L: Label> {
    edges: HashMap<Call<L>, HashSet<(L, ParseNode<L>, Call<L>)>>,
}

impl<L: Label> StackGraph<L> {
    pub fn print(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph gss {{")?;
        writeln!(out, "    graph [rankdir=RL]")?;
        for (source, edges) in &self.edges {
            for &(l, _w, target) in edges {
                writeln!(out, r#"    "{}" -> "{}" [label="{}"]"#, source, target, l)?;
            }
        }
        writeln!(out, "}}")
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Call<L: Label> {
    pub l: L,
    pub i: usize,
}

impl<L: Label> fmt::Display for Call<L> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}({}..)", self.l, self.i)
    }
}

#[derive(Default)]
pub struct ParseGraphChildren<L: Label> {
    pub map: HashMap<ParseNode<L>, HashSet<ParseResult<L>>>,
}

impl<L: Label> ParseGraphChildren<L> {
    pub fn add_result(&mut self, l: L, w: ParseNode<L>, z: ParseNode<L>) -> ParseNode<L> {
        let (y, p) = if w != ParseNode::DUMMY {
            (
                ParseNode {
                    l: Some(l),
                    i: w.i,
                    j: z.j,
                },
                ParseResult::Binary(w, z),
            )
        } else {
            (
                ParseNode {
                    l: Some(l),
                    i: z.i,
                    j: z.j,
                },
                ParseResult::Unary(z),
            )
        };
        self.map.entry(y).or_insert(HashSet::new()).insert(p);
        y
    }
}

#[derive(Default)]
pub struct ParseGraph<L: Label> {
    pub children: ParseGraphChildren<L>,
    pub results: HashMap<Call<L>, HashSet<ParseNode<L>>>,
}

impl<L: Label> ParseGraph<L> {
    pub fn add_result(&mut self, l: L, w: ParseNode<L>, z: ParseNode<L>) -> ParseNode<L> {
        self.children.add_result(l, w, z)
    }
    pub fn print(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph sppf {{")?;
        let mut p = 0;
        for (source, children) in &self.children.map {
            writeln!(out, r#"    "{}" [shape=box]"#, source)?;
            for child in children {
                writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                writeln!(out, r#"    "{}" -> p{}:n"#, source, p)?;
                match *child {
                    ParseResult::Unary(x) => {
                        writeln!(out, r#"    p{}:s -> "{}":n [dir=none]"#, p, x)?;
                    }
                    ParseResult::Binary(a, b) => {
                        writeln!(out, r#"    p{}:sw -> "{}":n [dir=none]"#, p, a)?;
                        writeln!(out, r#"    p{}:se -> "{}":n [dir=none]"#, p, b)?;
                    }
                }
                p += 1;
            }
        }
        for (query, results) in &self.results {
            for result in results {
                writeln!(out, r#"    "{}" -> "{}""#, query, result)?;
            }
        }
        writeln!(out, "}}")
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ParseNode<L: Label> {
    pub l: Option<L>,
    pub i: usize,
    pub j: usize,
}

impl<L: Label> ParseNode<L> {
    pub const DUMMY: ParseNode<L> = ParseNode {
        l: None,
        i: !0,
        j: !0,
    };

    pub fn terminal(i: usize, j: usize) -> ParseNode<L> {
        ParseNode { l: None, i, j }
    }
}

impl<L: Label> fmt::Display for ParseNode<L> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if *self == Self::DUMMY {
            return write!(f, "DUMMY");
        }
        if let Some(l) = self.l {
            write!(f, "{}({}..) = ..{}", l, self.i, self.j)
        } else {
            write!(f, "{}..{}", self.i, self.j)
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ParseResult<L: Label> {
    Unary(ParseNode<L>),
    Binary(ParseNode<L>, ParseNode<L>),
}

impl<L: Label, I> Parser<L, I> {
    pub fn new(input: I) -> Parser<L, I> {
        Parser {
            input,
            candidates: Candidates::default(),
            gss: StackGraph::default(),
            sppf: ParseGraph::default(),
        }
    }
    pub fn call(&mut self, callee: Candidate<L>, next: L) -> Call<L> {
        let v = Call {
            l: callee.l,
            i: callee.i,
        };
        let edges = self.gss.edges.entry(v).or_insert(HashSet::new());
        if edges.insert((next, callee.w, callee.u)) && edges.len() > 1 {
            if let Some(results) = self.sppf.results.get(&v) {
                for &z in results {
                    let y = self.sppf.children.add_result(next, callee.w, z);
                    self.candidates.add(next, callee.u, y.j, y);
                }
            }
        }
        v
    }
    pub fn ret(&mut self, u: Call<L>, i: usize, z: ParseNode<L>) {
        if self.sppf
            .results
            .entry(u)
            .or_insert(HashSet::new())
            .insert(z)
        {
            if let Some(edges) = self.gss.edges.get(&u) {
                for &(l, w, v) in edges {
                    let y = self.sppf.add_result(l, w, z);
                    self.candidates.add(l, v, i, y);
                }
            }
        }
    }
}

pub trait Label: fmt::Display + Ord + Hash + Copy + Default {}
