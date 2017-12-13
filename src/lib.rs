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
    pub parse_results: HashMap<StackNode<L>, HashSet<ParseNode<L>>>,
}

#[derive(Default)]
pub struct Candidates<L: Label> {
    queue: BinaryHeap<Candidate<L>>,
    attempted: BTreeSet<Candidate<L>>,
}

impl<L: Label> Candidates<L> {
    pub fn add(&mut self, l: L, u: StackNode<L>, i: usize, w: ParseNode<L>) {
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
    pub u: StackNode<L>,
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
    edges: HashMap<StackNode<L>, HashSet<(L, ParseNode<L>, StackNode<L>)>>,
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
pub struct StackNode<L: Label> {
    pub l: L,
    pub i: usize,
}

impl<L: Label> fmt::Display for StackNode<L> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}, {}..", self.l, self.i)
    }
}

#[derive(Default)]
pub struct ParseGraph<L: Label> {
    pub children: HashMap<ParseNode<L>, HashSet<PackedNode<L>>>,
}

impl<L: Label> ParseGraph<L> {
    pub fn add_packed(&mut self, l: L, w: ParseNode<L>, z: ParseNode<L>) -> ParseNode<L> {
        let (y, p) = if w != ParseNode::DUMMY {
            (
                ParseNode {
                    l: Some(l),
                    i: w.i,
                    j: z.j,
                },
                PackedNode::Two(w, z),
            )
        } else {
            (
                ParseNode {
                    l: Some(l),
                    i: z.i,
                    j: z.j,
                },
                PackedNode::One(z),
            )
        };
        self.children.entry(y).or_insert(HashSet::new()).insert(p);
        y
    }
    pub fn print(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph gss {{")?;
        let mut p = 0;
        for (source, children) in &self.children {
            for child in children {
                writeln!(out, r#"    p{} [label="" shape=none width=0 height=0]"#, p)?;
                writeln!(out, r#"    "{}" -> p{}:n"#, source, p)?;
                match *child {
                    PackedNode::One(x) => {
                        writeln!(out, r#"    p{}:s -> "{}":n [dir=none]"#, p, x)?;
                    }
                    PackedNode::Two(a, b) => {
                        writeln!(out, r#"    p{}:sw -> "{}":n [dir=none]"#, p, a)?;
                        writeln!(out, r#"    p{}:se -> "{}":n [dir=none]"#, p, b)?;
                    }
                }
                p += 1;
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
        i: 1,
        j: 0,
    };

    pub fn terminal(i: usize, j: usize) -> ParseNode<L> {
        ParseNode { l: None, i, j }
    }
}

impl<L: Label> fmt::Display for ParseNode<L> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(l) = self.l {
            write!(f, "{}, ", l)?;
        }
        write!(f, "{}..{}", self.i, self.j)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PackedNode<L: Label> {
    One(ParseNode<L>),
    Two(ParseNode<L>, ParseNode<L>),
}

impl<L: Label, I> Parser<L, I> {
    pub fn new(input: I) -> Parser<L, I> {
        Parser {
            input,
            candidates: Candidates::default(),
            gss: StackGraph::default(),
            sppf: ParseGraph::default(),
            parse_results: HashMap::default(),
        }
    }
    pub fn create(&mut self, l: L, u: StackNode<L>, i: usize, w: ParseNode<L>) -> StackNode<L> {
        let v = StackNode {
            l: l.nonterminal_before_dot().unwrap(),
            i,
        };
        let edges = self.gss.edges.entry(v).or_insert(HashSet::new());
        if edges.insert((l, w, u)) && edges.len() > 1 {
            if let Some(results) = self.parse_results.get(&v) {
                for &z in results {
                    let y = self.sppf.add_packed(l, w, z);
                    self.candidates.add(l, u, y.j, y);
                }
            }
        }
        v
    }
    pub fn pop(&mut self, u: StackNode<L>, i: usize, z: ParseNode<L>) {
        if self.parse_results
            .entry(u)
            .or_insert(HashSet::new())
            .insert(z)
        {
            if let Some(edges) = self.gss.edges.get(&u) {
                for &(l, w, v) in edges {
                    let y = self.sppf.add_packed(l, w, z);
                    self.candidates.add(l, v, i, y);
                }
            }
        }
    }
}

pub trait Label: fmt::Display + Ord + Hash + Copy + Default {
    fn nonterminal_before_dot(&self) -> Option<Self>;
}
