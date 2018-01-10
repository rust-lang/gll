#![feature(decl_macro, from_ref, rustc_private, str_escape)]

extern crate ordermap;
extern crate syntax;

use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, BinaryHeap, HashMap};
use std::fmt;
use std::hash::Hash;
use std::io::{self, Write};

pub mod grammar;

pub struct Parser<L: Label, I> {
    pub input: I,
    pub gss: CallGraph<L>,
    pub sppf: ParseGraph<L>,
}

pub struct Threads<L: Label> {
    queue: BinaryHeap<Call<(Continuation<L>, ParseNode<L>)>>,
    seen: BTreeSet<Call<(Continuation<L>, ParseNode<L>)>>,
}

impl<L: Label> Threads<L> {
    pub fn spawn(&mut self, next: Continuation<L>, right: ParseNode<L>, i: usize) {
        let t = Call {
            callee: (next, right),
            i,
        };
        if self.seen.insert(t) {
            self.queue.push(t);
        }
    }
    pub fn steal(&mut self) -> Option<Call<(Continuation<L>, ParseNode<L>)>> {
        if let Some(t) = self.queue.pop() {
            loop {
                let old = self.seen.iter().rev().next().cloned();
                if let Some(old) = old {
                    if old.i < t.i {
                        self.seen.remove(&old);
                        continue;
                    }
                }
                break;
            }
            Some(t)
        } else {
            self.seen.clear();
            None
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Continuation<L: Label> {
    pub code: L,
    pub stack: Call<L>,
    pub left: ParseNode<L>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Call<C> {
    pub callee: C,
    pub i: usize,
}

impl<C: fmt::Display> fmt::Display for Call<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}({}..)", self.callee, self.i)
    }
}

impl<C: PartialOrd> PartialOrd for Call<C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (Reverse(self.i), &self.callee).partial_cmp(&(Reverse(other.i), &other.callee))
    }
}

impl<C: Ord> Ord for Call<C> {
    fn cmp(&self, other: &Self) -> Ordering {
        (Reverse(self.i), &self.callee).cmp(&(Reverse(other.i), &other.callee))
    }
}

pub struct CallGraph<L: Label> {
    pub threads: Threads<L>,
    returns: HashMap<Call<L>, BTreeSet<Continuation<L>>>,
    pub results: HashMap<Call<L>, BTreeSet<ParseNode<L>>>,
}

impl<L: Label> CallGraph<L> {
    pub fn print(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph gss {{")?;
        writeln!(out, "    graph [rankdir=RL]")?;
        for (source, returns) in &self.returns {
            for next in returns {
                writeln!(
                    out,
                    r#"    "{}" -> "{}" [label="{}"]"#,
                    source,
                    next.stack,
                    next.code
                )?;
            }
        }
        writeln!(out, "}}")
    }
    pub fn call(&mut self, call: Call<L>, next: Continuation<L>) {
        let returns = self.returns.entry(call).or_insert(BTreeSet::new());
        if returns.insert(next) {
            if returns.len() > 1 {
                if let Some(results) = self.results.get(&call) {
                    for &right in results {
                        self.threads.spawn(next, right, right.j);
                    }
                }
            } else {
                self.threads.spawn(
                    Continuation {
                        code: call.callee,
                        stack: call,
                        left: ParseNode::DUMMY,
                    },
                    ParseNode::DUMMY,
                    call.i,
                );
            }
        }
    }
    pub fn ret(&mut self, stack: Call<L>, right: ParseNode<L>) {
        if self.results
            .entry(stack)
            .or_insert(BTreeSet::new())
            .insert(right)
        {
            if let Some(returns) = self.returns.get(&stack) {
                for &next in returns {
                    self.threads.spawn(next, right, right.j);
                }
            }
        }
    }
}

pub struct ParseGraphChildren<L: Label> {
    pub unary: HashMap<ParseNode<L>, BTreeSet<ParseNode<L>>>,
    pub binary: HashMap<ParseNode<L>, BTreeSet<(ParseNode<L>, ParseNode<L>)>>,
}

impl<L: Label> ParseGraphChildren<L> {
    pub fn add(&mut self, l: L, left: ParseNode<L>, right: ParseNode<L>) -> ParseNode<L> {
        if left != ParseNode::DUMMY {
            let result = ParseNode {
                l: Some(l),
                i: left.i,
                j: right.j,
            };
            self.binary
                .entry(result)
                .or_insert(BTreeSet::new())
                .insert((left, right));
            result
        } else {
            let result = ParseNode {
                l: Some(l),
                i: right.i,
                j: right.j,
            };
            self.unary
                .entry(result)
                .or_insert(BTreeSet::new())
                .insert(right);
            result
        }
    }
}

pub struct ParseGraph<L: Label> {
    pub children: ParseGraphChildren<L>,
}

impl<L: Label> ParseGraph<L> {
    pub fn add_children(&mut self, l: L, left: ParseNode<L>, right: ParseNode<L>) -> ParseNode<L> {
        self.children.add(l, left, right)
    }
}

impl<L: Label, I> Parser<L, I> {
    pub fn print_sppf(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph sppf {{")?;
        let mut p = 0;
        for (source, children) in &self.sppf.children.unary {
            writeln!(out, r#"    "{}" [shape=box]"#, source)?;
            for child in children {
                writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                writeln!(out, r#"    "{}" -> p{}:n"#, source, p)?;
                writeln!(out, r#"    p{}:s -> "{}":n [dir=none]"#, p, child)?;
                p += 1;
            }
        }
        for (source, children) in &self.sppf.children.binary {
            writeln!(out, r#"    "{}" [shape=box]"#, source)?;
            for &(left, right) in children {
                writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                writeln!(out, r#"    "{}" -> p{}:n"#, source, p)?;
                writeln!(out, r#"    p{}:sw -> "{}":n [dir=none]"#, p, left)?;
                writeln!(out, r#"    p{}:se -> "{}":n [dir=none]"#, p, right)?;
                p += 1;
            }
        }
        for (query, results) in &self.gss.results {
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

impl<L: Label, I> Parser<L, I> {
    pub fn new(input: I) -> Parser<L, I> {
        Parser {
            input,
            gss: CallGraph {
                threads: Threads {
                    queue: BinaryHeap::new(),
                    seen: BTreeSet::new(),
                },
                returns: HashMap::new(),
                results: HashMap::new(),
            },
            sppf: ParseGraph {
                children: ParseGraphChildren {
                    unary: HashMap::new(),
                    binary: HashMap::new(),
                },
            },
        }
    }
}

pub trait Label: fmt::Display + Ord + Hash + Copy {}
