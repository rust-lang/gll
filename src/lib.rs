#![feature(decl_macro, from_ref, rustc_private, str_escape)]

extern crate indexing;
extern crate ordermap;
extern crate syntax;

use indexing::container_traits::Trustworthy;
use indexing::{scope, Container};
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, BinaryHeap, HashMap};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::{self, Write};
use std::ops::Deref;

pub mod grammar;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Range<'id>(pub indexing::Range<'id>);

impl<'id> Deref for Range<'id> {
    type Target = indexing::Range<'id>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'id> PartialOrd for Range<'id> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.start(), self.end()).partial_cmp(&(other.start(), other.end()))
    }
}

impl<'id> Ord for Range<'id> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.start(), self.end()).cmp(&(other.start(), other.end()))
    }
}

impl<'id> Hash for Range<'id> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.start(), self.end()).hash(state);
    }
}

impl<'id> Range<'id> {
    pub fn subtract(self, other: Self) -> Self {
        assert_eq!(self.start(), other.start());
        Range(self.split_at(other.len()).1)
    }
}

pub struct Parser<'id, L: Label, I> {
    pub input: Container<'id, I>,
    pub gss: CallGraph<'id, L>,
    pub sppf: ParseGraph<'id, L>,
}

pub struct Threads<'id, L: Label> {
    queue: BinaryHeap<Call<'id, (Continuation<'id, L>, ParseNode<'id, L>)>>,
    seen: BTreeSet<Call<'id, (Continuation<'id, L>, ParseNode<'id, L>)>>,
}

impl<'id, L: Label> Threads<'id, L> {
    pub fn spawn(
        &mut self,
        next: Continuation<'id, L>,
        right: ParseNode<'id, L>,
        range: Range<'id>,
    ) {
        let t = Call {
            callee: (next, right),
            range,
        };
        if self.seen.insert(t) {
            self.queue.push(t);
        }
    }
    pub fn steal(&mut self) -> Option<Call<'id, (Continuation<'id, L>, ParseNode<'id, L>)>> {
        if let Some(t) = self.queue.pop() {
            loop {
                let old = self.seen.iter().rev().next().cloned();
                if let Some(old) = old {
                    // TODO also check end point for proper "t.range includes old.range".
                    if !t.range.contains(old.range.start()).is_some() {
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
pub struct Continuation<'id, L: Label> {
    pub code: L,
    pub stack: Call<'id, L>,
    pub left: ParseNode<'id, L>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Call<'id, C> {
    pub callee: C,
    pub range: Range<'id>,
}

impl<'id, C: fmt::Display> fmt::Display for Call<'id, C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}({}..{})",
            self.callee,
            self.range.start(),
            self.range.end()
        )
    }
}

impl<'id, C: PartialOrd> PartialOrd for Call<'id, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (Reverse(self.range), &self.callee).partial_cmp(&(Reverse(other.range), &other.callee))
    }
}

impl<'id, C: Ord> Ord for Call<'id, C> {
    fn cmp(&self, other: &Self) -> Ordering {
        (Reverse(self.range), &self.callee).cmp(&(Reverse(other.range), &other.callee))
    }
}

pub struct CallGraph<'id, L: Label> {
    pub threads: Threads<'id, L>,
    returns: HashMap<Call<'id, L>, BTreeSet<Continuation<'id, L>>>,
    pub results: HashMap<Call<'id, L>, BTreeSet<ParseNode<'id, L>>>,
}

impl<'id, L: Label> CallGraph<'id, L> {
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
    pub fn call(&mut self, call: Call<'id, L>, next: Continuation<'id, L>) {
        let returns = self.returns.entry(call).or_insert(BTreeSet::new());
        if returns.insert(next) {
            if returns.len() > 1 {
                if let Some(results) = self.results.get(&call) {
                    for &right in results {
                        self.threads
                            .spawn(next, right, call.range.subtract(right.range));
                    }
                }
            } else {
                let dummy = ParseNode {
                    l: None,
                    range: Range(call.range.frontiers().0),
                };
                self.threads.spawn(
                    Continuation {
                        code: call.callee,
                        stack: call,
                        left: dummy,
                    },
                    dummy,
                    call.range,
                );
            }
        }
    }
    pub fn ret(&mut self, call: Call<'id, L>, right: ParseNode<'id, L>) {
        if self.results
            .entry(call)
            .or_insert(BTreeSet::new())
            .insert(right)
        {
            if let Some(returns) = self.returns.get(&call) {
                for &next in returns {
                    self.threads
                        .spawn(next, right, call.range.subtract(right.range));
                }
            }
        }
    }
}

pub struct ParseGraphChildren<'id, L: Label> {
    pub unary: HashMap<ParseNode<'id, L>, BTreeSet<ParseNode<'id, L>>>,
    pub binary: HashMap<ParseNode<'id, L>, BTreeSet<(ParseNode<'id, L>, ParseNode<'id, L>)>>,
}

impl<'id, L: Label> ParseGraphChildren<'id, L> {
    pub fn add(
        &mut self,
        l: L,
        left: ParseNode<'id, L>,
        right: ParseNode<'id, L>,
    ) -> ParseNode<'id, L> {
        if left.range.is_empty() && left.l.is_none() {
            let result = ParseNode {
                l: Some(l),
                range: right.range,
            };
            self.unary
                .entry(result)
                .or_insert(BTreeSet::new())
                .insert(right);
            result
        } else {
            let result = ParseNode {
                l: Some(l),
                range: Range(left.range.join(right.range.0).unwrap().no_proof()),
            };
            self.binary
                .entry(result)
                .or_insert(BTreeSet::new())
                .insert((left, right));
            result
        }
    }
}

pub struct ParseGraph<'id, L: Label> {
    pub children: ParseGraphChildren<'id, L>,
}

impl<'id, L: Label> ParseGraph<'id, L> {
    pub fn add_children(
        &mut self,
        l: L,
        left: ParseNode<'id, L>,
        right: ParseNode<'id, L>,
    ) -> ParseNode<'id, L> {
        self.children.add(l, left, right)
    }
}

impl<'id, L: Label, I> Parser<'id, L, I> {
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
pub struct ParseNode<'id, L: Label> {
    pub l: Option<L>,
    pub range: Range<'id>,
}

impl<'id, L: Label> ParseNode<'id, L> {
    pub fn terminal(range: Range<'id>) -> ParseNode<'id, L> {
        ParseNode { l: None, range }
    }
}

impl<'id, L: Label> fmt::Display for ParseNode<'id, L> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(l) = self.l {
            write!(f, "{} @ {}..{}", l, self.range.start(), self.range.end())
        } else {
            write!(f, "{}..{}", self.range.start(), self.range.end())
        }
    }
}

impl<'a, L: Label, I: Trustworthy> Parser<'a, L, I> {
    pub fn with<F, R>(input: I, f: F) -> R
    where
        F: for<'id> FnOnce(Parser<'id, L, I>) -> R,
    {
        scope(input, |input| {
            f(Parser {
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
            })
        })
    }
}

pub trait Label: fmt::Display + Ord + Hash + Copy {}
