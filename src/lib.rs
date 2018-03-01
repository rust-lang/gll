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
    queue: BinaryHeap<Call<'id, (Continuation<'id, L>, Range<'id>)>>,
    seen: BTreeSet<Call<'id, (Continuation<'id, L>, Range<'id>)>>,
}

impl<'id, L: Label> Threads<'id, L> {
    pub fn spawn(&mut self, next: Continuation<'id, L>, right: Range<'id>, range: Range<'id>) {
        let t = Call {
            callee: (next, right),
            range,
        };
        if self.seen.insert(t) {
            self.queue.push(t);
        }
    }
    pub fn steal(&mut self) -> Option<Call<'id, (Continuation<'id, L>, Range<'id>)>> {
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
    pub left: Range<'id>,
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
    pub results: HashMap<Call<'id, L>, BTreeSet<Range<'id>>>,
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
                    source, next.stack, next.code
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
                        self.threads.spawn(next, right, call.range.subtract(right));
                    }
                }
            } else {
                let dummy = Range(call.range.frontiers().0);
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
    pub fn ret(&mut self, call: Call<'id, L>, right: Range<'id>) {
        if self.results
            .entry(call)
            .or_insert(BTreeSet::new())
            .insert(right)
        {
            if let Some(returns) = self.returns.get(&call) {
                for &next in returns {
                    self.threads.spawn(next, right, call.range.subtract(right));
                }
            }
        }
    }
}

pub struct ParseGraph<'id, L: Label> {
    pub children: HashMap<ParseNode<'id, L>, BTreeSet<usize>>,
}

impl<'id, L: Label> ParseGraph<'id, L> {
    pub fn add_choice(&mut self, l: L, range: Range<'id>, child: L) -> ParseNode<'id, L> {
        let result = ParseNode { l: Some(l), range };
        self.children
            .entry(result)
            .or_insert(BTreeSet::new())
            .insert(child.to_usize());
        result
    }
    pub fn add_unary(&mut self, l: L, range: Range<'id>) -> ParseNode<'id, L> {
        let result = ParseNode { l: Some(l), range };
        self.children
            .entry(result)
            .or_insert(BTreeSet::new())
            .insert(0);
        result
    }
    pub fn add_binary(&mut self, l: L, left: Range<'id>, right: Range<'id>) -> ParseNode<'id, L> {
        let result = ParseNode {
            l: Some(l),
            range: Range(left.join(right.0).unwrap().no_proof()),
        };
        self.children
            .entry(result)
            .or_insert(BTreeSet::new())
            .insert(left.len());

        result
    }

    pub fn print(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph sppf {{")?;
        let mut p = 0;
        for (source, children) in &self.children {
            writeln!(out, r#"    "{}" [shape=box]"#, source)?;
            match source.l.unwrap().kind() {
                LabelKind::Choice => for &child in children {
                    let child = ParseNode {
                        l: Some(L::from_usize(child)),
                        range: source.range,
                    };
                    writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                    writeln!(out, r#"    "{}" -> p{}:n"#, source, p)?;
                    writeln!(out, r#"    p{}:s -> "{}":n [dir=none]"#, p, child)?;
                    p += 1;
                },

                LabelKind::Unary(l) => for &child in children {
                    assert_eq!(child, 0);
                    let child = ParseNode {
                        l,
                        range: source.range,
                    };
                    writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                    writeln!(out, r#"    "{}" -> p{}:n"#, source, p)?;
                    writeln!(out, r#"    p{}:s -> "{}":n [dir=none]"#, p, child)?;
                    p += 1;
                },

                LabelKind::Binary(left_l, right_l) => for &child in children {
                    let (left, right, _) = source.range.split_at(child);
                    let (left, right) = (
                        ParseNode {
                            l: left_l,
                            range: Range(left),
                        },
                        ParseNode {
                            l: right_l,
                            range: Range(right),
                        },
                    );
                    writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                    writeln!(out, r#"    "{}" -> p{}:n"#, source, p)?;
                    writeln!(out, r#"    p{}:sw -> "{}":n [dir=none]"#, p, left)?;
                    writeln!(out, r#"    p{}:se -> "{}":n [dir=none]"#, p, right)?;
                    p += 1;
                },
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
                    children: HashMap::new(),
                },
            })
        })
    }
}

pub enum LabelKind<L: Label> {
    Unary(Option<L>),
    Binary(Option<L>, Option<L>),
    Choice,
}

pub trait Label: fmt::Display + Ord + Hash + Copy + 'static {
    fn kind(self) -> LabelKind<Self>;
    fn from_usize(i: usize) -> Self;
    fn to_usize(self) -> usize;
}
