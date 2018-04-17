#![feature(conservative_impl_trait, decl_macro, from_ref, str_escape)]

extern crate indexing;
extern crate ordermap;

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

pub struct Parser<'id, P: ParseLabel, C: CodeLabel, I> {
    pub input: Container<'id, I>,
    pub gss: CallGraph<'id, C>,
    pub sppf: ParseGraph<'id, P>,
}

pub struct Threads<'id, C: CodeLabel> {
    queue: BinaryHeap<Call<'id, (Continuation<'id, C>, Range<'id>)>>,
    seen: BTreeSet<Call<'id, (Continuation<'id, C>, Range<'id>)>>,
}

impl<'id, C: CodeLabel> Threads<'id, C> {
    pub fn spawn(&mut self, next: Continuation<'id, C>, result: Range<'id>, range: Range<'id>) {
        let t = Call {
            callee: (next, result),
            range,
        };
        if self.seen.insert(t) {
            self.queue.push(t);
        }
    }
    pub fn steal(&mut self) -> Option<Call<'id, (Continuation<'id, C>, Range<'id>)>> {
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
pub struct Continuation<'id, C: CodeLabel> {
    pub code: C,
    pub stack: Call<'id, C>,
    pub state: usize,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
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

pub struct CallGraph<'id, C: CodeLabel> {
    pub threads: Threads<'id, C>,
    returns: HashMap<Call<'id, C>, BTreeSet<Continuation<'id, C>>>,
    pub results: HashMap<Call<'id, C>, BTreeSet<Range<'id>>>,
}

impl<'id, C: CodeLabel> CallGraph<'id, C> {
    pub fn print(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph gss {{")?;
        writeln!(out, "    graph [rankdir=RL]")?;
        for (source, returns) in &self.returns {
            for next in returns {
                writeln!(
                    out,
                    r#"    "{:?}" -> "{:?}" [label="{:?}"]"#,
                    source, next.stack, next.code
                )?;
            }
        }
        writeln!(out, "}}")
    }
    pub fn call(&mut self, call: Call<'id, C>, next: Continuation<'id, C>) {
        let returns = self.returns.entry(call).or_insert(BTreeSet::new());
        if returns.insert(next) {
            if returns.len() > 1 {
                if let Some(results) = self.results.get(&call) {
                    for &result in results {
                        self.threads
                            .spawn(next, result, call.range.subtract(result));
                    }
                }
            } else {
                let dummy = Range(call.range.frontiers().0);
                self.threads.spawn(
                    Continuation {
                        code: call.callee,
                        stack: call,
                        state: 0,
                    },
                    dummy,
                    call.range,
                );
            }
        }
    }
    pub fn ret(&mut self, call: Call<'id, C>, result: Range<'id>) {
        if self.results
            .entry(call)
            .or_insert(BTreeSet::new())
            .insert(result)
        {
            if let Some(returns) = self.returns.get(&call) {
                for &next in returns {
                    self.threads
                        .spawn(next, result, call.range.subtract(result));
                }
            }
        }
    }
}

pub struct ParseGraph<'id, P: ParseLabel> {
    pub children: HashMap<ParseNode<'id, P>, BTreeSet<usize>>,
}

impl<'id, P: ParseLabel> ParseGraph<'id, P> {
    pub fn add(&mut self, l: P, range: Range<'id>, child: usize) {
        self.children
            .entry(ParseNode { l: Some(l), range })
            .or_insert(BTreeSet::new())
            .insert(child);
    }

    pub fn unary_children<'a>(
        &'a self,
        node: ParseNode<'id, P>,
    ) -> impl Iterator<Item = ParseNode<'id, P>> + 'a {
        match node.l.unwrap().kind() {
            ParseLabelKind::Unary(l) => self.children[&node].iter().map(move |&i| {
                assert_eq!(i, 0);
                ParseNode {
                    l,
                    range: node.range,
                }
            }),
            _ => unreachable!(),
        }
    }

    pub fn binary_children<'a>(
        &'a self,
        node: ParseNode<'id, P>,
    ) -> impl Iterator<Item = (ParseNode<'id, P>, ParseNode<'id, P>)> + 'a {
        match node.l.unwrap().kind() {
            ParseLabelKind::Binary(left_l, right_l) => self.children[&node].iter().map(move |&i| {
                let (left, right, _) = node.range.split_at(i);
                (
                    ParseNode {
                        l: left_l,
                        range: Range(left),
                    },
                    ParseNode {
                        l: right_l,
                        range: Range(right),
                    },
                )
            }),
            _ => unreachable!(),
        }
    }

    pub fn print(&self, out: &mut Write) -> io::Result<()> {
        writeln!(out, "digraph sppf {{")?;
        let mut p = 0;
        for (source, children) in &self.children {
            writeln!(out, r#"    "{}" [shape=box]"#, source)?;
            match source.l.unwrap().kind() {
                ParseLabelKind::Choice => for &child in children {
                    let child = ParseNode {
                        l: Some(P::from_usize(child)),
                        range: source.range,
                    };
                    writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                    writeln!(out, r#"    "{}" -> p{}:n"#, source, p)?;
                    writeln!(out, r#"    p{}:s -> "{}":n [dir=none]"#, p, child)?;
                    p += 1;
                },

                ParseLabelKind::Unary(l) => for &child in children {
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

                ParseLabelKind::Binary(left_l, right_l) => for &child in children {
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
pub struct ParseNode<'id, P: ParseLabel> {
    pub l: Option<P>,
    pub range: Range<'id>,
}

impl<'id, P: ParseLabel> ParseNode<'id, P> {
    pub fn terminal(range: Range<'id>) -> ParseNode<'id, P> {
        ParseNode { l: None, range }
    }
}

impl<'id, P: ParseLabel> fmt::Display for ParseNode<'id, P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(l) = self.l {
            write!(f, "{} @ {}..{}", l, self.range.start(), self.range.end())
        } else {
            write!(f, "{}..{}", self.range.start(), self.range.end())
        }
    }
}

impl<'a, P: ParseLabel, C: CodeLabel, I: Trustworthy> Parser<'a, P, C, I> {
    pub fn with<F, R>(input: I, f: F) -> R
    where
        F: for<'id> FnOnce(Parser<'id, P, C, I>) -> R,
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

pub enum ParseLabelKind<P: ParseLabel> {
    Unary(Option<P>),
    Binary(Option<P>, Option<P>),
    Choice,
}

pub trait ParseLabel: fmt::Display + Ord + Hash + Copy + 'static {
    fn kind(self) -> ParseLabelKind<Self>;
    fn from_usize(i: usize) -> Self;
    fn to_usize(self) -> usize;
}

pub trait CodeLabel: fmt::Debug + Ord + Hash + Copy + 'static {}
