use crate::forest::{OwnedParseForestAndNode, ParseForest, ParseNode, ParseNodeKind};
use crate::high::ErasableL;
use crate::input::{Input, InputMatch, Range};
use indexing::{self, Index, Unknown};
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, BinaryHeap, HashMap};
use std::fmt;
use std::hash::Hash;
use std::io::{self, Write};

pub struct Parser<'a, 'i, C: CodeLabel, I: Input> {
    state: &'a mut ParserState<'i, C, I>,
    current: C,
    saved: Option<ParseNode<'i, C::ParseNodeKind>>,
    result: Range<'i>,
    remaining: Range<'i>,
}

struct ParserState<'i, C: CodeLabel, I: Input> {
    threads: Threads<'i, C>,
    gss: GraphStack<'i, C>,
    memoizer: Memoizer<'i, C>,
    forest: ParseForest<'i, C::ParseNodeKind, I>,
    last_input_pos: Index<'i, Unknown>,
    expected_pats: Vec<&'static dyn fmt::Debug>,
}

#[derive(Debug)]
pub struct ParseError<A> {
    pub at: A,
    pub expected: Vec<&'static dyn fmt::Debug>,
}

pub type ParseResult<A, T> = Result<T, ParseError<A>>;

impl<'i, C: CodeStep<I>, I: Input> Parser<'_, 'i, C, I> {
    pub fn parse(
        input: I,
        callee: C,
        kind: C::ParseNodeKind,
    ) -> ParseResult<I::SourceInfoPoint, OwnedParseForestAndNode<C::ParseNodeKind, I>> {
        ErasableL::indexing_scope(input.to_container(), |lifetime, input| {
            let call = Call {
                callee,
                range: Range(input.range()),
            };
            let mut state = ParserState {
                threads: Threads {
                    queue: BinaryHeap::new(),
                    seen: BTreeSet::new(),
                },
                gss: GraphStack {
                    returns: HashMap::new(),
                },
                memoizer: Memoizer {
                    lengths: HashMap::new(),
                },
                forest: ParseForest {
                    input,
                    possible_choices: HashMap::new(),
                    possible_splits: HashMap::new(),
                },
                last_input_pos: call.range.first(),
                expected_pats: vec![],
            };

            // Start with one thread, at the provided entry-point.
            state.threads.spawn(
                Continuation {
                    code: call.callee,
                    saved: None,
                    result: Range(call.range.frontiers().0),
                },
                call.range,
            );

            // Run all threads to completion.
            while let Some(next) = state.threads.steal() {
                let Call {
                    callee:
                        Continuation {
                            code,
                            saved,
                            result,
                        },
                    range,
                } = next;
                code.step(Parser {
                    state: &mut state,
                    current: code,
                    saved,
                    result,
                    remaining: range,
                });
            }

            // If the function call we started with ever returned,
            // we will find an entry for it in the memoizer, from
            // which we pick the longest match, which is only a
            // successful parse if it's as long as the input.
            let error = ParseError {
                at: I::source_info_point(&state.forest.input, state.last_input_pos),
                expected: state.expected_pats,
            };
            match state.memoizer.longest_result(call) {
                None => Err(error),
                Some(range) => {
                    if range == call.range {
                        Ok(OwnedParseForestAndNode::pack(
                            lifetime,
                            (state.forest, ParseNode { kind, range }),
                        ))
                    } else {
                        Err(error)
                    }
                }
            }
        })
    }

    pub fn input_consume_left<'a, Pat: fmt::Debug>(
        &'a mut self,
        pat: &'static Pat,
    ) -> Option<Parser<'a, 'i, C, I>>
    where
        I::Slice: InputMatch<Pat>,
    {
        let start = self.remaining.first();
        if start > self.state.last_input_pos {
            self.state.last_input_pos = start;
            self.state.expected_pats.clear();
        }
        match self.state.forest.input(self.remaining).match_left(pat) {
            Some(n) => {
                let (matching, after, _) = self.remaining.split_at(n);
                if n > 0 {
                    self.state.last_input_pos = after.first();
                    self.state.expected_pats.clear();
                }
                Some(Parser {
                    state: self.state,
                    current: self.current,
                    saved: self.saved,
                    result: Range(self.result.join(matching).unwrap()),
                    remaining: Range(after),
                })
            }
            None => {
                if start == self.state.last_input_pos {
                    self.state.expected_pats.push(pat);
                }
                None
            }
        }
    }

    pub fn input_consume_right<'a, Pat>(
        &'a mut self,
        pat: &'static Pat,
    ) -> Option<Parser<'a, 'i, C, I>>
    where
        I::Slice: InputMatch<Pat>,
    {
        // FIXME(eddyb) implement error reporting support like in `input_consume_left`
        match self.state.forest.input(self.remaining).match_right(pat) {
            Some(n) => {
                let (before, matching, _) = self.remaining.split_at(self.remaining.len() - n);
                Some(Parser {
                    state: self.state,
                    current: self.current,
                    saved: self.saved,
                    result: Range(matching.join(self.result.0).unwrap()),
                    remaining: Range(before),
                })
            }
            None => None,
        }
    }

    // FIXME(eddyb) maybe specialize this further, for `forest_add_split`?
    pub fn save(&mut self, kind: C::ParseNodeKind) {
        let old_saved = self.saved.replace(ParseNode {
            kind,
            range: self.result,
        });
        assert_eq!(old_saved, None);
    }

    pub fn take_saved(&mut self) -> ParseNode<'i, C::ParseNodeKind> {
        self.saved.take().unwrap()
    }

    pub fn forest_add_choice(&mut self, kind: C::ParseNodeKind, choice: C::ParseNodeKind) {
        self.state
            .forest
            .possible_choices
            .entry(ParseNode {
                kind,
                range: self.result,
            })
            .or_default()
            .insert(choice);
    }

    // FIXME(eddyb) safeguard this against misuse.
    pub fn forest_add_split(
        &mut self,
        kind: C::ParseNodeKind,
        left: ParseNode<'i, C::ParseNodeKind>,
    ) {
        self.state
            .forest
            .possible_splits
            .entry(ParseNode {
                kind,
                range: self.result,
            })
            .or_default()
            .insert(left.range.len());
    }

    pub fn spawn(&mut self, next: C) {
        self.state.threads.spawn(
            Continuation {
                code: next,
                saved: self.saved,
                result: self.result,
            },
            self.remaining,
        );
    }

    pub fn call(&mut self, callee: C, next: C) {
        let call = Call {
            callee,
            range: self.remaining,
        };
        let next = Continuation {
            code: next,
            saved: self.saved,
            result: self.result,
        };
        let returns = self.state.gss.returns.entry(call).or_default();
        if returns.insert(next) {
            if returns.len() > 1 {
                if let Some(lengths) = self.state.memoizer.lengths.get(&call) {
                    for &len in lengths {
                        let (call_result, remaining, _) = call.range.split_at(len);
                        self.state.threads.spawn(
                            Continuation {
                                result: Range(next.result.join(call_result).unwrap()),
                                ..next
                            },
                            Range(remaining),
                        );
                    }
                }
            } else {
                self.state.threads.spawn(
                    Continuation {
                        code: call.callee,
                        saved: None,
                        result: Range(call.range.frontiers().0),
                    },
                    call.range,
                );
            }
        }
    }

    pub fn ret(&mut self) {
        let call_result = self.result;
        let remaining = self.remaining;
        let call = Call {
            callee: self.current.enclosing_fn(),
            range: Range(call_result.join(remaining.0).unwrap()),
        };
        if self
            .state
            .memoizer
            .lengths
            .entry(call)
            .or_default()
            .insert(call_result.len())
        {
            if let Some(returns) = self.state.gss.returns.get(&call) {
                for &next in returns {
                    self.state.threads.spawn(
                        Continuation {
                            result: Range(next.result.join(call_result.0).unwrap()),
                            ..next
                        },
                        remaining,
                    );
                }
            }
        }
    }
}

struct Threads<'i, C: CodeLabel> {
    queue: BinaryHeap<Call<'i, Continuation<'i, C>>>,
    seen: BTreeSet<Call<'i, Continuation<'i, C>>>,
}

impl<'i, C: CodeLabel> Threads<'i, C> {
    fn spawn(&mut self, next: Continuation<'i, C>, range: Range<'i>) {
        let t = Call {
            callee: next,
            range,
        };
        if self.seen.insert(t) {
            self.queue.push(t);
        }
    }
    fn steal(&mut self) -> Option<Call<'i, Continuation<'i, C>>> {
        if let Some(t) = self.queue.pop() {
            loop {
                let old = self.seen.iter().rev().next().cloned();
                if let Some(old) = old {
                    // TODO also check end point for proper "t.range includes old.range".
                    let new_includes_old = t.range.contains(old.range.start()).is_some();
                    if !new_includes_old {
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
struct Continuation<'i, C: CodeLabel> {
    code: C,
    saved: Option<ParseNode<'i, C::ParseNodeKind>>,
    // FIXME(eddyb) for GC purposes, this would also need to be a `ParseNode`,
    // except that's not always the case? But `ParseNode | Range` seems likely
    // to be a deoptimization, especially if `ParseNode` stops containing a
    // `Range` (e.g. if it's an index in a node array).
    result: Range<'i>,
}

// TODO(eddyb) figure out if `Call<Continuation<C>>` can be optimized,
// based on the fact that `result.end == range.start` should always hold.
// (Also, `range.end` is constant across a whole parse)
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct Call<'i, C> {
    callee: C,
    range: Range<'i>,
}

impl<C: fmt::Display> fmt::Display for Call<'_, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({}..{})",
            self.callee,
            self.range.start(),
            self.range.end()
        )
    }
}

impl<C: PartialOrd> PartialOrd for Call<'_, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (Reverse(self.range), &self.callee).partial_cmp(&(Reverse(other.range), &other.callee))
    }
}

impl<C: Ord> Ord for Call<'_, C> {
    fn cmp(&self, other: &Self) -> Ordering {
        (Reverse(self.range), &self.callee).cmp(&(Reverse(other.range), &other.callee))
    }
}

struct GraphStack<'i, C: CodeLabel> {
    returns: HashMap<Call<'i, C>, BTreeSet<Continuation<'i, C>>>,
}

impl<C: CodeLabel> GraphStack<'_, C> {
    // FIXME(eddyb) figure out what to do here, now that
    // the GSS is no longer exposed in the public API.
    #[allow(unused)]
    fn dump_graphviz(&self, out: &mut dyn Write) -> io::Result<()> {
        writeln!(out, "digraph gss {{")?;
        writeln!(out, "    graph [rankdir=RL]")?;
        for (call, returns) in &self.returns {
            for next in returns {
                writeln!(
                    out,
                    r#"    "{:?}" -> "{:?}" [label="{:?}"]"#,
                    call,
                    Call {
                        callee: next.code.enclosing_fn(),
                        range: Range(next.result.join(call.range.0).unwrap()),
                    },
                    next.code
                )?;
            }
        }
        writeln!(out, "}}")
    }
}

struct Memoizer<'i, C: CodeLabel> {
    lengths: HashMap<Call<'i, C>, BTreeSet<usize>>,
}

impl<'i, C: CodeLabel> Memoizer<'i, C> {
    fn results<'a>(&'a self, call: Call<'i, C>) -> impl DoubleEndedIterator<Item = Range<'i>> + 'a {
        self.lengths
            .get(&call)
            .into_iter()
            .flat_map(move |lengths| {
                lengths
                    .iter()
                    .map(move |&len| Range(call.range.split_at(len).0))
            })
    }
    fn longest_result(&self, call: Call<'i, C>) -> Option<Range<'i>> {
        self.results(call).rev().next()
    }
}

pub trait CodeLabel: fmt::Debug + Ord + Hash + Copy + 'static {
    type ParseNodeKind: ParseNodeKind;

    fn enclosing_fn(self) -> Self;
}

pub trait CodeStep<I: Input>: CodeLabel {
    fn step<'i>(self, p: Parser<'_, 'i, Self, I>);
}
