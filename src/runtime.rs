use grammer::forest::{GrammarReflector, OwnedParseForestAndNode, ParseNode};
use grammer::input::{Input, InputMatch, Range};
use grammer::parser::{ParseResult, Parser};
use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeSet, BinaryHeap, HashMap};
use std::fmt;
use std::hash::Hash;
use std::io::{self, Write};

pub struct Runtime<'a, 'i, C: CodeLabel, I: Input, Pat> {
    parser: Parser<'a, 'i, C::GrammarReflector, I, Pat>,
    state: &'a mut RuntimeState<'i, C>,
    current: C,
    saved: Option<ParseNode<'i, C::ParseNodeKind>>,
}

struct RuntimeState<'i, C: CodeLabel> {
    threads: Threads<'i, C>,
    gss: GraphStack<'i, C>,
    memoizer: Memoizer<'i, C>,
}

impl<'i, P, G, C, I: Input, Pat> Runtime<'_, 'i, C, I, Pat>
where
    // FIXME(eddyb) these shouldn't be needed, as they are bounds on
    // `GrammarReflector::ParseNodeKind`, but that's ignored currently.
    P: fmt::Debug + Ord + Hash + Copy,
    G: GrammarReflector<ParseNodeKind = P>,
    C: CodeStep<I, Pat, GrammarReflector = G, ParseNodeKind = P>,
{
    pub fn parse(
        grammar: G,
        input: I,
        callee: C,
        kind: P,
    ) -> ParseResult<I::SourceInfoPoint, Pat, OwnedParseForestAndNode<G, P, I>> {
        Parser::parse_with(grammar, input, |mut parser| {
            let call = Call {
                callee,
                range: parser.remaining(),
            };
            let mut state = RuntimeState {
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
                code.step(Runtime {
                    parser: parser.with_result_and_remaining(result, range),
                    state: &mut state,
                    current: code,
                    saved,
                });
            }

            // If the function call we started with ever returned,
            // we will find an entry for it in the memoizer, from
            // which we pick the longest match.
            state
                .memoizer
                .longest_result(call)
                .map(|range| ParseNode { kind, range })
        })
    }

    pub fn input_consume_left<'a, SpecificPat: Into<Pat>>(
        &'a mut self,
        pat: SpecificPat,
    ) -> Option<Runtime<'a, 'i, C, I, Pat>>
    where
        I::Slice: InputMatch<SpecificPat>,
    {
        match self.parser.input_consume_left(pat) {
            Some(parser) => Some(Runtime {
                parser,
                state: self.state,
                current: self.current,
                saved: self.saved,
            }),
            None => None,
        }
    }

    pub fn input_consume_right<'a, SpecificPat: Into<Pat>>(
        &'a mut self,
        pat: SpecificPat,
    ) -> Option<Runtime<'a, 'i, C, I, Pat>>
    where
        I::Slice: InputMatch<SpecificPat>,
    {
        match self.parser.input_consume_right(pat) {
            Some(parser) => Some(Runtime {
                parser,
                state: self.state,
                current: self.current,
                saved: self.saved,
            }),
            None => None,
        }
    }

    // FIXME(eddyb) maybe specialize this further, for `forest_add_split`?
    pub fn save(&mut self, kind: P) {
        let old_saved = self.saved.replace(ParseNode {
            kind,
            range: self.parser.take_result(),
        });
        assert_eq!(old_saved, None);
    }

    pub fn take_saved(&mut self) -> ParseNode<'i, P> {
        self.saved.take().unwrap()
    }

    pub fn forest_add_choice(&mut self, kind: P, choice: P) {
        self.parser.forest_add_choice(kind, choice);
    }

    // FIXME(eddyb) safeguard this against misuse.
    pub fn forest_add_split(&mut self, kind: P, left: ParseNode<'i, P>) {
        self.parser.forest_add_split(kind, left);
    }

    pub fn spawn(&mut self, next: C) {
        self.state.threads.spawn(
            Continuation {
                code: next,
                saved: self.saved,
                result: self.parser.result(),
            },
            self.parser.remaining(),
        );
    }

    pub fn call(&mut self, callee: C, next: C) {
        let call = Call {
            callee,
            range: self.parser.remaining(),
        };
        let next = Continuation {
            code: next,
            saved: self.saved,
            result: self.parser.result(),
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
        let call_result = self.parser.result();
        let remaining = self.parser.remaining();
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
    // HACK(eddyb) this allows using `C::ParseNodeKind` in structs without
    // autoderiving adding spurious bounds on `C::GrammarReflector`.
    type GrammarReflector: GrammarReflector<ParseNodeKind = Self::ParseNodeKind>;
    type ParseNodeKind: fmt::Debug + Ord + Hash + Copy;

    fn enclosing_fn(self) -> Self;
}

pub trait CodeStep<I: Input, Pat>: CodeLabel {
    fn step<'i>(self, rt: Runtime<'_, 'i, Self, I, Pat>);
}
