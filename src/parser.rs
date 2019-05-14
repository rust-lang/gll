use crate::forest::{OwnedParseForestAndNode, ParseForest, ParseNode, ParseNodeKind};
use crate::high::ErasableL;
use crate::input::{Input, InputMatch, Range};
use indexing::{self, Index, Unknown};
use std::collections::HashMap;
use std::fmt;

pub struct Parser<'a, 'i, P: ParseNodeKind, I: Input> {
    state: &'a mut ParserState<'i, P, I>,
    result: Range<'i>,
    remaining: Range<'i>,
}

struct ParserState<'i, P: ParseNodeKind, I: Input> {
    forest: ParseForest<'i, P, I>,
    last_input_pos: Index<'i, Unknown>,
    expected_pats: Vec<&'static dyn fmt::Debug>,
}

#[derive(Debug)]
pub struct ParseError<A> {
    pub at: A,
    pub expected: Vec<&'static dyn fmt::Debug>,
}

pub type ParseResult<A, T> = Result<T, ParseError<A>>;

impl<'i, P: ParseNodeKind, I: Input> Parser<'_, 'i, P, I> {
    pub fn parse_with(
        input: I,
        f: impl for<'i2> FnOnce(Parser<'_, 'i2, P, I>) -> Option<ParseNode<'i2, P>>,
    ) -> ParseResult<I::SourceInfoPoint, OwnedParseForestAndNode<P, I>> {
        ErasableL::indexing_scope(input.to_container(), |lifetime, input| {
            let range = Range(input.range());
            let mut state = ParserState {
                forest: ParseForest {
                    input,
                    possible_choices: HashMap::new(),
                    possible_splits: HashMap::new(),
                },
                last_input_pos: range.first(),
                expected_pats: vec![],
            };

            let result = f(Parser {
                state: &mut state,
                result: Range(range.frontiers().0),
                remaining: range,
            });

            let error = ParseError {
                at: I::source_info_point(&state.forest.input, state.last_input_pos),
                expected: state.expected_pats,
            };
            match result {
                None => Err(error),
                Some(node) => {
                    // The result is only a successful parse if it's as long as the input.
                    if node.range == range {
                        Ok(OwnedParseForestAndNode::pack(
                            lifetime,
                            (state.forest, node),
                        ))
                    } else {
                        Err(error)
                    }
                }
            }
        })
    }

    // FIXME(eddyb) find an nicer way for algorithms to manipulate these ranges.
    pub fn result(&self) -> Range<'i> {
        self.result
    }

    pub fn remaining(&self) -> Range<'i> {
        self.remaining
    }

    pub fn with_result_and_remaining<'a>(
        &'a mut self,
        result: Range<'i>,
        remaining: Range<'i>,
    ) -> Parser<'a, 'i, P, I> {
        // HACK(eddyb) enforce that `result` and `remaining` are inside `self`.
        assert_eq!(self.result, Range(self.remaining.frontiers().0));
        let full_new_range = result.join(remaining.0).unwrap();
        assert!(self.remaining.start() <= full_new_range.start());
        assert_eq!(self.remaining.end(), full_new_range.end());

        Parser {
            state: self.state,
            result,
            remaining,
        }
    }

    pub fn input_consume_left<'a, Pat: fmt::Debug>(
        &'a mut self,
        pat: &'static Pat,
    ) -> Option<Parser<'a, 'i, P, I>>
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
    ) -> Option<Parser<'a, 'i, P, I>>
    where
        I::Slice: InputMatch<Pat>,
    {
        // FIXME(eddyb) implement error reporting support like in `input_consume_left`
        match self.state.forest.input(self.remaining).match_right(pat) {
            Some(n) => {
                let (before, matching, _) = self.remaining.split_at(self.remaining.len() - n);
                Some(Parser {
                    state: self.state,
                    result: Range(matching.join(self.result.0).unwrap()),
                    remaining: Range(before),
                })
            }
            None => None,
        }
    }

    pub fn forest_add_choice(&mut self, kind: P, choice: P) {
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
    pub fn forest_add_split(&mut self, kind: P, left: ParseNode<'i, P>) {
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
}
