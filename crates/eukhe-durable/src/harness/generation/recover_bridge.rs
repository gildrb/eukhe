//! The bridge between the recoveries ([`recover`], [`rounds_in_a_row`],
//! [`retry_note`]) and their Bend model (the recoveries `Rec` of
//! `bend/run.bend`, whose laws `PROOF.bend` proves, H4.8): both run the
//! same replies and must print the same transcript, byte for byte.
//!
//! A scenario is a list of replies (`bend/bridge_recover.bend` documents
//! the format). The driver keeps what production keeps: the note of the
//! next request (its recovery and row, through [`retry_note`] as
//! `classify` makes it) and the context of the run (each round that ran
//! is a tool-use reply and its result, each answer a text reply, each
//! user message a user message). A stuck
//! reply goes through [`recover`]; the rounds of a call come from the
//! context through [`rounds_in_a_row`], with the call's intent and key
//! order changed at random, as they are no part of a call's identity.
//! After each reply both sides print the act, the recovery and row of the
//! next note, and the rounds in a row that the run ran with the last
//! calls.

use std::fmt::Write as _;

use eukhe_ai::providers::faux::{faux_assistant_message, FauxAssistantMessageOptions};
use eukhe_types::pi_ai::{
    AssistantContentBlock, JsonObject, JsonValue, Message, StopReason, TextContent, ToolCall,
    ToolResultMessage, UserContent, UserContentBlock, UserMessage,
};

use super::decide::{recover, retry_note, Act, Caps, Counts, Stuck, CAPS};
use super::note::{NoteCause, Recovery, RepeatedCall, RetryNote};
use super::repeat::rounds_in_a_row;
use crate::testing::bridge::{compare, Rng, Scenario};

/// One reply, as the model reads it.
#[derive(Clone, Copy)]
enum Out {
    Long,
    Leak {
        rebuilt: bool,
        hash: u64,
        kept: bool,
    },
    Ran {
        hash: u64,
        kept: bool,
    },
    Noted,
    /// A user message joins the context (a steer, the user's next turn).
    Said,
    Answer,
    Other,
}

/// The run's recoveries as the generation's phases keep them.
struct Run {
    caps: Caps,
    /// The note of the next request.
    note: Option<RetryNote>,
    /// The attempt of the request that the next reply answers.
    attempt: u64,
    context: Vec<Message>,
    /// The calls of the last round that ran.
    last: Vec<ToolCall>,
    /// The number in the text of the last round's result.
    result: u64,
    out: String,
}

fn assistant(stop_reason: StopReason, content: Vec<AssistantContentBlock>) -> Message {
    Message::Assistant(faux_assistant_message(
        content,
        FauxAssistantMessageOptions {
            stop_reason: Some(stop_reason),
            ..FauxAssistantMessageOptions::default()
        },
    ))
}

impl Run {
    /// The calls of hash `hash`: the same name and arguments, with a
    /// random intent and key order.
    fn calls(hash: u64, rng: &mut Rng) -> Vec<ToolCall> {
        let mut arguments = JsonObject::new();
        let intent = (
            "i".to_owned(),
            JsonValue::String(format!("intent {}", rng.below(100))),
        );
        let fields = [
            ("hash".to_owned(), JsonValue::from(hash)),
            ("path".to_owned(), JsonValue::from("a.txt")),
        ];
        if rng.chance(50) {
            arguments.insert(intent.0, intent.1);
            arguments.extend(fields);
        } else {
            arguments.extend(fields.into_iter().rev());
        }
        vec![ToolCall {
            id: format!("call_{}", rng.below(1_000_000)),
            name: "read".to_owned(),
            arguments,
            ..ToolCall::default()
        }]
    }

    /// The note after a reply whose retry carries `cause` (None: an error
    /// that is not noted), as `classify` makes it.
    fn retry(&mut self, cause: Option<NoteCause>) {
        let at = Counts {
            attempt: self.attempt,
            notes: self.note.as_ref().map_or(0, |note| note.spent),
            polls: 0,
            compacted: false,
        };
        self.note = retry_note(at, cause, self.note.take());
        self.attempt += 1;
    }

    /// A new generation: its first request, with no note.
    fn generation(&mut self) {
        self.note = None;
        self.attempt = 1;
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one arm per reply, as `Rec.step` of `bend/run.bend` has"
    )]
    fn reply(&mut self, out: Out, rng: &mut Rng) {
        let note = self.note.as_ref().map(|note| &note.cause);
        let act = match out {
            Out::Long => {
                let act = recover(Stuck::Length, note, &self.caps);
                if let Act::Redo { row } = act {
                    self.retry(Some(NoteCause::Length { tokens: 0, row }));
                }
                Some(act)
            }
            Out::Leak { rebuilt: false, .. } => {
                let act = recover(Stuck::Leak, note, &self.caps);
                if let Act::Redo { row } = act {
                    self.retry(Some(NoteCause::Leaked {
                        markup: "hermes".to_owned(),
                        reason: "bad JSON".to_owned(),
                        row,
                    }));
                }
                Some(act)
            }
            Out::Leak {
                rebuilt: true,
                hash,
                kept,
            }
            | Out::Ran { hash, kept } => {
                let calls = Self::calls(hash, rng);
                let rounds = rounds_in_a_row(&self.context, &calls);
                let act = recover(Stuck::Calls { rounds }, note, &self.caps);
                match act {
                    Act::Run => {
                        self.context.push(assistant(
                            StopReason::ToolUse,
                            calls
                                .iter()
                                .cloned()
                                .map(AssistantContentBlock::ToolCall)
                                .collect(),
                        ));
                        if !kept {
                            self.result += 1;
                        }
                        self.context.push(Message::ToolResult(ToolResultMessage {
                            tool_call_id: calls[0].id.clone(),
                            tool_name: "read".to_owned(),
                            content: vec![UserContentBlock::Text(TextContent::new(format!(
                                "result {}",
                                self.result
                            )))],
                            details: None,
                            usage: None,
                            nested_calls: None,
                            is_error: false,
                            timestamp: 0,
                            duration_ms: None,
                        }));
                        self.last = calls;
                        self.generation();
                    }
                    Act::Redo { row } => self.retry(Some(NoteCause::Redirect {
                        calls: vec![RepeatedCall {
                            tool: "read".to_owned(),
                            arguments: String::new(),
                        }],
                        rounds,
                        row,
                    })),
                    Act::Stand | Act::Quit => {}
                }
                Some(act)
            }
            Out::Noted => {
                self.retry(Some(NoteCause::NoAnswer));
                None
            }
            // The note stays: the request that the next reply answers is
            // the one that the note ends.
            Out::Said => {
                self.context.push(Message::User(UserMessage {
                    content: UserContent::Text("steer".to_owned()),
                    timestamp: 0,
                }));
                None
            }
            Out::Answer => {
                self.context.push(assistant(
                    StopReason::Stop,
                    vec![AssistantContentBlock::Text(TextContent::new("done"))],
                ));
                self.context.push(Message::User(UserMessage {
                    content: UserContent::Text("again".to_owned()),
                    timestamp: 0,
                }));
                self.generation();
                None
            }
            Out::Other => {
                self.retry(None);
                None
            }
        };
        let act = match act {
            None => "pass",
            Some(Act::Run) => "exec",
            Some(Act::Redo { .. }) => "redo",
            Some(Act::Stand) => "stand",
            Some(Act::Quit) => "quit",
        };
        let (kind, row) = match self.note.as_ref().map(|note| &note.cause) {
            None | Some(NoteCause::Repeated { .. } | NoteCause::NoAnswer) => ("free", 0),
            Some(cause @ NoteCause::Length { .. }) => ("longs", cause.row(Recovery::Length)),
            Some(cause @ NoteCause::Leaked { .. }) => ("leaks", cause.row(Recovery::Leak)),
            Some(cause @ NoteCause::Redirect { .. }) => ("loops", cause.row(Recovery::Redirect)),
        };
        let same = rounds_in_a_row(&self.context, &self.last) - 1;
        let _ = writeln!(self.out, "{act} {kind} row={row} same={same}");
    }
}

/// One reply the adversary may send; small hashes, so calls repeat, and
/// results that mostly stay, so rows grow.
fn pick(rng: &mut Rng) -> Out {
    let hash = rng.below(3);
    let kept = rng.chance(80);
    match rng.below(13) {
        0 | 1 => Out::Long,
        2 => Out::Leak {
            rebuilt: false,
            hash,
            kept,
        },
        3 => Out::Leak {
            rebuilt: true,
            hash,
            kept,
        },
        4..=8 => Out::Ran { hash, kept },
        9 => Out::Noted,
        10 => Out::Said,
        11 => Out::Answer,
        _ => Out::Other,
    }
}

fn write(events: &mut String, out: Out) {
    let (kind, hash, rebuilt, kept) = match out {
        Out::Long => ('L', 0, false, false),
        Out::Leak {
            rebuilt,
            hash,
            kept,
        } => ('K', hash, rebuilt, kept),
        Out::Ran { hash, kept } => ('R', hash, false, kept),
        Out::Noted => ('N', 0, false, false),
        Out::Said => ('S', 0, false, false),
        Out::Answer => ('A', 0, false, false),
        Out::Other => ('O', 0, false, false),
    };
    let _ = writeln!(
        events,
        "v {kind} {hash} {} {}",
        u8::from(rebuilt),
        u8::from(kept)
    );
}

/// One scenario: its caps, then its replies.
fn scenario(
    rng: &mut Rng,
    caps: Caps,
    inputs: impl IntoIterator<Item = Out>,
    events: &mut String,
    transcript: &mut String,
) {
    let _ = writeln!(
        events,
        "9 {} {} {} {}",
        caps.length, caps.leak, caps.redirect, caps.repeat
    );
    let mut run = Run {
        caps,
        note: None,
        attempt: 1,
        context: Vec::new(),
        last: Vec::new(),
        result: 0,
        out: String::new(),
    };
    for input in inputs {
        write(events, input);
        run.reply(input, rng);
    }
    transcript.push_str(&run.out);
}

/// The same calls with the same results round after round, then length
/// stops, then leaks: each recovery goes to its cap.
fn stuck() -> impl Iterator<Item = Out> {
    let ran = Out::Ran {
        hash: 7,
        kept: true,
    };
    let leak = Out::Leak {
        rebuilt: false,
        hash: 0,
        kept: true,
    };
    std::iter::repeat_n(ran, 9)
        .chain(std::iter::repeat_n(Out::Long, 5))
        .chain(std::iter::repeat_n(leak, 4))
}

#[test]
fn the_rust_recoveries_equal_the_bend_model() {
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let (mut events, mut transcript) = (String::new(), String::new());
    scenario(&mut rng, CAPS, stuck(), &mut events, &mut transcript);
    let random: Vec<Out> = (0..200).map(|_| pick(&mut rng)).collect();
    scenario(&mut rng, CAPS, random, &mut events, &mut transcript);
    for _ in 0..300 {
        let caps = Caps {
            length: u32::try_from(rng.below(4)).unwrap_or(0),
            leak: u32::try_from(rng.below(4)).unwrap_or(0),
            redirect: u32::try_from(rng.below(4)).unwrap_or(0),
            repeat: u32::try_from(rng.below(6)).unwrap_or(0),
        };
        if rng.chance(20) {
            scenario(&mut rng, caps, stuck(), &mut events, &mut transcript);
        } else {
            let replies = rng.range(1, 30);
            let random: Vec<Out> = (0..replies).map(|_| pick(&mut rng)).collect();
            scenario(&mut rng, caps, random, &mut events, &mut transcript);
        }
    }
    compare(
        "bend/bridge_recover.bend",
        [Scenario {
            name: "every scenario".to_owned(),
            events,
            transcript,
        }],
    );
}
