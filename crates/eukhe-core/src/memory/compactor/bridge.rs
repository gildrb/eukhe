//! The bridge between the compactor and its Bend model
//! (`bend/compactor.bend`, whose laws `PROOF.bend` proves, LAWS.bend
//! H1): both run the same scenarios and must print the same transcript,
//! byte for byte.
//!
//! A line scenario is a node's input and the model's replies in order:
//! texts of any length (multibyte characters across the cut), empty texts,
//! thinking-only replies, errors, and too few replies. The Rust side runs
//! `build_line` on a scripted summarizer and prints how many calls it made
//! and the line (each character by its UTF-8 width); `bridge/bridge_compactor.bend`
//! prints the same from `line`. The failure cap scenario runs every
//! sequence of up to six ends of a node's calls (a failed call, a disk
//! error) through [`Pend::after`], which `Actor::failed` counts with, and
//! prints the failures left after each; the model prints `Pend.after`'s.

use std::fmt::Write as _;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, StopReason};

use super::tests::{reply, thinking_only, Scripted};
use super::{build_line, CallEnd, NodeRequest, Pend, ResponseStarted, FAILURES, NODE, TRIES};
use crate::memory::saved::CompactionPrompt;

/// One character of each UTF-8 width, 1 to 4 bytes.
const CHARACTERS: [char; 4] = ['a', 'é', '€', '😀'];

/// A text of about `bytes` bytes: its characters, and their widths as the
/// scenario writes them.
fn text(rng: &mut Rng, bytes: u64) -> (String, String) {
    let bytes = usize::try_from(bytes).unwrap_or(usize::MAX);
    let wide = rng.chance(40);
    let (mut text, mut widths) = (String::new(), String::new());
    while text.len() < bytes {
        let at = if wide { rng.below(4) } else { 0 };
        let character = CHARACTERS[usize::try_from(at).unwrap_or(0)];
        text.push(character);
        let _ = write!(widths, "{}", character.len_utf8());
    }
    (text, widths)
}

/// A reply with `line` as its text: sometimes padded with spaces, split
/// in two text blocks, or after a thinking block (none of which is part of
/// the line).
fn reply_with(rng: &mut Rng, line: &str) -> AssistantMessage {
    let padded = if rng.chance(20) {
        format!("  {line}\n")
    } else {
        line.to_string()
    };
    let mut message = reply(&padded);
    if rng.chance(20) {
        let mut thinking = thinking_only().content;
        thinking.append(&mut message.content);
        message.content = thinking;
    }
    if rng.chance(15) {
        if let Some(AssistantContentBlock::Text(mut tail)) = message.content.pop() {
            let at = tail.text.char_indices().nth(1).map_or(0, |(at, _)| at);
            let mut head = tail.clone();
            head.text.truncate(at);
            tail.text.drain(..at);
            message.content.push(AssistantContentBlock::Text(head));
            message.content.push(AssistantContentBlock::Text(tail));
        }
    }
    message
}

/// One scenario: its events for the model and the replies for the Rust
/// summarizer.
fn scenario(rng: &mut Rng, events: &mut String) -> (String, Vec<anyhow::Result<AssistantMessage>>) {
    let bytes = rng.range(1, 3000);
    let (input, input_widths) = text(rng, bytes);
    let _ = writeln!(events, "s {TRIES} {NODE} {input_widths}");
    let mut replies = Vec::new();
    // Sometimes fewer replies than calls: the missing reply is an error.
    let count = rng.range(0, 7);
    // Over-long replies often shrink, as a model asked to cut does.
    let mut size = rng.range(513, 1500);
    for _ in 0..count {
        let roll = rng.range(0, 99);
        if roll < 8 {
            events.push_str("e\n");
            let mut failed = reply("partial");
            failed.stop_reason = StopReason::Error;
            replies.push(if rng.chance(50) {
                Ok(failed)
            } else {
                Err(anyhow::anyhow!("overloaded"))
            });
        } else if roll < 18 {
            events.push_str("r\n");
            replies.push(Ok(if rng.chance(50) {
                thinking_only()
            } else {
                reply(" \n ")
            }));
        } else {
            let bytes = if roll < 38 {
                rng.range(1, 512)
            } else if roll < 70 {
                size = size.saturating_sub(rng.range(0, 40)).max(1);
                size
            } else {
                rng.range(400, 1500)
            };
            let (line, widths) = text(rng, bytes);
            let _ = writeln!(events, "r {widths}");
            replies.push(Ok(reply_with(rng, &line)));
        }
    }
    events.push_str(".\n");
    (input, replies)
}

/// The failure cap scenario: `p FAILURES <ends>` for the model (`f` a
/// failed call, `d` a disk error), from an untried node.
fn failure_cap() -> Scenario {
    let show = |pend: Pend, out: &mut String| match pend {
        Pend::Made => out.push('M'),
        Pend::Owed(left) => {
            let _ = write!(out, "{left}");
        }
    };
    let (mut events, mut transcript) = (String::new(), String::new());
    for length in 0..=6 {
        for bits in 0..1u32 << length {
            let _ = write!(events, "p {FAILURES} ");
            let mut pend = Pend::UNTRIED;
            transcript.push_str("p=");
            show(pend, &mut transcript);
            for at in 0..length {
                let end = if (bits >> at) & 1 == 1 {
                    CallEnd::Failed
                } else {
                    CallEnd::Disk
                };
                events.push(match end {
                    CallEnd::Failed => 'f',
                    CallEnd::Disk => 'd',
                });
                pend = pend.after(end);
                transcript.push(' ');
                show(pend, &mut transcript);
            }
            events.push('\n');
            transcript.push('\n');
        }
    }
    Scenario {
        name: "failure cap".to_string(),
        events,
        transcript,
    }
}

#[tokio::test]
async fn the_compactor_equals_the_bend_model() {
    let mut rng = Rng(11);
    let mut scenarios = vec![failure_cap()];
    for batch in 0..4 {
        let (mut events, mut transcript) = (String::new(), String::new());
        for _ in 0..500 {
            let (input, replies) = scenario(&mut rng, &mut events);
            let summarizer = Scripted::with(replies);
            let line = build_line(
                summarizer.as_ref(),
                &CompactionPrompt::memory_layer(),
                &NodeRequest {
                    context: "<chat>\n</chat>".to_string(),
                    task: "task".to_string(),
                    input,
                },
                7,
                ResponseStarted::default(),
            )
            .await;
            let shown = match line {
                Ok(line) => line.chars().map(|c| c.len_utf8().to_string()).collect(),
                Err(_) => "!".to_string(),
            };
            let _ = writeln!(transcript, "c={} l={shown}", summarizer.requests().len());
        }
        scenarios.push(Scenario {
            name: format!("batch {batch}"),
            events,
            transcript,
        });
    }
    compare("bridge/bridge_compactor.bend", scenarios);
}
