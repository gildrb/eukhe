//! Outbound anonymization (`privacy.anonymizeRemote`, opt-in, default
//! off): when it is on and the session's model sits behind a
//! non-loopback endpoint, every text the request carries is scrubbed
//! first, and the model's answer is restored before anyone reads it.
//!
//! Two kinds of token:
//!
//! - Mapped (`CLASS_<n>`, one index space per class), for every personal
//!   value: the phrases of `privacy.terms` (`PERSON`), emails, phone
//!   numbers, IP addresses and US social security numbers (`EMAIL`,
//!   `PHONE`, `IP`, `ID`). The map is in memory and append-only: the
//!   same value keeps its index for the daemon's life, and
//!   [`restore_message`] maps every token of the model's answer (text,
//!   thinking, tool call arguments) back, so the transcript, the user
//!   and every tool see the real bytes. A false positive therefore never
//!   reaches a file.
//! - Hashed (`CLASS_<6 hex of the value's SHA-256>`, one way), only for
//!   credentials: API keys and tokens, private key blocks (`KEY`), card
//!   numbers (`CARD`), IBANs (`IBAN`). Their detectors are strict
//!   (vendor prefix, length and mixed characters; network prefix and
//!   Luhn; country length and mod-97).
//!
//! Paths and domains are not scrubbed: a coding model reads them to work
//! (a file you point at, a screenshot's path, an endpoint to deploy). A
//! path says little about you; your own name, domain or username goes in
//! `privacy.terms`.
//!
//! The detectors (`detect.rs`) are hand-written grammars, one per class,
//! that match only well-formed values between word boundaries. The scrub
//! is one left-to-right pass; a literal in the text that reads as a
//! mapped token (`IP_1` in someone's code) is itself mapped, so every
//! token maps back to exactly one value and restoring a scrubbed text
//! gives the text back, byte for byte. The chat memory in `~/.eukhe` is
//! never touched: the scrub runs on the outbound copy only.

mod detect;

#[cfg(test)]
mod corpus_tests;
#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::sync::{LazyLock, Mutex, MutexGuard};

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, Message, SystemContent,
    UserContent, UserContentBlock,
};
use futures::StreamExt;
use sha2::{Digest, Sha256};

use crate::utils::event_stream::AssistantMessageEventStream;
use detect::{is_word, Class};

/// Whether the model's endpoint leaves the machine: loopback hosts
/// (`localhost`, `127.0.0.0/8`, `::1`) are local, everything else is
/// remote.
#[must_use]
pub fn is_local(base_url: &str) -> bool {
    let rest = base_url
        .split_once("://")
        .map_or(base_url, |(_, rest)| rest);
    let authority = rest.split(['/', '?', '#']).next().unwrap_or(rest);
    let host = authority
        .rsplit_once('@')
        .map_or(authority, |(_, host)| host);
    // A bracketed IPv6 keeps its brackets through the port strip.
    let host = if let Some(inner) = host.strip_prefix('[') {
        inner.split(']').next().unwrap_or(inner)
    } else {
        host.split(':').next().unwrap_or(host)
    };
    let host = host.to_ascii_lowercase();
    host == "localhost" || host.starts_with("127.") || host == "::1"
}

/// The one-way token of a credential `value` in `class`: `CLASS_<6 hex>`.
fn pseudonym(class: Class, value: &str) -> String {
    let digest = Sha256::digest(value.as_bytes());
    format!(
        "{}_{:02x}{:02x}{:02x}",
        class.name(),
        digest[0],
        digest[1],
        digest[2]
    )
}

// The map of the mapped classes
// -----------------------------

/// The in-memory map: append-only, one index space per class (from 1),
/// stable for the daemon's life.
#[derive(Default)]
struct Map {
    indexes: HashMap<(Class, String), u32>,
    originals: HashMap<(Class, u32), String>,
    last: HashMap<Class, u32>,
}

static MAP: LazyLock<Mutex<Map>> = LazyLock::new(Mutex::default);

fn map() -> MutexGuard<'static, Map> {
    MAP.lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// The mapped token of `original` in `class` (`PERSON_1`): the existing
/// index when the map holds one, the next free index otherwise.
fn mapped(class: Class, original: &str) -> String {
    let mut map = map();
    if let Some(index) = map.indexes.get(&(class, original.to_owned())) {
        return format!("{}_{index}", class.name());
    }
    let last = map.last.entry(class).or_insert(0);
    *last += 1;
    let index = *last;
    map.indexes.insert((class, original.to_owned()), index);
    map.originals.insert((class, index), original.to_owned());
    format!("{}_{index}", class.name())
}

// The scrubber
// ------------

/// Scrubs one request's text: every detected value becomes its class's
/// token (`detect.rs`).
#[derive(Clone)]
pub struct Scrubber {
    /// The phrases of `privacy.terms`, longest first.
    terms: Vec<Vec<char>>,
}

impl Scrubber {
    /// The scrubber for `terms` (`privacy.terms`): every phrase becomes a
    /// `PERSON_<n>` token at word boundaries, case-insensitively.
    #[must_use]
    pub fn new(terms: &[String]) -> Self {
        let mut terms: Vec<Vec<char>> = terms
            .iter()
            .filter(|term| !term.trim().is_empty())
            .map(|term| term.chars().collect())
            .collect();
        terms.sort_by_key(|term| std::cmp::Reverse(term.len()));
        terms.dedup();
        Self { terms }
    }

    /// Scrub one string in one left-to-right pass: at each position whose
    /// char before (in the output) is no word char, the first class whose
    /// grammar matches replaces the value with its token.
    #[must_use]
    pub fn scrub_str(&self, input: &str) -> String {
        let mut out = String::with_capacity(input.len());
        let mut copied = 0;
        let mut at = 0;
        let mut after_word = false;
        while let Some(c) = input[at..].chars().next() {
            if !after_word {
                if let Some(found) = detect::detect(input, at, &self.terms) {
                    let value_start = at + found.keep;
                    let value = &input[value_start..found.end];
                    out.push_str(&input[copied..value_start]);
                    out.push_str(&if found.class.reversible() {
                        mapped(found.class, value)
                    } else {
                        pseudonym(found.class, value)
                    });
                    copied = found.end;
                    at = found.end;
                    // A token ends in a word char.
                    after_word = true;
                    continue;
                }
            }
            after_word = is_word(c);
            at += c.len_utf8();
        }
        out.push_str(&input[copied..]);
        out
    }

    /// Scrub the text fields of one request's messages. Images are
    /// untouched; tool call arguments are scrubbed per string value.
    #[must_use]
    pub fn scrub_messages(&self, messages: Vec<Message>) -> Vec<Message> {
        messages
            .into_iter()
            .map(|message| match message {
                Message::System(mut system) => {
                    system.content = match system.content {
                        SystemContent::Text(text) => SystemContent::Text(self.scrub_str(&text)),
                        SystemContent::Blocks(blocks) => SystemContent::Blocks(
                            blocks
                                .into_iter()
                                .map(|mut block| {
                                    block.text = self.scrub_str(&block.text);
                                    block
                                })
                                .collect(),
                        ),
                    };
                    Message::System(system)
                }
                Message::User(mut user) => {
                    user.content = match user.content {
                        UserContent::Text(text) => UserContent::Text(self.scrub_str(&text)),
                        UserContent::Blocks(blocks) => UserContent::Blocks(
                            blocks
                                .into_iter()
                                .map(|block| match block {
                                    UserContentBlock::Text(mut text) => {
                                        text.text = self.scrub_str(&text.text);
                                        UserContentBlock::Text(text)
                                    }
                                    other @ UserContentBlock::Image(_) => other,
                                })
                                .collect(),
                        ),
                    };
                    Message::User(user)
                }
                Message::Assistant(mut assistant) => {
                    for block in &mut assistant.content {
                        match block {
                            AssistantContentBlock::Text(text) => {
                                text.text = self.scrub_str(&text.text);
                            }
                            AssistantContentBlock::Thinking(thinking) => {
                                thinking.thinking = self.scrub_str(&thinking.thinking);
                            }
                            AssistantContentBlock::ToolCall(call) => {
                                call.arguments = std::mem::take(&mut call.arguments)
                                    .into_iter()
                                    .map(|(key, value)| (key, self.scrub_json(value)))
                                    .collect();
                            }
                        }
                    }
                    Message::Assistant(assistant)
                }
                Message::ToolResult(mut result) => {
                    result.content = result
                        .content
                        .into_iter()
                        .map(|block| match block {
                            UserContentBlock::Text(mut text) => {
                                text.text = self.scrub_str(&text.text);
                                UserContentBlock::Text(text)
                            }
                            other @ UserContentBlock::Image(_) => other,
                        })
                        .collect();
                    result.details = result.details.map(|details| self.scrub_json(details));
                    Message::ToolResult(result)
                }
            })
            .collect()
    }

    /// Scrub every string in a JSON tree (keys stay).
    #[must_use]
    pub fn scrub_json(&self, value: serde_json::Value) -> serde_json::Value {
        match value {
            serde_json::Value::String(text) => serde_json::Value::String(self.scrub_str(&text)),
            serde_json::Value::Array(items) => serde_json::Value::Array(
                items
                    .into_iter()
                    .map(|item| self.scrub_json(item))
                    .collect(),
            ),
            serde_json::Value::Object(map) => serde_json::Value::Object(
                map.into_iter()
                    .map(|(key, value)| (key, self.scrub_json(value)))
                    .collect(),
            ),
            other => other,
        }
    }
}

// The restore
// -----------

/// Map every mapped token of `text` back to its value: the inverse of
/// [`Scrubber::scrub_str`] on every reversible class. A token is read
/// where the scrub writes one (no word char before or after); a token
/// the map does not hold, and every one-way token, stays as it is.
#[must_use]
pub fn restore(text: &str) -> String {
    if !text.contains('_') {
        return text.to_owned();
    }
    let map = map();
    let mut out = String::with_capacity(text.len());
    let mut copied = 0;
    let mut at = 0;
    let mut after_word = false;
    while let Some(c) = text[at..].chars().next() {
        if !after_word {
            let original = detect::token_at(text, at).and_then(|(class, end)| {
                let index = text[at + class.name().len() + 1..end].parse::<u32>().ok()?;
                map.originals
                    .get(&(class, index))
                    .map(|original| (original, end))
            });
            if let Some((original, end)) = original {
                out.push_str(&text[copied..at]);
                out.push_str(original);
                copied = end;
                at = end;
                after_word = true;
                continue;
            }
        }
        after_word = is_word(c);
        at += c.len_utf8();
    }
    out.push_str(&text[copied..]);
    out
}

/// [`restore`] every string in a JSON tree (keys stay).
#[must_use]
pub fn restore_json(value: serde_json::Value) -> serde_json::Value {
    match value {
        serde_json::Value::String(text) => serde_json::Value::String(restore(&text)),
        serde_json::Value::Array(items) => {
            serde_json::Value::Array(items.into_iter().map(restore_json).collect())
        }
        serde_json::Value::Object(map) => serde_json::Value::Object(
            map.into_iter()
                .map(|(key, value)| (key, restore_json(value)))
                .collect(),
        ),
        other => other,
    }
}

/// The model's answer to a scrubbed request with every mapped token
/// restored: its text, its thinking and its tool calls' arguments, so a
/// tool runs against the real strings and the transcript keeps them.
#[must_use]
pub fn restore_message(mut message: AssistantMessage) -> AssistantMessage {
    for block in &mut message.content {
        match block {
            AssistantContentBlock::Text(text) => text.text = restore(&text.text),
            AssistantContentBlock::Thinking(thinking) => {
                thinking.thinking = restore(&thinking.thinking);
            }
            AssistantContentBlock::ToolCall(call) => {
                call.arguments = std::mem::take(&mut call.arguments)
                    .into_iter()
                    .map(|(key, value)| (key, restore_json(value)))
                    .collect();
            }
        }
    }
    message
}

/// The stream of a scrubbed request as its reader sees it: every event of
/// `source` in order, the terminal message (`done`, `error`) restored
/// ([`restore_message`]). The live partial and its deltas stay as the
/// model wrote them; the terminal message is the one the transcript keeps
/// and the tools run. Must be called inside a tokio runtime.
#[must_use]
pub fn restore_stream(source: AssistantMessageEventStream) -> AssistantMessageEventStream {
    let out = AssistantMessageEventStream::new();
    let target = out.clone();
    tokio::spawn(async move {
        let mut events = source.events();
        while let Some(event) = events.next().await {
            target.push(match event {
                AssistantMessageEvent::Done { reason, message } => AssistantMessageEvent::Done {
                    reason,
                    message: restore_message(message),
                },
                AssistantMessageEvent::Error { reason, error } => AssistantMessageEvent::Error {
                    reason,
                    error: restore_message(error),
                },
                other @ (AssistantMessageEvent::Start { .. }
                | AssistantMessageEvent::PromptProgress { .. }
                | AssistantMessageEvent::TextStart { .. }
                | AssistantMessageEvent::TextDelta { .. }
                | AssistantMessageEvent::TextEnd { .. }
                | AssistantMessageEvent::ThinkingStart { .. }
                | AssistantMessageEvent::ThinkingDelta { .. }
                | AssistantMessageEvent::ThinkingEnd { .. }
                | AssistantMessageEvent::ToolCallStart { .. }
                | AssistantMessageEvent::ToolCallDelta { .. }
                | AssistantMessageEvent::ToolCallEnd { .. }) => other,
            });
        }
        target.end(None);
    });
    out
}
