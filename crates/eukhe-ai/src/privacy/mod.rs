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
//!   `PHONE`, `IP`, `ID`). The map runs as the compiled core
//!   (`bend/privacy/token.bend`, laws `laws/privacy/token.bend`), in
//!   memory and append-only, one map per session ([`TokenMap`]: it opens
//!   empty with the session and goes with it): the same value keeps its
//!   index for the session's life, each session numbers its values from
//!   1, and [`TokenMap::restore_message`] maps every token of the model's
//!   answer (text, thinking, tool call arguments) back with the map of the
//!   session that sent the request, so the transcript, the user and every
//!   tool see the real bytes, and no session's answer ever brings back a
//!   value another session scrubbed. A false positive therefore never
//!   reaches a file.
//! - Hashed (`CLASS_<6 hex of the value's SHA-256>`, one way), only for
//!   credentials: API keys and tokens, private key blocks (`KEY`), card
//!   numbers (`CARD`), IBANs (`IBAN`). Their detectors are strict
//!   (vendor prefix, length and mixed characters; network prefix and
//!   Luhn; country length and mod-97). Which classes map back is the
//!   core's: it answers them when the map opens.
//!
//! Paths and domains are not scrubbed: a coding model reads them to work
//! (a file you point at, a screenshot's path, an endpoint to deploy). A
//! path says little about you; your own name, domain or username goes in
//! `privacy.terms`.
//!
//! The detectors (`detect.rs`) are hand-written grammars, one per class,
//! that match only well-formed values between word boundaries (the IP
//! addresses are the compiled core's, `bend/privacy/ip.bend`). The scrub
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

use std::sync::{Arc, Mutex, MutexGuard};

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, Message, SystemContent,
    UserContent, UserContentBlock,
};
use futures::StreamExt;
use sha2::{Digest, Sha256};

use crate::utils::event_stream::AssistantMessageEventStream;
use detect::{is_word, Ips};
use eukhe_bend::rules::privacy::{Class, Token, Tokens};

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

/// The token map of one session, kept in the compiled core: it opens
/// empty, is append-only, has one index space per class (from 1) and is
/// stable for the session's life. Clones share the map: the session holds
/// it, and each request's scrub and its answer's restore (on whatever
/// thread the answer arrives) take a clone; it is dropped with the last.
#[derive(Clone, Default)]
pub struct TokenMap {
    tokens: Arc<Mutex<Tokens>>,
}

impl TokenMap {
    fn lock(&self) -> MutexGuard<'_, Tokens> {
        self.tokens
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

// The scrubber
// ------------

/// Scrubs one request's text: every detected value becomes its class's
/// token (`detect.rs`), numbered in the session's map.
#[derive(Clone)]
pub struct Scrubber {
    /// The phrases of `privacy.terms`, longest first.
    terms: Vec<Vec<char>>,
    /// The map of the session the request belongs to.
    tokens: TokenMap,
}

impl Scrubber {
    /// The scrubber for `terms` (`privacy.terms`) of the session whose map
    /// is `tokens`: every phrase becomes a `PERSON_<n>` token at word
    /// boundaries, case-insensitively.
    #[must_use]
    pub fn new(terms: &[String], tokens: TokenMap) -> Self {
        let mut terms: Vec<Vec<char>> = terms
            .iter()
            .filter(|term| !term.trim().is_empty())
            .map(|term| term.chars().collect())
            .collect();
        terms.sort_by_key(|term| std::cmp::Reverse(term.len()));
        terms.dedup();
        Self { terms, tokens }
    }

    /// The map of the session this scrubber numbers values in.
    #[must_use]
    pub fn tokens(&self) -> &TokenMap {
        &self.tokens
    }

    /// Scrub one string in one left-to-right pass: at each position whose
    /// char before (in the output) is no word char, the first class whose
    /// grammar matches replaces the value with its token. One call to the
    /// core decides the string's IP addresses, one step asks the tokens
    /// of its values.
    #[must_use]
    pub fn scrub_str(&self, input: &str) -> String {
        let mut tokens = self.tokens.lock();
        let ips = Ips::of(input);
        // Each value: where it starts, where it ends, its class.
        let mut found = Vec::new();
        let mut at = 0;
        let mut after_word = false;
        while let Some(c) = input[at..].chars().next() {
            if !after_word {
                if let Some(value) = detect::detect(input, at, &self.terms, &ips, tokens.mapped()) {
                    found.push((at + value.keep, value.end, value.class));
                    at = value.end;
                    // A token ends in a word char.
                    after_word = true;
                    continue;
                }
            }
            after_word = is_word(c);
            at += c.len_utf8();
        }
        if found.is_empty() {
            return input.to_owned();
        }
        let values: Vec<(Class, &str)> = found
            .iter()
            .map(|&(start, end, class)| (class, &input[start..end]))
            .collect();
        // A value longer than the wire carries (never a real one) goes one
        // way: nothing of it leaves in clear.
        let asked = tokens
            .scrub(&values)
            .unwrap_or_else(|_| vec![Token::OneWay; values.len()]);
        let mut out = String::with_capacity(input.len());
        let mut copied = 0;
        for (&(start, end, class), token) in found.iter().zip(asked) {
            out.push_str(&input[copied..start]);
            match token {
                Token::Mapped(index) => {
                    out.push_str(class.name());
                    out.push('_');
                    out.push_str(&index.to_string());
                }
                Token::OneWay => out.push_str(&pseudonym(class, &input[start..end])),
            }
            copied = end;
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

impl TokenMap {
    /// Map every mapped token of `text` back to its value in this
    /// session's map: the inverse of [`Scrubber::scrub_str`] on every
    /// reversible class. A token is read where the scrub writes one (no
    /// word char before or after); a token the map does not hold (one
    /// this session never issued), and every one-way token, stays as it
    /// is. One step asks the core the values of the text's tokens.
    #[must_use]
    pub fn restore(&self, text: &str) -> String {
        if !text.contains('_') {
            return text.to_owned();
        }
        let mut tokens = self.lock();
        // Each token: where it starts, where it ends, its class and index.
        let mut found = Vec::new();
        let mut at = 0;
        let mut after_word = false;
        while let Some(c) = text[at..].chars().next() {
            if !after_word {
                let token = detect::token_at(text, at, tokens.mapped()).and_then(|(class, end)| {
                    let index = text[at + class.name().len() + 1..end].parse::<u32>().ok()?;
                    Some((at, end, class, index))
                });
                if let Some(token) = token {
                    found.push(token);
                    at = token.1;
                    after_word = true;
                    continue;
                }
            }
            after_word = is_word(c);
            at += c.len_utf8();
        }
        if found.is_empty() {
            return text.to_owned();
        }
        let asked: Vec<(Class, u32)> = found
            .iter()
            .map(|&(_, _, class, index)| (class, index))
            .collect();
        let values = tokens.restore(&asked);
        let mut out = String::with_capacity(text.len());
        let mut copied = 0;
        for ((start, end, _, _), value) in found.into_iter().zip(values) {
            if let Some(value) = value {
                out.push_str(&text[copied..start]);
                out.push_str(&value);
                copied = end;
            }
        }
        out.push_str(&text[copied..]);
        out
    }

    /// [`Self::restore`] every string in a JSON tree (keys stay).
    #[must_use]
    pub fn restore_json(&self, value: serde_json::Value) -> serde_json::Value {
        match value {
            serde_json::Value::String(text) => serde_json::Value::String(self.restore(&text)),
            serde_json::Value::Array(items) => serde_json::Value::Array(
                items
                    .into_iter()
                    .map(|item| self.restore_json(item))
                    .collect(),
            ),
            serde_json::Value::Object(map) => serde_json::Value::Object(
                map.into_iter()
                    .map(|(key, value)| (key, self.restore_json(value)))
                    .collect(),
            ),
            other => other,
        }
    }

    /// The model's answer to a scrubbed request of this session with every
    /// mapped token restored: its text, its thinking and its tool calls'
    /// arguments, so a tool runs against the real strings and the
    /// transcript keeps them.
    #[must_use]
    pub fn restore_message(&self, mut message: AssistantMessage) -> AssistantMessage {
        for block in &mut message.content {
            match block {
                AssistantContentBlock::Text(text) => text.text = self.restore(&text.text),
                AssistantContentBlock::Thinking(thinking) => {
                    thinking.thinking = self.restore(&thinking.thinking);
                }
                AssistantContentBlock::ToolCall(call) => {
                    call.arguments = std::mem::take(&mut call.arguments)
                        .into_iter()
                        .map(|(key, value)| (key, self.restore_json(value)))
                        .collect();
                }
            }
        }
        message
    }

    /// The stream of a scrubbed request of this session as its reader sees
    /// it: every event of `source` in order, the terminal message (`done`,
    /// `error`) restored ([`Self::restore_message`]) with this session's
    /// map, whatever thread the task runs on. The live partial and its
    /// deltas stay as the model wrote them; the terminal message is the one
    /// the transcript keeps and the tools run. Must be called inside a
    /// tokio runtime.
    #[must_use]
    pub fn restore_stream(
        &self,
        source: AssistantMessageEventStream,
    ) -> AssistantMessageEventStream {
        let out = AssistantMessageEventStream::new();
        let target = out.clone();
        let map = self.clone();
        tokio::spawn(async move {
            let mut events = source.events();
            while let Some(event) = events.next().await {
                target.push(match event {
                    AssistantMessageEvent::Done { reason, message } => {
                        AssistantMessageEvent::Done {
                            reason,
                            message: map.restore_message(message),
                        }
                    }
                    AssistantMessageEvent::Error { reason, error } => {
                        AssistantMessageEvent::Error {
                            reason,
                            error: map.restore_message(error),
                        }
                    }
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
}
