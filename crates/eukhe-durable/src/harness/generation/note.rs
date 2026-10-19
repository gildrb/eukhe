//! The note at the end of a retry's request (docs/harness.md H4.7, laws
//! `run_retry_sends_a_new_request` and `run_note_is_never_logged`).
//!
//! A model decodes the same request the same way, and a greedy one always
//! does. After a noted reply (the repetition guard cut the stream, or the
//! reply had no text and no tool call), the retry must not send the request
//! again: its request ends with a note that names the retry's attempt and
//! what went wrong ([`retry_note`](super::decide::retry_note)). The note
//! goes out with the request only, as the soft prompt of a forced call
//! does: the run never commits it, so the transcript never logs it as the
//! user's words.

use serde::{Deserialize, Serialize};

/// What went wrong with a noted reply.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum NoteCause {
    /// The repetition guard cut the stream: it repeated a cycle of
    /// `period` lines (1: one line) that ends with `line`.
    Repeated { period: u32, line: String },
    /// The reply had no text and no tool call.
    NoAnswer,
}

/// The note of a retry: the attempt it names and what went wrong.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RetryNote {
    /// The retry's attempt (1 for a generation's first request).
    pub(crate) attempt: u64,
    pub(crate) cause: NoteCause,
}

impl RetryNote {
    /// The text of the note: the last user message of the request, before
    /// the soft prompt of a forced call.
    pub(crate) fn text(&self) -> String {
        let attempt = self.attempt;
        match &self.cause {
            NoteCause::Repeated { period: 1, line } => format!(
                "Harness note, attempt {attempt}: your previous reply repeated the line {line:?} \
                 until it was cut. Give the answer again; never list the same item twice."
            ),
            NoteCause::Repeated { period, line } => format!(
                "Harness note, attempt {attempt}: your previous reply repeated a cycle of \
                 {period} lines, ending with the line {line:?}, until it was cut. Give the \
                 answer again; never repeat the same lines."
            ),
            NoteCause::NoAnswer => format!(
                "Harness note, attempt {attempt}: your previous reply gave no text and no tool \
                 call. Give the answer again, as text or as a tool call."
            ),
        }
    }
}
