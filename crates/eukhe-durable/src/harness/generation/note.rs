//! The note at the end of a retry's request (docs/harness.md H4.7, H4.8,
//! laws `run_retry_sends_a_new_request`, `run_note_is_never_logged` and
//! the `rec_*` laws).
//!
//! A model decodes the same request the same way, and a greedy one always
//! does. After a noted reply (the repetition guard cut the stream, the
//! reply had no text and no tool call, or a recovery of H4.8 stopped it),
//! the retry must not send the request again: its request ends with a note
//! that names the retry's attempt and what went wrong
//! ([`retry_note`](super::decide::retry_note)). The note goes out with the
//! request only, as the soft prompt of a forced call does: the run never
//! commits it, so the transcript never logs it as the user's words.

use serde::{Deserialize, Serialize};

use super::decide::{LEAK_NOTES, LENGTH_NOTES, REDIRECT_NOTES};

/// What went wrong with a noted reply.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum NoteCause {
    /// The repetition guard cut the stream: it repeated a cycle of
    /// `period` lines (1: one line) that ends with `line`.
    Repeated { period: u32, line: String },
    /// The reply had no text and no tool call.
    NoAnswer,
    /// The reply hit the output limit (`tokens`, 0 when the provider
    /// reported none) while it still reasoned: no text and no tool call.
    /// `row`: the length notes in a row, this one included.
    Length { tokens: u64, row: u32 },
    /// The reply wrote tool calls as `markup` text that the harness could
    /// not rebuild, for `reason`. `row`: the leak notes in a row.
    Leaked {
        markup: String,
        reason: String,
        row: u32,
    },
    /// The reply made `calls` and would have made `rounds` rounds in a row
    /// with the same calls and the same results. `row`: the redirect notes
    /// in a row.
    Redirect {
        calls: Vec<RepeatedCall>,
        rounds: u32,
        row: u32,
    },
}

/// One call of a repeated round: its tool and its arguments (their
/// canonical JSON, cut to [`ARGUMENTS_SHOWN`] characters).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RepeatedCall {
    pub(crate) tool: String,
    pub(crate) arguments: String,
}

/// The characters of a repeated call's arguments that its note shows
/// (omp `ARGUMENT_SUMMARY_LIMIT`).
pub(crate) const ARGUMENTS_SHOWN: usize = 400;

/// A recovery that counts its notes in a row (H4.8).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Recovery {
    Length,
    Leak,
    Redirect,
}

impl NoteCause {
    /// The notes of `recovery` in a row that this note makes: its row when
    /// it is a note of that recovery, else 0.
    pub(crate) fn row(&self, recovery: Recovery) -> u32 {
        match (self, recovery) {
            (Self::Length { row, .. }, Recovery::Length)
            | (Self::Leaked { row, .. }, Recovery::Leak)
            | (Self::Redirect { row, .. }, Recovery::Redirect) => *row,
            (
                Self::Repeated { .. }
                | Self::NoAnswer
                | Self::Leaked { .. }
                | Self::Redirect { .. },
                Recovery::Length,
            )
            | (
                Self::Repeated { .. }
                | Self::NoAnswer
                | Self::Length { .. }
                | Self::Redirect { .. },
                Recovery::Leak,
            )
            | (
                Self::Repeated { .. } | Self::NoAnswer | Self::Length { .. } | Self::Leaked { .. },
                Recovery::Redirect,
            ) => 0,
        }
    }
}

/// The note of a retry: the attempt it names and what went wrong.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RetryNote {
    /// The retry's attempt (1 for a generation's first request).
    pub(crate) attempt: u64,
    pub(crate) cause: NoteCause,
    /// The noted retries of the generation so far, this one included:
    /// what they spent of [`MAX_NOTES`](super::decide::MAX_NOTES).
    #[serde(default)]
    pub(crate) spent: u32,
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
            NoteCause::Length { tokens, row } => {
                let limit = match tokens {
                    0 => "the output limit".to_owned(),
                    tokens => format!("the {tokens}-token output limit"),
                };
                format!(
                    "Harness note, attempt {attempt}: your previous reply hit {limit} while it \
                     was still reasoning. It gave no text and no tool call, so the harness \
                     discarded it with every tool call that it planned. If you plan the whole \
                     task again in your reasoning, you hit the same limit. Reason only about the \
                     next step, then call its tool. For a large answer (a file, a document, a \
                     long text), write a minimal working version first, then extend it with \
                     more edits in later turns. Length note {row} of {LENGTH_NOTES}."
                )
            }
            NoteCause::Leaked {
                markup,
                reason,
                row,
            } => format!(
                "Harness note, attempt {attempt}: your previous reply wrote a tool call as \
                 {markup} markup in its text, and the harness could not read it ({reason}). No \
                 tool ran. Make the call again through the tool-calling interface, with its \
                 arguments as one JSON object that agrees with the schema of the tool. Do not \
                 write a tool call as text. If you need no tool, give the answer as plain text. \
                 Leak note {row} of {LEAK_NOTES}."
            ),
            NoteCause::Redirect { calls, rounds, row } => {
                let listed = calls
                    .iter()
                    .map(|call| format!("`{}` with `{}`", call.tool, call.arguments))
                    .collect::<Vec<_>>()
                    .join("; ");
                format!(
                    "Harness note, attempt {attempt}: you made the same tool calls {rounds} \
                     times in a row, and they gave the same results each time: {listed}. The \
                     harness did not run them again. Do not make these calls with these \
                     arguments again in this turn. Use different arguments, use a different \
                     tool, or give your answer with what you found. Redirect note {row} of \
                     {REDIRECT_NOTES}."
                )
            }
        }
    }
}
