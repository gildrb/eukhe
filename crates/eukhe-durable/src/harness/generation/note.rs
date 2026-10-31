//! The note at the end of a retry's request (LAWS.bend H4.7, H4.8,
//! laws `run_retry_sends_a_new_request`, `run_note_is_never_logged` and
//! the `rec_*` laws).
//!
//! A model decodes the same request the same way, and a greedy one always
//! does. After a noted reply (the repetition guard cut the stream, the
//! stream stalled, the reply had no text and no tool call, or a recovery
//! of H4.8 stopped it), the retry must not send the request again: its
//! request ends with a note that names the retry's attempt and what went
//! wrong ([`retry_note`](super::decide::retry_note)). The note goes out with the
//! request only, as the soft prompt of a forced call does: the run never
//! commits it, so the transcript never logs it as the user's words. The
//! compiled Bend core writes the note's text (`bend/retry_note.bend`,
//! `laws/retry_note.bend`).

use eukhe_bend::rules::retry_note::{self, Call, Cause};
use eukhe_bend::wire::NAT_MAX;
use eukhe_bend::{expect_core, Entry};
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
    /// The stream sent no event for `idle_ms` (its idle deadline), so the
    /// harness cut it (M3). The retry has twice that deadline
    /// ([`idle_after_stall`](super::deferred::idle_after_stall)).
    Stalled { idle_ms: u64 },
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
    /// The recovery whose notes in a row this note counts, and its row
    /// (this note included); None for a note of no recovery.
    pub(crate) fn recovery(&self) -> Option<(Recovery, u32)> {
        match self {
            Self::Length { row, .. } => Some((Recovery::Length, *row)),
            Self::Leaked { row, .. } => Some((Recovery::Leak, *row)),
            Self::Redirect { row, .. } => Some((Recovery::Redirect, *row)),
            Self::Repeated { .. } | Self::NoAnswer | Self::Stalled { .. } => None,
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
    /// the soft prompt of a forced call. The compiled core writes it
    /// (`eukhe_bend::rules::retry_note`, law `retry_note_exact`); the host
    /// quotes a repeated line (`{:?}`), gives each recovery's cap, and
    /// saturates a count past the wire's bound.
    ///
    /// # Panics
    ///
    /// On a text past the core's wire bound (8 Mi chars) or an inconsistent
    /// build ([`expect_core`]).
    pub(crate) fn text(&self) -> String {
        let quoted;
        let listed;
        let cause = match &self.cause {
            NoteCause::Repeated { period, line } => {
                quoted = format!("{line:?}");
                Cause::Repeated {
                    period: *period,
                    line: &quoted,
                }
            }
            NoteCause::NoAnswer => Cause::NoAnswer,
            NoteCause::Length { tokens, row } => Cause::Length {
                tokens: (*tokens).min(NAT_MAX),
                row: *row,
                cap: LENGTH_NOTES,
            },
            NoteCause::Leaked {
                markup,
                reason,
                row,
            } => Cause::Leaked {
                markup,
                reason,
                row: *row,
                cap: LEAK_NOTES,
            },
            NoteCause::Redirect { calls, rounds, row } => {
                listed = calls
                    .iter()
                    .map(|call| Call {
                        tool: &call.tool,
                        arguments: &call.arguments,
                    })
                    .collect::<Vec<_>>();
                Cause::Redirect {
                    calls: &listed,
                    rounds: *rounds,
                    row: *row,
                    cap: REDIRECT_NOTES,
                }
            }
            NoteCause::Stalled { idle_ms } => Cause::Stalled {
                idle_ms: (*idle_ms).min(NAT_MAX),
            },
        };
        expect_core(
            Entry::RetryNote,
            retry_note::text(self.attempt.min(NAT_MAX), &cause),
        )
    }
}
