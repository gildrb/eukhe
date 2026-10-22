//! The row a turn that ended without an answer leaves, live and rebuilt
//! alike (`LAWS.bend` section `turn_visibility` R4, R5, R7): a failure the chat does
//! not show yet gets its failure row, and a turn with no reply at all says
//! so. Both rows name the user's next step. The live event pump pushes them
//! at the turn's end; the transcript rebuild folds the same rows from the
//! stored messages ([`TurnFold`]).

use super::{AssistantMessage, ChatEntry, TurnOutcome};
use crate::chat::StatusKind;
use crate::glyphs::{SEP, WARN};

/// The failure row of a turn whose failure the chat does not show yet:
/// the failed-attempt row shape (an error-only assistant entry), so it
/// renders the failure's next step and a retry episode's outcome row
/// replaces it like any failed attempt.
pub(crate) fn failure_row(error: &str) -> ChatEntry {
    ChatEntry::Assistant(Box::new(AssistantMessage {
        blocks: Vec::new(),
        has_tool_calls: false,
        streaming: false,
        error: Some(format!("Error: {error}")),
        aborted: false,
    }))
}

/// The row of a turn that ended with no reply and no failure to show: a
/// blank answer, a turn the engine reported nothing for, or a run that
/// ended before its turn answered.
pub(crate) fn no_reply_row() -> ChatEntry {
    let step = crate::error_summary::failure_next_step("").unwrap_or_default();
    ChatEntry::Status {
        text: format!("{WARN} The turn ended without a reply{SEP}{step}"),
        kind: StatusKind::Warning,
    }
}

/// Whether the transcript's newest turn may still run: the attach
/// snapshot's run is open (`isStreaming`), or the transcript was fetched
/// without that state (the post-compaction re-fetch).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnTail {
    /// The newest turn may still answer: its end row is not folded.
    Running,
    /// No run is open: the newest turn ended, and its end row folds.
    Ended,
}

/// Where a stored turn ends in the transcript.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum TurnBoundary {
    /// The next user message: a turn that called tools or has no
    /// assistant message yet may go on past it (a steering or batched
    /// prompt lands mid-run), so only a settled last message decides.
    NextPrompt,
    /// The transcript's end with no run open: the turn is over.
    RunEnded,
}

/// One stored turn being folded, from its user message on: how its newest
/// assistant message settled and whether a retry episode's outcome row
/// followed that message.
#[derive(Debug, Default)]
pub(super) struct TurnFold {
    last: Option<(TurnOutcome, bool)>,
    outcome_after: bool,
}

impl TurnFold {
    /// An assistant message of the turn.
    pub(super) fn assistant(&mut self, message: &eukhe_types::ai::AssistantMessage) {
        let (_, tool_calls) = super::assistant_message_parts(message);
        self.last = Some((
            super::decoder::message_outcome(message),
            !tool_calls.is_empty(),
        ));
        self.outcome_after = false;
    }

    /// A `provider_retry_outcome` row: the episode's one line now shows its
    /// failure.
    pub(super) fn outcome(&mut self) {
        self.outcome_after = true;
    }

    /// The row the turn leaves at `boundary`, the one the live event pump
    /// pushed at its end (`apply.rs` `TurnEnded` and `Idle`).
    pub(super) fn end(self, boundary: TurnBoundary) -> Option<ChatEntry> {
        match self.last {
            // No answer yet, or a tool round with no answering turn after
            // it: over only when the run is.
            None | Some((TurnOutcome::Continues, _)) => match boundary {
                TurnBoundary::RunEnded => Some(no_reply_row()),
                TurnBoundary::NextPrompt => None,
            },
            Some((TurnOutcome::Empty | TurnOutcome::Unreported, _)) => Some(no_reply_row()),
            // A failure whose tool cards carry it shows no row of its own;
            // an outcome row after it is the one line.
            Some((TurnOutcome::Failed(error), true)) if !self.outcome_after => {
                Some(failure_row(&error))
            }
            Some((TurnOutcome::Failed(_) | TurnOutcome::Answered | TurnOutcome::Aborted, _)) => {
                None
            }
        }
    }
}
