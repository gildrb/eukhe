//! The rows a turn leaves at its end, live and rebuilt alike (`LAWS.bend`
//! section `turn_visibility` R4, R5, R7): a failure the chat does not
//! show yet gets its failure row, a turn with no reply at all says so,
//! and a turn that used tokens closes with its usage footer
//! ([`crate::turn_usage`]). The live event pump pushes them at the turn's
//! end; the transcript rebuild folds the same rows from the stored
//! messages ([`TurnFold`]).

use super::{AssistantMessage, ChatEntry, TurnOutcome};
use crate::chat::StatusKind;
use crate::glyphs::{SEP, WARN};
use crate::turn_usage::TurnUsage;

/// The failure row of a turn whose failure the chat does not show yet:
/// the failed-attempt row shape (an error-only assistant entry), so it
/// renders the failure's report and a retry episode's outcome row
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
    let report = crate::error_summary::failure_report("", None).unwrap_or_default();
    ChatEntry::Status {
        text: format!("{WARN} The turn ended without a reply{SEP}{report}"),
        kind: StatusKind::Warning,
    }
}

/// The row of a run the user stopped before its turn answered (an abort
/// during the tools): the aborted-message row shape, carrying `text`
/// (`crate::chat::live_abort_text`).
pub(crate) fn aborted_row(text: String) -> ChatEntry {
    ChatEntry::Assistant(Box::new(AssistantMessage {
        blocks: Vec::new(),
        has_tool_calls: false,
        streaming: false,
        error: Some(text),
        aborted: true,
    }))
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
/// assistant message settled, whether a retry episode's outcome row
/// followed that message, and the usage of its messages so far (a turn
/// that may go on past the next prompt carries it there).
#[derive(Debug, Default)]
pub(super) struct TurnFold {
    last: Option<(TurnOutcome, bool)>,
    outcome_after: bool,
    usage: TurnUsage,
}

impl TurnFold {
    /// A turn that starts with the usage an unfinished turn carried.
    pub(super) fn carrying(usage: TurnUsage) -> Self {
        Self {
            usage,
            ..Self::default()
        }
    }

    /// An assistant message of the turn; `counted` is false for the open
    /// run's in-flight partial, whose `message_end` the live pump counts.
    pub(super) fn assistant(&mut self, message: &eukhe_types::ai::AssistantMessage, counted: bool) {
        let (_, tool_calls) = super::assistant_message_parts(message);
        self.last = Some((
            super::decoder::message_outcome(message),
            !tool_calls.is_empty(),
        ));
        self.outcome_after = false;
        if counted {
            self.usage.add_message(message);
        }
    }

    /// A tool result of the turn that reported an error.
    pub(super) fn tool_failed(&mut self) {
        self.usage.tool_failed();
    }

    /// A `provider_retry_outcome` row: the episode's one line now shows its
    /// failure.
    pub(super) fn outcome(&mut self) {
        self.outcome_after = true;
    }

    /// The usage the turn's messages have added so far.
    pub(super) fn usage(&self) -> TurnUsage {
        self.usage
    }

    /// The rows the turn leaves at `boundary`, the ones the live event
    /// pump pushed at its end (`apply.rs` `TurnEnded` and `Idle`): its end
    /// row, then its usage footer. A turn that may go on past the next
    /// prompt leaves nothing yet and hands its usage on (the second
    /// value).
    pub(super) fn end(self, boundary: TurnBoundary) -> (Vec<ChatEntry>, TurnUsage) {
        let row = match self.last {
            // No answer yet, or a tool round with no answering turn after
            // it: over only when the run is.
            None | Some((TurnOutcome::Continues, _)) => match boundary {
                TurnBoundary::RunEnded => Some(no_reply_row()),
                TurnBoundary::NextPrompt => return (Vec::new(), self.usage),
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
        };
        let footer = turn_footer(self.usage);
        (
            row.into_iter().chain(footer).collect(),
            TurnUsage::default(),
        )
    }
}

/// The usage footer of a turn that ended, when it used any tokens.
pub(crate) fn turn_footer(usage: TurnUsage) -> Option<ChatEntry> {
    (!usage.is_empty()).then(|| ChatEntry::TurnFooter(Box::new(usage)))
}
