//! The headless terminal selection over the durable transcript (the
//! selection half of TS `headless-completion.ts` + the text-output half of
//! `print-mode.ts`): walk the main conversation newest-first, collect the
//! trailing compaction outcomes and the warning of a truncated answer, skip
//! internal notices and replies out of the model's context, and take the
//! first substantive entry (an assistant answer or a slash-command result)
//! as the primary.

use std::collections::HashSet;

use eukhe_bend::rules::headless::Primary;
use eukhe_chord::context::Context;
use eukhe_core::durable::messages::{
    COMPACTION_OUTCOME_CUSTOM_TYPE, HARNESS_DIGEST_CUSTOM_TYPE, PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE,
    REFINEMENT_NOTICE_CUSTOM_TYPE, REFINEMENT_OUTCOME_CUSTOM_TYPE,
    SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
};
use eukhe_core::durable::{custom_entry_content, CUSTOM_ENTRY};
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::types::{ContextEditAction, EntryId, EntryRecord};
use eukhe_types::custom_type::OUTPUT_LIMIT_NOTICE_CUSTOM_TYPE;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Message, StopReason, UserContent,
};

/// Entries read per page while walking the transcript backwards.
const PAGE: usize = 64;

/// The primary terminal result of a headless run.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum HeadlessPrimary {
    /// The final assistant message.
    Assistant(Box<AssistantMessage>),
    /// A session slash-command result row.
    SlashCommandResult {
        content: String,
        success: bool,
        severity: Option<String>,
    },
}

impl HeadlessPrimary {
    /// Stdout content.
    pub(crate) fn stdout_text(&self) -> String {
        match self {
            Self::Assistant(message) => message
                .content
                .iter()
                .filter_map(|block| match block {
                    AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                    AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
                })
                .collect(),
            Self::SlashCommandResult { content, .. } => content.clone(),
        }
    }

    /// Whether the run exits non-zero, and what it prints to stderr.
    pub(crate) fn failure(&self) -> Option<RunFailure> {
        match self {
            Self::Assistant(message) => match message.stop_reason {
                StopReason::Error | StopReason::Aborted => Some(RunFailure::Message(
                    message
                        .error_message
                        .clone()
                        .filter(|text| !text.is_empty())
                        .unwrap_or_else(|| {
                            format!("Request {}", stop_reason_name(message.stop_reason))
                        }),
                )),
                StopReason::Stop
                | StopReason::Length
                | StopReason::ToolUse
                | StopReason::Pending
                | StopReason::Deferred => None,
            },
            Self::SlashCommandResult {
                success, severity, ..
            } => (!success || severity.as_deref() == Some("error")).then_some(RunFailure::Silent),
        }
    }

    /// The primary as the exit rule's fact (`headless_exit`).
    pub(crate) fn kind(&self) -> Primary {
        match self {
            Self::Assistant(message) => match message.stop_reason {
                StopReason::Stop | StopReason::Length => Primary::Answer,
                StopReason::ToolUse | StopReason::Pending | StopReason::Deferred => {
                    Primary::Unfinished
                }
                StopReason::Error => Primary::ProviderError,
                StopReason::Aborted => Primary::Aborted,
            },
            Self::SlashCommandResult {
                success, severity, ..
            } => {
                if *success && severity.as_deref() != Some("error") {
                    Primary::SlashOk
                } else {
                    Primary::SlashFailed
                }
            }
        }
    }
}

/// A failed run's stderr: the failed or aborted request's text, or nothing
/// (a failed slash command already showed its result).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RunFailure {
    Message(String),
    Silent,
}

fn stop_reason_name(reason: StopReason) -> &'static str {
    match reason {
        StopReason::Stop => "stop",
        StopReason::Length => "length",
        StopReason::ToolUse => "tool_use",
        StopReason::Error => "error",
        StopReason::Aborted => "aborted",
        StopReason::Pending => "pending",
        StopReason::Deferred => "deferred",
    }
}

/// One compaction outcome trailing the terminal result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompactionOutcome {
    pub content: String,
    pub outcome: String,
}

/// The selected terminal result.
#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct HeadlessTerminalResult {
    pub primary: Option<HeadlessPrimary>,
    pub compaction_outcomes: Vec<CompactionOutcome>,
    /// The warnings trailing the primary, oldest first: the answer hit the
    /// output limit and is truncated.
    pub warnings: Vec<String>,
}

/// What one transcript entry means for the selection.
enum Step {
    /// A trailing compaction outcome.
    Outcome(CompactionOutcome),
    /// A trailing warning about the answer it follows.
    Warning(String),
    /// Bookkeeping or an internal notice: keep walking.
    Skip,
    /// The selection ends here, with this primary (or none).
    Stop(Option<HeadlessPrimary>),
}

/// Select the terminal result of `conversation`.
///
/// # Errors
///
/// A transcript read failure.
pub(crate) async fn select_terminal_result(
    conversation: &Conversation,
    cx: &Context,
) -> Result<HeadlessTerminalResult, eukhe_durable::session::SessionError> {
    let mut walk = Walk::default();
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(ConversationEntryQuery::default(), PAGE, cursor, cx)
            .await?;
        for entry in page.items {
            if walk.take(entry) {
                return Ok(walk.result);
            }
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(walk.result),
        }
    }
}

/// The selection so far, newest entry first: the result, and the entries
/// a newer entry omits from the model's context.
#[derive(Default)]
struct Walk {
    result: HeadlessTerminalResult,
    omitted: HashSet<EntryId>,
}

impl Walk {
    /// Take the next older entry; true once the selection ended. A reply
    /// a newer entry omits from the model's context (a cut reply the stop
    /// walk dropped: `pi.drop`) is no result: print mode prints the last
    /// assistant message of the model's context, which no longer holds
    /// it.
    fn take(&mut self, entry: EntryRecord) -> bool {
        self.omitted.extend(
            entry
                .edits
                .iter()
                .flatten()
                .filter(|edit| matches!(edit.action, ContextEditAction::Omit))
                .map(|edit| edit.target),
        );
        if ASSISTANT_ENTRY.is(Some(&entry)) && self.omitted.contains(&entry.id) {
            return false;
        }
        match step(entry) {
            Step::Outcome(outcome) => self.result.compaction_outcomes.insert(0, outcome),
            Step::Warning(warning) => self.result.warnings.insert(0, warning),
            Step::Skip => {}
            Step::Stop(primary) => {
                self.result.primary = primary;
                return true;
            }
        }
        false
    }
}

fn step(entry: EntryRecord) -> Step {
    if ASSISTANT_ENTRY.is(Some(&entry)) {
        return Step::Stop(match entry.model.as_deref() {
            Some([Message::Assistant(message), ..]) => {
                Some(HeadlessPrimary::Assistant(Box::new(message.clone())))
            }
            _ => None,
        });
    }
    if CUSTOM_ENTRY.is(Some(&entry)) {
        let Ok(Some(custom)) = CUSTOM_ENTRY.narrow(entry) else {
            // A corrupt row is still part of the suffix; skip it without
            // letting it hide earlier valid rows.
            return Step::Skip;
        };
        let data = custom.data();
        let content = custom_entry_content(custom.entry().model.as_deref(), data)
            .map_or_default(user_content_text);
        let detail = |key: &str| {
            data.details
                .as_ref()
                .and_then(|details| details.get(key))
                .cloned()
        };
        return match data.custom_type.as_str() {
            COMPACTION_OUTCOME_CUSTOM_TYPE => Step::Outcome(CompactionOutcome {
                content,
                outcome: detail("outcome")
                    .and_then(|outcome| outcome.as_str().map(str::to_owned))
                    .unwrap_or_default(),
            }),
            // The row after an answer that hit the output limit and was
            // kept as it is: the answer is the primary.
            OUTPUT_LIMIT_NOTICE_CUSTOM_TYPE => Step::Warning(content),
            REFINEMENT_OUTCOME_CUSTOM_TYPE
            | REFINEMENT_NOTICE_CUSTOM_TYPE
            | HARNESS_DIGEST_CUSTOM_TYPE => Step::Skip,
            // A recovered retry episode's disclosure row trails the answer
            // that settled it: the answer is the primary (TS print mode
            // prints the last assistant message). A failed episode's row
            // still ends the walk on the run's failure.
            PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE
                if detail("success") == Some(serde_json::Value::Bool(true)) =>
            {
                Step::Skip
            }
            SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE => {
                Step::Stop(Some(HeadlessPrimary::SlashCommandResult {
                    content,
                    success: detail("success") == Some(serde_json::Value::Bool(true)),
                    severity: detail("severity")
                        .and_then(|severity| severity.as_str().map(str::to_owned)),
                }))
            }
            _ => Step::Stop(None),
        };
    }
    // Model messages without a terminal meaning (the user prompt, tool
    // results, user bash runs) end the walk; durable bookkeeping entries
    // (compaction heads, resets, summaries) are not messages.
    if entry.model.is_some() {
        Step::Stop(None)
    } else {
        Step::Skip
    }
}

fn user_content_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                eukhe_types::pi_ai::UserContentBlock::Text(text) => Some(text.text.as_str()),
                eukhe_types::pi_ai::UserContentBlock::Image(_) => None,
            })
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::{step, Step, Walk};
    use eukhe_durable::types::EntryRecord;

    /// The `provider_retry_outcome` row of an episode (the durable shape
    /// the retry observer appends after the answer that ended it).
    fn retry_outcome_row(success: bool) -> EntryRecord {
        serde_json::from_value(serde_json::json!({
            "kind": "eukhe.custom", "id": 17, "conversationId": 1,
            "data": {
                "customType": "provider_retry_outcome",
                "content": "Recovered after 1 retries: 500 stub: internal server error",
                "display": true,
                "details": { "success": success, "attempts": 1, "finalError": "500" },
            },
        }))
        .expect("an entry record")
    }

    /// A recovered episode's row trails the answer that settled it: the
    /// walk passes over it to that answer (TS print mode prints the last
    /// assistant message).
    #[test]
    fn a_recovered_retry_row_does_not_hide_the_answer() {
        assert!(matches!(step(retry_outcome_row(true)), Step::Skip));
    }

    /// A failed episode's row still ends the walk: the run has no answer.
    #[test]
    fn a_failed_retry_row_ends_the_walk() {
        assert!(matches!(step(retry_outcome_row(false)), Step::Stop(None)));
    }

    /// The warning row of a truncated answer trails the answer the run
    /// kept: the walk takes its text and passes over it to that answer.
    #[test]
    fn a_truncated_answer_warning_does_not_hide_the_answer() {
        let text = "Response hit the faux/faux-1 output limit (8 tokens) and was truncated.";
        let row: EntryRecord = serde_json::from_value(serde_json::json!({
            "kind": "eukhe.custom", "id": 17, "conversationId": 1,
            "data": { "customType": "eukhe.output_limit", "content": text, "display": true },
        }))
        .expect("an entry record");
        assert!(matches!(step(row), Step::Warning(warning) if warning == text));
    }

    /// A cut reply the stop walk dropped stays in the transcript, out of
    /// the model's context (the `pi.drop` entry after it omits it): the
    /// walk passes over it to the user's prompt, so the run has no result
    /// to print.
    #[test]
    fn a_dropped_reply_is_no_result() {
        let entries: Vec<EntryRecord> = serde_json::from_value(serde_json::json!([
            { "kind": "pi.drop", "id": 3, "conversationId": 1,
              "edits": [{ "target": 2, "action": "omit" }] },
            { "kind": "pi.assistant", "id": 2, "conversationId": 1,
              "model": [{ "role": "assistant",
                "content": [{ "type": "text", "text": "Here is the whole plan: first" }],
                "api": "faux", "provider": "faux", "model": "faux-1",
                "usage": { "input": 0, "output": 8, "cacheRead": 0, "cacheWrite": 0,
                  "totalTokens": 8,
                  "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 } },
                "stopReason": "length", "timestamp": 2 }] },
            { "kind": "pi.user", "id": 1, "conversationId": 1,
              "model": [{ "role": "user", "content": "go", "timestamp": 1 }] },
        ]))
        .expect("entry records");
        let mut walk = Walk::default();
        let ended: Vec<bool> = entries.into_iter().map(|entry| walk.take(entry)).collect();
        assert_eq!(
            (ended, walk.result.primary, walk.result.warnings),
            (vec![false, false, true], None, Vec::<String>::new())
        );
    }
}
