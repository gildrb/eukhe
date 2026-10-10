//! The headless terminal selection over the durable transcript (the
//! selection half of TS `headless-completion.ts` + the text-output half of
//! `print-mode.ts`): walk the main conversation newest-first, collect the
//! trailing compaction outcomes, skip internal notices, and take the first
//! substantive entry (an assistant answer or a slash-command result) as the
//! primary.

use eukhe_chord::context::Context;
use eukhe_core::durable::{custom_entry_content, CUSTOM_ENTRY};
use eukhe_core::session_engine::headless::{
    COMPACTION_OUTCOME_CUSTOM_TYPE, HARNESS_DIGEST_CUSTOM_TYPE, REFINEMENT_NOTICE_CUSTOM_TYPE,
    REFINEMENT_OUTCOME_CUSTOM_TYPE,
};
use eukhe_core::session_engine::messages::SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE;
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::types::EntryRecord;
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
}

/// What one transcript entry means for the selection.
enum Step {
    /// A trailing compaction outcome.
    Outcome(CompactionOutcome),
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
) -> Result<HeadlessTerminalResult, String> {
    let mut result = HeadlessTerminalResult::default();
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(ConversationEntryQuery::default(), PAGE, cursor, cx)
            .await
            .map_err(|error| format!("{error:#}"))?;
        for entry in page.items {
            match step(entry) {
                Step::Outcome(outcome) => result.compaction_outcomes.insert(0, outcome),
                Step::Skip => {}
                Step::Stop(primary) => {
                    result.primary = primary;
                    return Ok(result);
                }
            }
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(result),
        }
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
            .map(user_content_text)
            .unwrap_or_default();
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
            REFINEMENT_OUTCOME_CUSTOM_TYPE
            | REFINEMENT_NOTICE_CUSTOM_TYPE
            | HARNESS_DIGEST_CUSTOM_TYPE => Step::Skip,
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
