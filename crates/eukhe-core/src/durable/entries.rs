//! eukhe entry kinds of the durable transcript: the session rows the old
//! engine kept besides user/assistant/tool-result messages (custom messages,
//! user bash runs, branch summaries, custom state). Live eukhe code and the
//! legacy session import write them in the same shapes, so attach/replay
//! treats imported and live rows alike.
//!
//! An entry's `model` is what reaches the provider, exactly as the old
//! engine's `convert_to_llm` rendered the row; the entry timestamp is the
//! row's time.

use eukhe_chord::json::JsonError;
use eukhe_durable::entries::Entry;
use eukhe_durable::types::{EntryDraft, TypedEntryDraft};
use eukhe_types::pi_ai::{Message, TextContent, UserContent, UserContentBlock, UserMessage};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::session_engine::messages::{
    bash_execution_to_text, COMPACTION_OUTCOME_CUSTOM_TYPE, PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE,
    REFINEMENT_OUTCOME_CUSTOM_TYPE, SESSION_SLASH_COMMAND_CUSTOM_TYPE,
    SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
};

/// A custom message (the old `custom_message` row / `custom` role):
/// `model` is `[UserMessage]` with the row's content when it reaches the
/// model, absent for display-only rows (whose content then rides in
/// `data.content`). Build drafts with [`custom_entry_draft`].
pub static CUSTOM_ENTRY: Entry<CustomEntryData> = define("eukhe.custom");

/// A user `!` bash run (the old `bashExecution` role): `model` is the
/// `[UserMessage]` "Ran `cmd`" text, absent when excluded from context.
/// Build drafts with [`bash_entry_draft`].
pub static BASH_ENTRY: Entry<BashEntryData> = define("eukhe.bash");

/// A summary of a branch the conversation came back from: `model` is the
/// wrapped `[UserMessage]`, absent for an empty summary.
pub static BRANCH_SUMMARY_ENTRY: Entry<BranchSummaryData> = define("eukhe.branch-summary");

/// A `compactionSummary`-role message stored as a plain message row (not a
/// compaction): `model` is its wrapped `[UserMessage]`.
pub static COMPACTION_SUMMARY_ENTRY: Entry<eukhe_types::session::CompactionSummaryMessage> =
    define("eukhe.compaction-summary");

/// Opaque application state (the old non-message `custom` row); never model
/// context.
pub static CUSTOM_STATE_ENTRY: Entry<CustomStateData> = define("eukhe.custom-state");

const fn define<D>(kind: &'static str) -> Entry<D> {
    match Entry::define(kind) {
        Ok(entry) => entry,
        Err(_) => panic!("eukhe entry kinds are non-empty"),
    }
}

/// Data of a [`CUSTOM_ENTRY`]: `{customType, content?, display, details?,
/// input?}`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CustomEntryData {
    pub custom_type: String,
    /// The row's content when no `model` carries it (display-only rows).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub content: Option<UserContent>,
    /// Whether the TUI shows the row.
    pub display: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub details: Option<Value>,
    /// The row stands for an input submitted after it with the same
    /// content (the old engine's injected custom turn, whose row replaced
    /// the user message): the input's user entry carries the model
    /// context, so the row has no `model`, and transcripts show the row in
    /// the input's place. Build drafts with [`input_row_draft`].
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub input: bool,
}

/// Data of a [`BASH_ENTRY`]: the old `bashExecution` fields without the
/// timestamp.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BashEntryData {
    pub command: String,
    pub output: String,
    /// Exit status; absent while the command is still running.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exit_code: Option<i64>,
    pub cancelled: bool,
    pub truncated: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub full_output_path: Option<String>,
    /// True keeps the run out of model context (`!!` prefix).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exclude_from_context: Option<bool>,
}

/// Data of a [`BRANCH_SUMMARY_ENTRY`].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BranchSummaryData {
    pub summary: String,
    /// The entry the conversation came back from.
    pub from_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub details: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub from_hook: Option<bool>,
    /// Unix timestamp in milliseconds.
    pub timestamp: u64,
}

/// Data of a [`CUSTOM_STATE_ENTRY`].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CustomStateData {
    pub custom_type: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub data: Option<Value>,
}

/// Whether custom messages of `custom_type` stay out of model context
/// (display-only bookkeeping, the old engine's `convert_to_llm` rule).
#[must_use]
pub fn is_display_only_custom_type(custom_type: &str) -> bool {
    matches!(
        custom_type,
        SESSION_SLASH_COMMAND_CUSTOM_TYPE
            | SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE
            | COMPACTION_OUTCOME_CUSTOM_TYPE
            | REFINEMENT_OUTCOME_CUSTOM_TYPE
            | PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE
            | crate::prompts::model_prompts::MODEL_PROMPT_ERROR_CUSTOM_TYPE
    )
}

/// The [`CUSTOM_ENTRY`] draft of a custom message. A model-visible type gets
/// `model: [UserMessage]` (text content becomes one text block, as the old
/// `convert_to_llm` sent it); a display-only type keeps `content` in data.
///
/// # Errors
///
/// `details` is not strict JSON.
pub fn custom_entry_draft(
    custom_type: impl Into<String>,
    content: UserContent,
    display: bool,
    details: Option<Value>,
    timestamp: u64,
) -> Result<EntryDraft, JsonError> {
    let custom_type = custom_type.into();
    let (model, content) = if is_display_only_custom_type(&custom_type) {
        (None, Some(content))
    } else {
        let content = match content {
            UserContent::Text(text) => {
                UserContent::Blocks(vec![UserContentBlock::Text(TextContent::new(text))])
            }
            blocks @ UserContent::Blocks(_) => blocks,
        };
        (Some(vec![user_message(content, timestamp)]), None)
    };
    CUSTOM_ENTRY.draft(&TypedEntryDraft {
        model,
        data: CustomEntryData {
            custom_type,
            content,
            display,
            details,
            input: false,
        },
        head: None,
        edits: None,
    })
}

/// The [`CUSTOM_ENTRY`] draft of a row that stands for the input submitted
/// right after it with the same `content` (see [`CustomEntryData::input`]):
/// no `model` (the input carries the context), `content` in data.
///
/// # Errors
///
/// `details` is not strict JSON.
pub fn input_row_draft(
    custom_type: impl Into<String>,
    content: UserContent,
    display: bool,
    details: Option<Value>,
) -> Result<EntryDraft, JsonError> {
    CUSTOM_ENTRY.draft(&TypedEntryDraft {
        model: None,
        data: CustomEntryData {
            custom_type: custom_type.into(),
            content: Some(content),
            display,
            details,
            input: true,
        },
        head: None,
        edits: None,
    })
}

/// The content of a custom entry: its model message's content, else
/// `data.content`.
#[must_use]
pub fn custom_entry_content<'a>(
    model: Option<&'a [Message]>,
    data: &'a CustomEntryData,
) -> Option<&'a UserContent> {
    match model.and_then(<[Message]>::first) {
        Some(Message::User(message)) => Some(&message.content),
        _ => data.content.as_ref(),
    }
}

/// The model text of a bash run (the old `bash_execution_to_text`).
#[must_use]
pub fn bash_entry_text(data: &BashEntryData) -> String {
    bash_execution_to_text(&eukhe_types::session::BashExecutionMessage {
        command: data.command.clone(),
        output: data.output.clone(),
        exit_code: data.exit_code,
        cancelled: data.cancelled,
        truncated: data.truncated,
        full_output_path: data.full_output_path.clone(),
        timestamp: 0,
        exclude_from_context: data.exclude_from_context,
    })
}

/// The [`BASH_ENTRY`] draft of a bash run: `model` is one user text message
/// unless the run is excluded from context.
///
/// # Errors
///
/// The data is not strict JSON (never for these field types).
pub fn bash_entry_draft(data: BashEntryData, timestamp: u64) -> Result<EntryDraft, JsonError> {
    let model = (!data.exclude_from_context.unwrap_or(false)).then(|| {
        vec![user_message(
            UserContent::Blocks(vec![UserContentBlock::Text(TextContent::new(
                bash_entry_text(&data),
            ))]),
            timestamp,
        )]
    });
    BASH_ENTRY.draft(&TypedEntryDraft {
        model,
        data,
        head: None,
        edits: None,
    })
}

fn user_message(content: UserContent, timestamp: u64) -> Message {
    Message::User(UserMessage { content, timestamp })
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn text(message: &Message) -> &str {
        match message {
            Message::User(UserMessage {
                content: UserContent::Blocks(blocks),
                ..
            }) => match blocks.as_slice() {
                [UserContentBlock::Text(text)] => &text.text,
                other => panic!("one text block expected: {other:?}"),
            },
            other => panic!("user blocks expected: {other:?}"),
        }
    }

    #[test]
    fn custom_entries_reach_the_model_unless_display_only() {
        let draft = custom_entry_draft(
            "agent_message",
            UserContent::Text("[agent-message from x] hi".to_owned()),
            true,
            Some(json!({"from": "x"})),
            7,
        )
        .expect("draft");
        assert_eq!(draft.kind, "eukhe.custom");
        let model = draft.model.expect("model");
        assert_eq!(text(&model[0]), "[agent-message from x] hi");
        assert_eq!(
            serde_json::to_value(draft.data.expect("data")).expect("json"),
            json!({"customType": "agent_message", "display": true, "details": {"from": "x"}})
        );

        let shown = custom_entry_draft(
            COMPACTION_OUTCOME_CUSTOM_TYPE,
            UserContent::Text("compacted".to_owned()),
            true,
            None,
            7,
        )
        .expect("draft");
        assert_eq!(shown.model, None);
        assert_eq!(
            serde_json::to_value(shown.data.expect("data")).expect("json"),
            json!({"customType": COMPACTION_OUTCOME_CUSTOM_TYPE, "content": "compacted", "display": true})
        );
    }

    #[test]
    fn bash_entries_render_the_old_llm_text() {
        let data = BashEntryData {
            command: "cargo test".to_owned(),
            output: "ok".to_owned(),
            exit_code: Some(1),
            cancelled: false,
            truncated: false,
            full_output_path: None,
            exclude_from_context: None,
        };
        let draft = bash_entry_draft(data.clone(), 3).expect("draft");
        assert_eq!(draft.kind, "eukhe.bash");
        assert_eq!(
            text(&draft.model.expect("model")[0]),
            "Ran `cargo test`\n```\nok\n```\n\nCommand exited with code 1"
        );
        assert_eq!(
            serde_json::to_value(draft.data.expect("data")).expect("json"),
            json!({"command": "cargo test", "output": "ok", "exitCode": 1, "cancelled": false, "truncated": false})
        );
        let excluded = bash_entry_draft(
            BashEntryData {
                exclude_from_context: Some(true),
                ..data
            },
            3,
        )
        .expect("draft");
        assert_eq!(excluded.model, None);
    }
}
