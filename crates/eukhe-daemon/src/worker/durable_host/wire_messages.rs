//! Durable transcript entries -> the wire `AgentMessage` objects the TUI
//! reads (attach `messages`, `get_messages`, `message_start`/`message_end`).
//!
//! Each shown entry kind maps to the role the old session file projected:
//! `pi.user`/`pi.assistant`/`pi.tool-result` pass their model message
//! through, the eukhe kinds rebuild their old roles (`custom`,
//! `bashExecution`, `branchSummary`), and a `pi.compaction` summary becomes a
//! `compactionSummary`. Kinds the transcript never showed (`pi.system`,
//! `pi.reset`, custom state) map to nothing.

use eukhe_core::durable::{
    custom_entry_content, BashEntryData, BranchSummaryData, CustomEntryData, BASH_ENTRY,
    BRANCH_SUMMARY_ENTRY, COMPACTION_SUMMARY_ENTRY, CUSTOM_ENTRY,
};
use eukhe_durable::entries::{ASSISTANT_ENTRY, COMPACTION_ENTRY, TOOL_RESULT_ENTRY, USER_ENTRY};
use eukhe_durable::types::EntryRecord;
use eukhe_types::pi_ai::{
    AssistantMessage, ContentBlockText, Message, UserContent, UserContentBlock,
};
use serde::de::DeserializeOwned;
use serde_json::{json, Map, Value};

/// The wrapper the durable compaction puts around a summary in the entry's
/// model message (`harness/compaction/prompt.rs` `SUMMARY_PREFIX` /
/// `SUMMARY_SUFFIX`, crate-private there). The wire `summary` is the bare
/// text, as the old `compaction` row stored it.
const SUMMARY_PREFIX: &str =
    "The conversation history before this point was compacted into the following summary:\n\n<summary>\n";
const SUMMARY_SUFFIX: &str = "\n</summary>";

/// The wire `AgentMessage` for one entry (attach snapshot, `get_messages`,
/// `message_start`/`message_end`), or None for entries the transcript does not show.
///
/// A `compactionSummary` built here carries `tokensBefore: 0`; use
/// [`transcript_messages`] for a transcript, which measures it from the
/// preceding answer.
#[must_use]
pub fn entry_wire_message(entry: &EntryRecord) -> Option<Value> {
    entry_wire_message_with(entry, 0)
}

/// The wire form of one assistant message: the pi-ai JSON, with the stop
/// reasons the TUI's typed readers do not know (`pending` on a streaming
/// partial, `deferred`) shown as `stop`, and `rawStopReason` also under the
/// old `stopReasonRaw` key.
#[must_use]
pub fn assistant_wire_message(message: &AssistantMessage) -> Value {
    let mut value = serde_json::to_value(message).unwrap_or(Value::Null);
    if let Value::Object(object) = &mut value {
        if matches!(
            object.get("stopReason").and_then(Value::as_str),
            Some("pending" | "deferred")
        ) {
            object.insert("stopReason".to_owned(), Value::from("stop"));
        }
        if let Some(raw) = object.get("rawStopReason").cloned() {
            object.insert("stopReasonRaw".to_owned(), raw);
        }
    }
    value
}

/// Attach `messages`: every shown entry mapped, in order. A user entry
/// covered by the input row before it (an `eukhe.custom` row with
/// `input: true`, the old engine's injected custom turn) shows as that row
/// only.
#[must_use]
pub fn transcript_messages(entries: &[EntryRecord]) -> Vec<Value> {
    let mut context_tokens = 0;
    let mut messages = Vec::with_capacity(entries.len());
    for (index, entry) in entries.iter().enumerate() {
        if entry.kind.as_str() == USER_ENTRY.kind()
            && entries[..index].last().is_some_and(|row| {
                row.kind.as_str() == CUSTOM_ENTRY.kind()
                    && entry_data::<CustomEntryData>(row).is_some_and(|data| data.input)
            })
        {
            continue;
        }
        if let Some(message) = entry_wire_message_with(entry, context_tokens) {
            messages.push(message);
        }
        if let Some(tokens) = assistant_context_tokens(entry) {
            context_tokens = tokens;
        }
    }
    messages
}

/// [`entry_wire_message`] with the `tokensBefore` a compaction summary shows.
pub(crate) fn entry_wire_message_with(entry: &EntryRecord, tokens_before: u64) -> Option<Value> {
    let kind = entry.kind.as_str();
    let first = entry.model.as_deref().and_then(<[Message]>::first);
    if kind == USER_ENTRY.kind() || kind == TOOL_RESULT_ENTRY.kind() {
        return first.and_then(|message| serde_json::to_value(message).ok());
    }
    if kind == ASSISTANT_ENTRY.kind() {
        return first
            .and_then(Message::as_assistant)
            .map(assistant_wire_message);
    }
    if kind == COMPACTION_ENTRY.kind() {
        return Some(json!({
            "role": "compactionSummary",
            "summary": compaction_summary_text(entry),
            "tokensBefore": tokens_before,
            "timestamp": entry_timestamp(entry),
        }));
    }
    if kind == CUSTOM_ENTRY.kind() {
        return custom_message(entry);
    }
    if kind == BASH_ENTRY.kind() {
        return bash_message(entry);
    }
    if kind == BRANCH_SUMMARY_ENTRY.kind() {
        let data: BranchSummaryData = entry_data(entry)?;
        return Some(json!({
            "role": "branchSummary",
            "summary": data.summary,
            "fromId": data.from_id,
            "timestamp": first.map_or(data.timestamp, Message::timestamp),
        }));
    }
    if kind == COMPACTION_SUMMARY_ENTRY.kind() {
        // The imported `compactionSummary` row: its data is the old message
        // without the role.
        let Value::Object(mut object) = Value::from(entry.data.as_ref()?) else {
            return None;
        };
        object.insert("role".to_owned(), Value::from("compactionSummary"));
        return Some(Value::Object(object));
    }
    None
}

/// The bare summary text of a `pi.compaction` entry: its model message's
/// text without the durable wrapper.
pub(crate) fn compaction_summary_text(entry: &EntryRecord) -> String {
    let text = match entry.model.as_deref().and_then(<[Message]>::first) {
        Some(Message::User(message)) => user_content_text(&message.content),
        _ => String::new(),
    };
    match text
        .strip_prefix(SUMMARY_PREFIX)
        .and_then(|rest| rest.strip_suffix(SUMMARY_SUFFIX))
    {
        Some(summary) => summary.to_owned(),
        None => text,
    }
}

/// The context size an assistant entry's answer measured (its usage total,
/// else the sum of its counters), or None for other entries.
pub(crate) fn assistant_context_tokens(entry: &EntryRecord) -> Option<u64> {
    if entry.kind != ASSISTANT_ENTRY.kind() {
        return None;
    }
    let message = entry
        .model
        .as_deref()
        .and_then(<[Message]>::first)
        .and_then(Message::as_assistant)?;
    let usage = &message.usage;
    Some(if usage.total_tokens > 0 {
        usage.total_tokens
    } else {
        usage.input + usage.output + usage.cache_read + usage.cache_write
    })
}

fn custom_message(entry: &EntryRecord) -> Option<Value> {
    let data: CustomEntryData = entry_data(entry)?;
    let content = custom_entry_content(entry.model.as_deref(), &data)
        .and_then(|content| serde_json::to_value(content).ok())
        .unwrap_or_else(|| Value::from(""));
    let mut message = Map::new();
    message.insert("role".to_owned(), Value::from("custom"));
    message.insert("customType".to_owned(), Value::from(data.custom_type));
    message.insert("content".to_owned(), content);
    message.insert("display".to_owned(), Value::from(data.display));
    if let Some(details) = data.details {
        message.insert("details".to_owned(), details);
    }
    message.insert("timestamp".to_owned(), Value::from(entry_timestamp(entry)));
    Some(Value::Object(message))
}

fn bash_message(entry: &EntryRecord) -> Option<Value> {
    let data: BashEntryData = entry_data(entry)?;
    let mut message = Map::new();
    message.insert("role".to_owned(), Value::from("bashExecution"));
    message.insert("command".to_owned(), Value::from(data.command));
    message.insert("output".to_owned(), Value::from(data.output));
    if let Some(exit_code) = data.exit_code {
        message.insert("exitCode".to_owned(), Value::from(exit_code));
    }
    message.insert("cancelled".to_owned(), Value::from(data.cancelled));
    message.insert("truncated".to_owned(), Value::from(data.truncated));
    if let Some(path) = data.full_output_path {
        message.insert("fullOutputPath".to_owned(), Value::from(path));
    }
    if let Some(exclude) = data.exclude_from_context {
        message.insert("excludeFromContext".to_owned(), Value::from(exclude));
    }
    message.insert("timestamp".to_owned(), Value::from(entry_timestamp(entry)));
    Some(Value::Object(message))
}

/// The entry's typed data, or None when absent or of another shape.
pub(crate) fn entry_data<T: DeserializeOwned>(entry: &EntryRecord) -> Option<T> {
    serde_json::from_value(Value::from(entry.data.as_ref()?)).ok()
}

/// The model message's timestamp when present, else the data's, else 0.
fn entry_timestamp(entry: &EntryRecord) -> u64 {
    if let Some(message) = entry.model.as_deref().and_then(<[Message]>::first) {
        return message.timestamp();
    }
    entry
        .data
        .as_ref()
        .and_then(|data| data.get("timestamp"))
        .and_then(|timestamp| Value::from(timestamp).as_u64())
        .unwrap_or(0)
}

fn user_content_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(UserContentBlock::text_block)
            .collect(),
    }
}

#[cfg(test)]
#[path = "wire_messages/tests.rs"]
mod tests;
