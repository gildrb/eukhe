//! Durable transcript entries -> the wire `AgentMessage` objects the TUI
//! reads (attach `messages`, `get_messages`, `message_start`/`message_end`).
//!
//! Each shown entry kind maps to the role the old session file projected:
//! `pi.user`/`pi.assistant`/`pi.tool-result` pass their model message
//! through, the eukhe kinds rebuild their old roles (`custom`,
//! `bashExecution`, `branchSummary`), and a `pi.compaction` summary becomes a
//! `compactionSummary`. Kinds the transcript never showed (`pi.system`,
//! `pi.reset`, custom state) map to nothing.

use eukhe_core::durable::compaction::compaction_summary_text;
use eukhe_core::durable::{
    custom_entry_content, BashEntryData, BranchSummaryData, CustomEntryData, BASH_ENTRY,
    BRANCH_SUMMARY_ENTRY, COMPACTION_SUMMARY_ENTRY, CUSTOM_ENTRY,
};
use eukhe_durable::entries::{ASSISTANT_ENTRY, COMPACTION_ENTRY, TOOL_RESULT_ENTRY, USER_ENTRY};
use eukhe_durable::types::EntryRecord;
use eukhe_types::pi_ai::{AssistantMessage, Message};
use eukhe_types::session::AgentMessage;
use serde::de::DeserializeOwned;
use serde::Serialize;
use serde_json::{json, Map, Value};

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

/// The wire form of one assistant message: the pi-ai message, with the stop
/// reasons the wire does not know (`pending` on a streaming partial,
/// `deferred`) shown as `stop`, and `rawStopReason` also under the old
/// `stopReasonRaw` key.
#[must_use]
pub fn assistant_wire_message(message: &AssistantMessage) -> Option<AgentMessage> {
    let mut value = serde_json::to_value(message).ok()?;
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
    match serde_json::from_value(value) {
        Ok(message) => Some(message),
        Err(error) => {
            eprintln!(
                "eukhe-daemon worker: dropped an assistant message the wire cannot carry: {error}"
            );
            None
        }
    }
}

/// `value` re-read as its wire type: the pi-ai messages and content blocks
/// map onto the wire's message types. A value the wire type rejects is
/// logged and dropped.
pub(crate) fn to_wire<T: Serialize, U: DeserializeOwned>(value: &T) -> Option<U> {
    match serde_json::to_value(value).and_then(serde_json::from_value) {
        Ok(wire) => Some(wire),
        Err(error) => {
            eprintln!(
                "eukhe-daemon worker: dropped a value the wire cannot carry ({}): {error}",
                std::any::type_name::<U>()
            );
            None
        }
    }
}

/// Attach `messages`: every shown entry mapped, in order. A user entry
/// covered by the input row before it (an `eukhe.custom` row with
/// `input: true`, an injected custom turn) shows as that row
/// only.
#[must_use]
pub fn transcript_messages(entries: &[EntryRecord]) -> Vec<Value> {
    transcript_messages_of(entries)
}

/// [`transcript_messages`] over any in-order run of entries (an active
/// context selected out of the mirror).
pub(crate) fn transcript_messages_of<'a>(
    entries: impl IntoIterator<Item = &'a EntryRecord>,
) -> Vec<Value> {
    let entries = entries.into_iter();
    let mut context_tokens = 0;
    let mut messages = Vec::with_capacity(entries.size_hint().0);
    let mut previous: Option<&EntryRecord> = None;
    for entry in entries {
        let covered = entry.kind.as_str() == USER_ENTRY.kind()
            && previous.is_some_and(|row| {
                row.kind.as_str() == CUSTOM_ENTRY.kind()
                    && entry_data::<CustomEntryData>(row).is_some_and(|data| data.input)
            });
        previous = Some(entry);
        if covered {
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
            .and_then(assistant_wire_message)
            .and_then(|message| serde_json::to_value(message).ok());
    }
    if kind == COMPACTION_ENTRY.kind() {
        // A malformed row maps to nothing, like `entry_data`.
        let summary = compaction_summary_text(entry).ok()?;
        return Some(json!({
            "role": "compactionSummary",
            "summary": summary,
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
    if let Some(omitted) = data.omitted {
        message.insert("omitted".to_owned(), serde_json::json!(omitted));
    }
    if let Some(path) = data.artifact {
        message.insert("artifact".to_owned(), Value::from(path));
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

#[cfg(test)]
#[path = "wire_messages/tests.rs"]
mod tests;
