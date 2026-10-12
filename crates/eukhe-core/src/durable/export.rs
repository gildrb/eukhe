//! The session-file form of a durable conversation's history, the shape the
//! HTML exporter and the JSONL export read: `message`, `compaction`,
//! `custom_message`, and `branch_summary` rows chained linearly under a
//! `session` header. The daemon maps its live main conversation through
//! [`export_rows`]; the CLI `session export` reads a storage on disk through
//! [`read_export_data`] (a read-only view, the session may be open
//! elsewhere).

use anyhow::{Context as _, Result};
use eukhe_chord::context::Context;
use eukhe_durable::entries::{ASSISTANT_ENTRY, COMPACTION_ENTRY, TOOL_RESULT_ENTRY, USER_ENTRY};
use eukhe_durable::types::{EntryData, EntryRecord};
use eukhe_types::pi_ai::Message;
use serde_json::{json, Map, Value};

use super::compaction::compaction_summary_text;
use super::discovery::{read_main_transcript, DiscoveryError, SessionLocation};
use super::entries::{
    custom_entry_content, BashEntryData, BranchSummaryData, CustomEntryData, BASH_ENTRY,
    BRANCH_SUMMARY_ENTRY, CUSTOM_ENTRY,
};
use crate::export_html::SessionExportData;
use crate::session::manager::{format_iso, format_iso_now};
use crate::session::CURRENT_SESSION_VERSION;

/// The exported history rows and the id of the last one (the leaf).
#[derive(Debug, Clone, PartialEq)]
pub struct ExportRows {
    pub entries: Vec<Value>,
    pub leaf_id: Option<String>,
}

/// A fresh `session` header row for `session_id` at `cwd`.
#[must_use]
pub fn export_header(session_id: &str, cwd: &str) -> Value {
    json!({
        "type": "session",
        "version": CURRENT_SESSION_VERSION,
        "id": session_id,
        "timestamp": format_iso_now(),
        "cwd": cwd,
    })
}

/// `entries` (a conversation's fork-aware history, oldest first) as
/// session-file rows chained linearly: `id` is the durable entry id,
/// `parentId` the previous exported row. Bookkeeping entries (`pi.system`,
/// `pi.reset`, custom state) are skipped.
///
/// # Errors
///
/// An entry's data or model message does not decode.
pub fn export_rows(entries: &[EntryRecord]) -> Result<ExportRows> {
    let mut rows = Vec::new();
    let mut previous: Option<String> = None;
    let mut last_timestamp = 0;
    for entry in entries {
        let timestamp = timestamp_ms(entry).unwrap_or(last_timestamp);
        last_timestamp = timestamp;
        let Some(body) = file_entry(entry, timestamp)
            .with_context(|| format!("exporting durable entry {}", entry.id))?
        else {
            continue;
        };
        let id = entry.id.to_string();
        let mut row = Map::new();
        if let Value::Object(body) = body {
            let mut body = body.into_iter();
            if let Some((key, value)) = body.next() {
                row.insert(key, value);
            }
            row.insert("id".to_owned(), json!(id));
            row.insert(
                "parentId".to_owned(),
                previous
                    .as_ref()
                    .map_or(Value::Null, |parent| json!(parent)),
            );
            row.insert("timestamp".to_owned(), json!(iso(timestamp)));
            row.extend(body);
        }
        rows.push(Value::Object(row));
        previous = Some(id);
    }
    Ok(ExportRows {
        entries: rows,
        leaf_id: previous,
    })
}

/// The export data of the session stored at `location`: its main
/// conversation's history under a header naming the storage directory and
/// the main agent's cwd. `None` for a legacy file not imported yet (it has
/// no durable storage to read).
///
/// # Errors
///
/// A durable location without a storage, an unreadable storage, or an
/// entry that does not decode.
pub(crate) async fn read_export_data(
    location: &SessionLocation,
    cx: &Context,
) -> Result<Option<SessionExportData>> {
    let dir = location.storage_dir();
    let transcript = match read_main_transcript(location, cx).await {
        Ok(transcript) => transcript,
        Err(DiscoveryError::NotDurable { .. })
            if matches!(location, SessionLocation::Legacy(_)) =>
        {
            return Ok(None);
        }
        Err(error) => {
            return Err(anyhow::Error::new(error)
                .context(format!("reading session storage {}", dir.display())));
        }
    };
    let rows = export_rows(&transcript.entries)?;
    let session_id = dir
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();
    let cwd = transcript.agent.cwd.unwrap_or_default();
    Ok(Some(SessionExportData {
        header: export_header(&session_id, &cwd),
        entries: rows.entries,
        leaf_id: rows.leaf_id,
        system_prompt: None,
        tools: None,
        rendered_tools: None,
    }))
}

fn timestamp_ms(entry: &EntryRecord) -> Option<u64> {
    entry
        .model
        .as_deref()
        .and_then(<[Message]>::first)
        .map(Message::timestamp)
}

#[expect(
    clippy::cast_possible_wrap,
    reason = "epoch milliseconds stay far below i64::MAX"
)]
fn iso(millis: u64) -> String {
    format_iso(millis as i64)
}

/// The session-file form of one durable entry (without `id`, `parentId`,
/// `timestamp`), or `None` for bookkeeping entries the export skips.
fn file_entry(entry: &EntryRecord, timestamp: u64) -> Result<Option<Value>> {
    let first = || {
        entry
            .model
            .as_deref()
            .and_then(<[Message]>::first)
            .map(serde_json::to_value)
            .transpose()
    };
    let kind = Some(entry);
    if USER_ENTRY.is(kind) || ASSISTANT_ENTRY.is(kind) || TOOL_RESULT_ENTRY.is(kind) {
        return Ok(first()?.map(|message| json!({ "type": "message", "message": message })));
    }
    if COMPACTION_ENTRY.is(kind) {
        return Ok(Some(json!({
            "type": "compaction",
            "summary": compaction_summary_text(entry)?,
            "firstKeptEntryId": entry.head.map_or_else(String::new, |head| head.to_string()),
            "tokensBefore": 0,
        })));
    }
    if CUSTOM_ENTRY.is(kind) {
        let data: CustomEntryData = EntryData::decode(entry.data.as_ref())?;
        let content = custom_entry_content(entry.model.as_deref(), &data)
            .map(serde_json::to_value)
            .transpose()?
            .unwrap_or(Value::Null);
        let mut row = json!({
            "type": "custom_message",
            "customType": data.custom_type,
            "content": content,
            "display": data.display,
        });
        if let Some(details) = data.details {
            row["details"] = details;
        }
        return Ok(Some(row));
    }
    if BASH_ENTRY.is(kind) {
        let data: BashEntryData = EntryData::decode(entry.data.as_ref())?;
        let mut message = serde_json::to_value(&data)?;
        if let Value::Object(map) = &mut message {
            let mut with_role = Map::new();
            with_role.insert("role".to_owned(), json!("bashExecution"));
            with_role.extend(std::mem::take(map));
            with_role.insert("timestamp".to_owned(), json!(timestamp));
            *map = with_role;
        }
        return Ok(Some(json!({ "type": "message", "message": message })));
    }
    if BRANCH_SUMMARY_ENTRY.is(kind) {
        let data: BranchSummaryData = EntryData::decode(entry.data.as_ref())?;
        let mut row = json!({
            "type": "branch_summary",
            "fromId": data.from_id,
            "summary": data.summary,
        });
        if let Some(details) = data.details {
            row["details"] = details;
        }
        if let Some(from_hook) = data.from_hook {
            row["fromHook"] = json!(from_hook);
        }
        return Ok(Some(row));
    }
    Ok(None)
}

#[cfg(test)]
mod tests;
