//! `export_html` / `export_jsonl` over a durable conversation: the
//! conversation's fork-aware history mapped to the session-file entry shapes
//! the exporter and the JSONL format read (`message`, `compaction`,
//! `custom_message`, `branch_summary`), chained linearly.

use std::path::{Path, PathBuf};

use anyhow::{Context as _, Result};
use eukhe_chord::context::Context;
use eukhe_core::durable::{
    custom_entry_content, BashEntryData, BranchSummaryData, CustomEntryData, HostDeps, BASH_ENTRY,
    BRANCH_SUMMARY_ENTRY, CUSTOM_ENTRY,
};
use eukhe_core::session::manager::{format_iso, format_iso_now};
use eukhe_durable::entries::{ASSISTANT_ENTRY, COMPACTION_ENTRY, TOOL_RESULT_ENTRY, USER_ENTRY};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::types::{EntryData, EntryRecord};
use eukhe_pi_ai::utils::text::get_system_message_text;
use eukhe_pi_ai::utils::transcript::{get_current_system_message, get_current_tools};
use eukhe_types::pi_ai::Message;
use serde_json::{json, Map, Value};

use crate::compaction::durable::compaction_summary_text;

/// Entries read per history page.
const PAGE: usize = 1_000;

/// The conversation's fork-aware history, oldest first.
async fn history(conversation: &Conversation, cx: &Context) -> Result<Vec<EntryRecord>> {
    let mut entries = Vec::new();
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(ConversationEntryQuery::default(), PAGE, cursor, cx)
            .await
            .context("reading the conversation history")?;
        entries.extend(page.items);
        match page.next {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    entries.reverse();
    Ok(entries)
}

fn timestamp_ms(entry: &EntryRecord) -> Option<u64> {
    entry
        .model
        .as_deref()
        .and_then(<[Message]>::first)
        .map(|message| match message {
            Message::User(message) => message.timestamp,
            Message::Assistant(message) => message.timestamp,
            Message::ToolResult(message) => message.timestamp,
            Message::System(message) => message.timestamp,
        })
}

#[expect(
    clippy::cast_possible_wrap,
    reason = "epoch milliseconds stay far below i64::MAX"
)]
fn iso(millis: u64) -> String {
    format_iso(millis as i64)
}

/// The session-file form of one durable entry (without `id`, `parentId`,
/// `timestamp`), or `None` for bookkeeping entries the export skips
/// (`pi.system`, `pi.reset`, custom state).
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
            "summary": compaction_summary_text(entry),
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

/// The exported entries chained linearly (`id` = durable entry id,
/// `parentId` = the previous exported entry), and the leaf id.
fn file_entries(entries: &[EntryRecord]) -> Result<(Vec<Value>, Option<String>)> {
    let mut rows = Vec::new();
    let mut previous: Option<String> = None;
    let mut last_timestamp = 0;
    for entry in entries {
        let timestamp = timestamp_ms(entry).unwrap_or(last_timestamp);
        last_timestamp = timestamp;
        let Some(body) = file_entry(entry, timestamp)? else {
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
    Ok((rows, previous))
}

fn header(deps: &HostDeps) -> Value {
    json!({
        "type": "session",
        "version": eukhe_core::session::CURRENT_SESSION_VERSION,
        "id": deps.session_id,
        "timestamp": format_iso_now(),
        "cwd": deps.cwd.to_string_lossy(),
    })
}

/// `export_html`: render `conversation` to a standalone HTML file and answer
/// the written path. A given `output_path` is used verbatim; without one the
/// file is `eukhe-session-<session id>.html`.
///
/// # Errors
///
/// History reads, theme resolution, or the file write fail.
pub(crate) async fn export_html(
    deps: &HostDeps,
    conversation: &Conversation,
    output_path: Option<&str>,
    cx: &Context,
) -> Result<String> {
    let entries = history(conversation, cx).await?;
    let (rows, leaf_id) = file_entries(&entries)?;
    let view = conversation
        .context(cx)
        .await
        .context("reading the conversation context")?;
    let system_prompt =
        get_current_system_message(&view.messages).map(|message| get_system_message_text(&message));
    let tools = get_current_tools(&view.messages)
        .iter()
        .map(|tool| {
            json!({
                "name": tool.name,
                "description": tool.description,
                "parameters": tool.parameters,
            })
        })
        .collect();
    let data = eukhe_core::export_html::SessionExportData {
        header: header(deps),
        entries: rows,
        leaf_id,
        system_prompt,
        tools: Some(tools),
        rendered_tools: None,
    };
    let theme = deps.settings.manager().get_theme().map(str::to_owned);
    eukhe_core::export_html::export_session_to_html(
        &data,
        theme.as_deref(),
        &deps.agent_dir,
        Path::new(&format!("{}.jsonl", deps.session_id)),
        output_path,
    )
}

/// `export_jsonl`: `conversation`'s history as a linear session file under a
/// fresh header; a relative (or omitted) path resolves against the session
/// cwd. Answers the written path.
///
/// # Errors
///
/// History reads or the file write fail.
pub(crate) async fn export_jsonl(
    deps: &HostDeps,
    conversation: &Conversation,
    output_path: Option<&str>,
    cx: &Context,
) -> Result<String> {
    let entries = history(conversation, cx).await?;
    let (rows, _) = file_entries(&entries)?;
    let file_path = match output_path {
        Some(path) if Path::new(path).is_absolute() => PathBuf::from(path),
        Some(path) => deps.cwd.join(path),
        None => deps.cwd.join(format!(
            "session-{}.jsonl",
            format_iso_now().replace([':', '.'], "-")
        )),
    };
    if let Some(parent) = file_path.parent() {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("creating {}", parent.display()))?;
    }
    let mut lines = vec![serde_json::to_string(&header(deps))?];
    for row in &rows {
        lines.push(serde_json::to_string(row)?);
    }
    std::fs::write(&file_path, format!("{}\n", lines.join("\n")))
        .with_context(|| format!("writing {}", file_path.display()))?;
    Ok(file_path.to_string_lossy().into_owned())
}

#[cfg(test)]
mod tests;
