//! `export_html` / `export_jsonl` over the live main conversation: its
//! fork-aware history mapped to session-file rows by eukhe-core's
//! [`export_rows`] (the mapping the CLI `session export` shares).

use std::path::{Path, PathBuf};

use anyhow::{Context as _, Result};
use eukhe_ai::utils::text::get_system_message_text;
use eukhe_ai::utils::transcript::{get_current_system_message, get_current_tools};
use eukhe_chord::context::Context;
use eukhe_core::durable::{export_header, export_rows, ExportRows, HostDeps};
use eukhe_core::iso_time::format_iso_now;
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::types::EntryRecord;
use serde_json::{json, Value};

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

fn header(deps: &HostDeps) -> Value {
    export_header(&deps.session_id, &deps.cwd.to_string_lossy())
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
    let ExportRows { entries, leaf_id } = export_rows(&history(conversation, cx).await?)?;
    let view = conversation
        .context(cx, eukhe_durable::harness::types::ContextOptions::default())
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
        entries,
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
    let rows = export_rows(&history(conversation, cx).await?)?.entries;
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
