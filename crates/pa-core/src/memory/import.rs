//! Importing history (`docs/optchat.md` §10): OptMem notes as kind `note`,
//! keeping their ids, and older agent sessions as plain text (the user's
//! messages and the agent's final replies, without repeated pastes and
//! tool noise). The compactor then builds the tree over them like any other
//! messages.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use super::service::ImportItem;
use super::{Kind, Memory};

/// A user message longer than this that repeats an earlier one exactly is
/// a repeated paste and is skipped; shorter repeats ("continue") stay.
const PASTE_CHARS: usize = 280;
/// Items per import request (each request is one socket line).
const BATCH_ITEMS: usize = 500;
/// Bytes of text per import request.
const BATCH_BYTES: usize = 8 * 1024 * 1024;

/// What an import wrote.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ImportReport {
    /// The id of the first imported message (`None` when nothing was new).
    pub first: Option<u64>,
    pub count: u64,
    /// Sessions read.
    pub sessions: u64,
    /// Subagent sessions and repeated pastes left out.
    pub skipped: u64,
}

/// Import the OptMem memory in `memory_dir` (its `LOG.txt`) as `note`
/// messages with their own ids: the chat must still be empty.
///
/// # Errors
///
/// Returns an error when `LOG.txt` cannot be read, its records are not
/// `#0, #1, ...` in order, or the chat is not empty.
pub async fn import_optmem(memory: &Memory, memory_dir: &Path) -> anyhow::Result<ImportReport> {
    let log = memory_dir.join("LOG.txt");
    let text = std::fs::read_to_string(&log)
        .map_err(|error| anyhow::anyhow!("cannot read {}: {error}", log.display()))?;
    let mut items = Vec::new();
    for (expected, line) in text.lines().enumerate() {
        let line = line.trim_end();
        let (head, rest) = line
            .split_once(' ')
            .ok_or_else(|| anyhow::anyhow!("{}: record {expected} is malformed", log.display()))?;
        let id: usize = head
            .strip_prefix('#')
            .and_then(|digits| digits.parse().ok())
            .ok_or_else(|| anyhow::anyhow!("{}: record {expected} has no #id", log.display()))?;
        if id != expected {
            anyhow::bail!(
                "{}: expected record #{expected}, found #{id}",
                log.display()
            );
        }
        let (date, note) = rest.split_once(' ').unwrap_or((rest, ""));
        items.push(ImportItem {
            kind: Kind::Note,
            text: note.to_string(),
            date: date.to_string(),
        });
    }
    let count = items.len() as u64;
    if count == 0 {
        return Ok(ImportReport::default());
    }
    // One request keeps the ids: the owner writes all or nothing, and only
    // into an empty chat.
    let (first, written) = memory.import(Some(0), items).await?;
    Ok(ImportReport {
        first: Some(first),
        count: written,
        sessions: 0,
        skipped: 0,
    })
}

/// Import the root sessions found in `paths` (session `.jsonl` files or
/// directories searched recursively), oldest first.
///
/// # Errors
///
/// Returns an error when a path cannot be read or the owner refuses a
/// batch.
pub async fn import_sessions(memory: &Memory, paths: &[PathBuf]) -> anyhow::Result<ImportReport> {
    let mut files = Vec::new();
    for path in paths {
        collect_session_files(path, &mut files)?;
    }
    let mut sessions = Vec::new();
    let mut report = ImportReport::default();
    for file in files {
        match parse_session(&file)? {
            Some(session) => sessions.push(session),
            None => report.skipped += 1,
        }
    }
    sessions.sort_by(|left, right| {
        left.start
            .cmp(&right.start)
            .then(left.path.cmp(&right.path))
    });
    let mut seen_pastes: HashSet<String> = HashSet::new();
    let mut items: Vec<ImportItem> = Vec::new();
    for session in sessions {
        report.sessions += 1;
        for item in session.items {
            if item.kind == Kind::User
                && item.text.chars().count() > PASTE_CHARS
                && !seen_pastes.insert(item.text.clone())
            {
                report.skipped += 1;
                continue;
            }
            items.push(item);
        }
    }
    let mut batch: Vec<ImportItem> = Vec::new();
    let mut batch_bytes = 0;
    for item in items {
        if !batch.is_empty()
            && (batch.len() >= BATCH_ITEMS || batch_bytes + item.text.len() > BATCH_BYTES)
        {
            write_batch(memory, std::mem::take(&mut batch), &mut report).await?;
            batch_bytes = 0;
        }
        batch_bytes += item.text.len();
        batch.push(item);
    }
    if !batch.is_empty() {
        write_batch(memory, batch, &mut report).await?;
    }
    Ok(report)
}

async fn write_batch(
    memory: &Memory,
    batch: Vec<ImportItem>,
    report: &mut ImportReport,
) -> anyhow::Result<()> {
    let (first, count) = memory.import(None, batch).await?;
    report.first.get_or_insert(first);
    report.count += count;
    Ok(())
}

fn collect_session_files(path: &Path, files: &mut Vec<PathBuf>) -> anyhow::Result<()> {
    let metadata = std::fs::metadata(path)
        .map_err(|error| anyhow::anyhow!("cannot read {}: {error}", path.display()))?;
    if metadata.is_file() {
        files.push(path.to_path_buf());
        return Ok(());
    }
    let mut entries: Vec<PathBuf> = std::fs::read_dir(path)?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<Result<_, _>>()?;
    entries.sort();
    for entry in entries {
        if entry.is_dir() {
            collect_session_files(&entry, files)?;
        } else if entry
            .extension()
            .is_some_and(|extension| extension == "jsonl")
        {
            files.push(entry);
        }
    }
    Ok(())
}

/// One session's importable messages.
struct Session {
    path: PathBuf,
    start: String,
    items: Vec<ImportItem>,
}

/// The user's messages and each turn's final reply. `None` for subagent
/// sessions and files without a session header.
fn parse_session(path: &Path) -> anyhow::Result<Option<Session>> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| anyhow::anyhow!("cannot read {}: {error}", path.display()))?;
    let mut lines = text.lines().filter(|line| !line.trim().is_empty());
    let Some(header) = lines.next() else {
        return Ok(None);
    };
    let Ok(header) = serde_json::from_str::<serde_json::Value>(header) else {
        return Ok(None);
    };
    if header.get("type").and_then(serde_json::Value::as_str) != Some("session") {
        return Ok(None);
    }
    if header
        .get("rlmDepth")
        .and_then(serde_json::Value::as_u64)
        .unwrap_or(0)
        > 0
    {
        return Ok(None);
    }
    let start = header
        .get("timestamp")
        .and_then(serde_json::Value::as_str)
        .unwrap_or_default()
        .to_string();
    let mut items = Vec::new();
    let mut reply: Option<ImportItem> = None;
    for line in lines {
        // A torn or foreign line is skipped, like the chat's own loader.
        let Ok(entry) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        if entry.get("type").and_then(serde_json::Value::as_str) != Some("message") {
            continue;
        }
        let Some(message) = entry.get("message") else {
            continue;
        };
        let date = entry
            .get("timestamp")
            .and_then(serde_json::Value::as_str)
            .map(local_date)
            .transpose()?
            .unwrap_or_default();
        let text = message_text(message);
        match message.get("role").and_then(serde_json::Value::as_str) {
            Some("user") => {
                items.extend(reply.take());
                if !text.trim().is_empty() {
                    items.push(ImportItem {
                        kind: Kind::User,
                        text,
                        date,
                    });
                }
            }
            Some("assistant") => {
                if !text.trim().is_empty() {
                    reply = Some(ImportItem {
                        kind: Kind::Talk,
                        text,
                        date,
                    });
                }
            }
            _ => {}
        }
    }
    items.extend(reply);
    Ok(Some(Session {
        path: path.to_path_buf(),
        start,
        items,
    }))
}

/// The text blocks of a stored message, joined by newlines.
fn message_text(message: &serde_json::Value) -> String {
    match message.get("content") {
        Some(serde_json::Value::String(text)) => text.clone(),
        Some(serde_json::Value::Array(blocks)) => blocks
            .iter()
            .filter(|block| block.get("type").and_then(serde_json::Value::as_str) == Some("text"))
            .filter_map(|block| block.get("text").and_then(serde_json::Value::as_str))
            .collect::<Vec<_>>()
            .join("\n"),
        _ => String::new(),
    }
}

/// A session timestamp (UTC ISO) as the local RFC 3339 date the chat
/// stores; other shapes are kept as written.
fn local_date(timestamp: &str) -> anyhow::Result<String> {
    match crate::platform::parse_utc_iso(timestamp) {
        Some(instant) => Ok(crate::platform::local_time(instant)?.rfc3339()),
        None => Ok(timestamp.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sessions_keep_user_words_and_final_replies() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("a.jsonl");
        let lines = [
            r#"{"type":"session","timestamp":"2026-10-01T10:00:00.000Z","rlmDepth":0}"#,
            r#"{"type":"message","timestamp":"2026-10-01T10:00:01.000Z","message":{"role":"user","content":[{"type":"text","text":"fix the bug"}]}}"#,
            r#"{"type":"message","timestamp":"2026-10-01T10:00:02.000Z","message":{"role":"assistant","content":[{"type":"text","text":"looking"},{"type":"toolCall","id":"1","name":"ipython","arguments":{}}]}}"#,
            r#"{"type":"message","timestamp":"2026-10-01T10:00:03.000Z","message":{"role":"toolResult","content":[{"type":"text","text":"noise"}]}}"#,
            r#"{"type":"message","timestamp":"2026-10-01T10:00:04.000Z","message":{"role":"assistant","content":[{"type":"text","text":"fixed in a.rs"}]}}"#,
            r#"{"type":"agent_status","timestamp":"2026-10-01T10:00:05.000Z"}"#,
            "{torn",
        ];
        std::fs::write(&path, lines.join("\n")).unwrap();
        let session = parse_session(&path).unwrap().unwrap();
        let summary: Vec<(Kind, &str)> = session
            .items
            .iter()
            .map(|item| (item.kind, item.text.as_str()))
            .collect();
        assert_eq!(
            summary,
            vec![(Kind::User, "fix the bug"), (Kind::Talk, "fixed in a.rs")]
        );
    }

    #[test]
    fn subagent_sessions_are_skipped() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("child.jsonl");
        std::fs::write(
            &path,
            r#"{"type":"session","timestamp":"2026-10-01T10:00:00.000Z","rlmDepth":1}"#,
        )
        .unwrap();
        assert!(parse_session(&path).unwrap().is_none());
    }
}
