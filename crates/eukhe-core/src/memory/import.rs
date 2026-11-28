//! Importing history: older agent sessions as plain text (the user's
//! messages and the agent's final replies, without repeated pastes and
//! tool noise), each logged as a `note` message, "memories imported from
//! before the chat" (spec §1), that names its author as `user: ` or
//! `eukhe: `. The compactor then builds the tree over them like any other
//! messages.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use serde::Deserialize;

use super::service::ImportItem;
use super::{labeled, Kind, Memory};

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
            items.push(ImportItem {
                kind: Kind::Note,
                text: labeled(item.kind, &item.text),
                date: item.date,
            });
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
    let (first, count) = memory.import(batch).await?;
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

/// A row field read only when it has the expected shape; any other value
/// reads as absent instead of failing the row.
#[derive(Deserialize)]
#[serde(untagged)]
enum Field<T> {
    Typed(T),
    Other(serde::de::IgnoredAny),
}

impl<T> Field<T> {
    fn typed(field: Option<Self>) -> Option<T> {
        match field {
            Some(Self::Typed(value)) => Some(value),
            Some(Self::Other(_)) | None => None,
        }
    }
}

/// The row `type`s the import tells apart.
#[derive(Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum RowKind {
    Session,
    Message,
    #[serde(other)]
    Other,
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum Role {
    User,
    Assistant,
    #[serde(other)]
    Other,
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum BlockKind {
    Text,
    #[serde(other)]
    Other,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct HeaderRow {
    #[serde(rename = "type")]
    kind: Option<Field<RowKind>>,
    rlm_depth: Option<Field<u64>>,
    timestamp: Option<Field<String>>,
}

#[derive(Deserialize)]
struct EntryRow {
    #[serde(rename = "type")]
    kind: Option<Field<RowKind>>,
    message: Option<Field<MessageRow>>,
    timestamp: Option<Field<String>>,
}

#[derive(Deserialize)]
struct MessageRow {
    role: Option<Field<Role>>,
    content: Option<Field<Content>>,
}

#[derive(Deserialize)]
#[serde(untagged)]
enum Content {
    Text(String),
    Blocks(Vec<Field<Block>>),
}

#[derive(Deserialize)]
struct Block {
    #[serde(rename = "type")]
    kind: Option<Field<BlockKind>>,
    text: Option<Field<String>>,
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
    let Ok(header) = serde_json::from_str::<HeaderRow>(header) else {
        return Ok(None);
    };
    if Field::typed(header.kind) != Some(RowKind::Session) {
        return Ok(None);
    }
    if Field::typed(header.rlm_depth).unwrap_or(0) > 0 {
        return Ok(None);
    }
    let start = Field::typed(header.timestamp).unwrap_or_default();
    let mut items = Vec::new();
    let mut reply: Option<ImportItem> = None;
    for line in lines {
        // A torn or foreign line is skipped, like the chat's own loader.
        let Ok(entry) = serde_json::from_str::<EntryRow>(line) else {
            continue;
        };
        if Field::typed(entry.kind) != Some(RowKind::Message) {
            continue;
        }
        let Some(message) = entry.message else {
            continue;
        };
        let date = Field::typed(entry.timestamp)
            .as_deref()
            .map(local_date)
            .transpose()?
            .unwrap_or_default();
        let Some(message) = Field::typed(Some(message)) else {
            continue;
        };
        let text = message_text(Field::typed(message.content));
        match Field::typed(message.role) {
            Some(Role::User) => {
                items.extend(reply.take());
                if !text.trim().is_empty() {
                    items.push(ImportItem {
                        kind: Kind::User,
                        text,
                        date,
                    });
                }
            }
            Some(Role::Assistant) if !text.trim().is_empty() => {
                reply = Some(ImportItem {
                    kind: Kind::Eukhe,
                    text,
                    date,
                });
            }
            Some(Role::Assistant | Role::Other) | None => {}
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
fn message_text(content: Option<Content>) -> String {
    match content {
        Some(Content::Text(text)) => text,
        Some(Content::Blocks(blocks)) => {
            let mut text = String::new();
            let texts = blocks.into_iter().filter_map(|block| match block {
                Field::Typed(block)
                    if matches!(block.kind, Some(Field::Typed(BlockKind::Text))) =>
                {
                    Field::typed(block.text)
                }
                Field::Typed(_) | Field::Other(_) => None,
            });
            for (index, block) in texts.enumerate() {
                if index > 0 {
                    text.push('\n');
                }
                text.push_str(&block);
            }
            text
        }
        None => String::new(),
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
    use crate::memory::compactor::tests::Scripted;

    /// Every message of the chat, as `id+0|kind: text`.
    async fn log(memory: &Memory) -> Vec<String> {
        let total = memory.status().await.unwrap().messages;
        let mut lines = Vec::new();
        for id in 0..total {
            lines.push(memory.zoom(id, 1).await.unwrap().text);
        }
        lines
    }

    fn session(start: &str, depth: u32, messages: &[(&str, &str)]) -> String {
        let mut lines = vec![serde_json::json!({
            "type": "session",
            "timestamp": start,
            "rlmDepth": depth
        })
        .to_string()];
        for (role, text) in messages {
            lines.push(
                serde_json::json!({
                    "type": "message",
                    "timestamp": start,
                    "message": { "role": role, "content": [{ "type": "text", "text": text }] }
                })
                .to_string(),
            );
        }
        lines.join("\n")
    }

    #[test]
    fn sessions_keep_user_words_and_final_replies() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("a.jsonl");
        let lines = [
            r#"{"type":"session","timestamp":"2026-10-01T10:00:00.000Z","rlmDepth":0}"#,
            r#"{"type":"message","timestamp":"2026-10-01T10:00:01.000Z","message":{"role":"user","content":[{"type":"text","text":"fix the bug"}]}}"#,
            r#"{"type":"message","timestamp":"2026-10-01T10:00:02.000Z","message":{"role":"assistant","content":[{"type":"text","text":"looking"},{"type":"toolCall","id":"1","name":"python","arguments":{}}]}}"#,
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
            vec![(Kind::User, "fix the bug"), (Kind::Eukhe, "fixed in a.rs")]
        );
    }

    #[test]
    fn subagent_sessions_are_skipped() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("child.jsonl");
        std::fs::write(&path, session("2026-10-01T10:00:00.000Z", 1, &[])).unwrap();
        assert!(parse_session(&path).unwrap().is_none());
    }

    /// Sessions go in oldest first, as `note` messages naming their author
    /// (§1): the user's words and the final replies, without repeated
    /// pastes or subagent sessions.
    #[tokio::test]
    async fn sessions_import_oldest_first_without_repeated_pastes() {
        let chat = tempfile::tempdir().unwrap();
        let sessions = tempfile::tempdir().unwrap();
        let paste = "p".repeat(PASTE_CHARS + 1);
        std::fs::write(
            sessions.path().join("a-later.jsonl"),
            session(
                "2026-10-02T10:00:00.000Z",
                0,
                &[
                    ("user", &paste),
                    ("user", "thanks"),
                    ("assistant", "welcome"),
                ],
            ),
        )
        .unwrap();
        std::fs::write(
            sessions.path().join("b-earlier.jsonl"),
            session(
                "2026-10-01T10:00:00.000Z",
                0,
                &[
                    ("user", "fix the bug"),
                    ("assistant", "fixed in a.rs"),
                    ("user", &paste),
                    ("assistant", "ok"),
                ],
            ),
        )
        .unwrap();
        std::fs::create_dir(sessions.path().join("children")).unwrap();
        std::fs::write(
            sessions.path().join("children").join("c.jsonl"),
            session("2026-10-01T11:00:00.000Z", 1, &[("user", "subtask")]),
        )
        .unwrap();
        let memory = Memory::open(chat.path(), Scripted::with(Vec::new()))
            .await
            .unwrap();
        memory.append(Kind::User, "already here").await.unwrap();
        let report = import_sessions(&memory, &[sessions.path().to_path_buf()])
            .await
            .unwrap();
        assert_eq!(
            (report, log(&memory).await),
            (
                ImportReport {
                    first: Some(1),
                    count: 6,
                    sessions: 2,
                    skipped: 2,
                },
                vec![
                    "0+0|user: already here".to_string(),
                    "1+0|note: user: fix the bug".to_string(),
                    "2+0|note: eukhe: fixed in a.rs".to_string(),
                    format!("3+0|note: user: {paste}"),
                    "4+0|note: eukhe: ok".to_string(),
                    "5+0|note: user: thanks".to_string(),
                    "6+0|note: eukhe: welcome".to_string(),
                ]
            )
        );
    }
}
