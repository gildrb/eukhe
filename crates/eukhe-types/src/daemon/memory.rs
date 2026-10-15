//! The chat memory on the wire (Rust-native, advertised by the
//! [`MEMORY_CAPABILITY`] server capability): the `get_memory` reply that
//! `/memory` prints, and the ephemeral `memory_update` session event the
//! compactor's progress shows as. The chat's owner sends the same
//! [`MemoryUpdate`] to its clients over the chat's `lock` socket, so one
//! definition serves the owner, the daemon and the interactive client.
//!
//! Every update is display only: a client never logs it into the chat or
//! sends it to a model.

use serde::{Deserialize, Serialize};

/// The server capability that advertises `get_memory` and the
/// `memory_update` session event.
pub const MEMORY_CAPABILITY: &str = "memory";

/// The server capability that advertises `get_memory_tree`.
pub const MEMORY_TREE_CAPABILITY: &str = "memory_tree";

/// The view's sawtooth ceiling, in UTF-8 bytes of line text: once the view
/// passes it, one batch merges it down to [`MEMORY_VIEW_FLOOR`].
pub const MEMORY_VIEW_CEILING: u64 = 128_000;

/// The size a batch merges the view down to, in UTF-8 bytes.
pub const MEMORY_VIEW_FLOOR: u64 = 64_000;

/// One tree node as the view shows it: `id+n|text`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemoryLine {
    /// The first message the node covers.
    pub id: u64,
    /// How many messages it covers (a power of two).
    pub count: u64,
    /// Its summary, newlines kept.
    pub text: String,
}

/// What the compactor or the view just did.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum MemoryUpdate {
    /// Nodes were built (by the model, or free: a short message or two
    /// short lines), in the order they were built.
    Summarized {
        lines: Vec<MemoryLine>,
        /// The view's size after them, in bytes of line text.
        view_bytes: u64,
    },
    /// One batch merged the view down (§3.2's sawtooth).
    Merged {
        pairs: u64,
        before_bytes: u64,
        after_bytes: u64,
    },
}

/// The chat memory's state for the `/memory` header and the status gauge.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemoryStatusSnapshot {
    /// Messages in the chat (`T`).
    pub messages: u64,
    /// View lines.
    pub lines: u64,
    /// The view's size, in bytes of line text.
    pub view_bytes: u64,
    /// Messages whose view line is not summarized yet.
    pub unsummarized: u64,
    /// Compactor calls running or waiting out their retry delay.
    pub running: u64,
    /// The compactor model as configured (`provider/model-id`); `None`
    /// when it follows the default model.
    #[serde(default)]
    pub model: Option<String>,
    /// The newest compactor failure not resolved yet.
    #[serde(default)]
    pub last_error: Option<String>,
}

/// `zoom(id, n)` as `/memory zoom <id> <n>` asks it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemoryZoom {
    pub id: u64,
    pub count: u64,
}

/// The `get_memory` response data.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemoryReply {
    /// `None` when the session keeps no chat memory.
    #[serde(default)]
    pub memory: Option<MemorySnapshot>,
}

/// The chat memory at the moment of the request.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemorySnapshot {
    pub status: MemoryStatusSnapshot,
    /// Without a zoom: the view as the model sees it, one `id+n|text` line
    /// per node, oldest first, without the `<chat>` frame. With one: the
    /// zoom tool's answer, verbatim.
    pub text: String,
}

/// The `get_memory_tree` response data: one level of the memory tree, for
/// the `/memory` tree and the dashboard's Memory view.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemoryTreeReply {
    /// `None` when the session keeps no chat memory.
    #[serde(default)]
    pub tree: Option<MemoryTree>,
}

/// One level of the memory tree at the moment of the request.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemoryTree {
    pub status: MemoryStatusSnapshot,
    /// The line this level opens; `None` for the view (the top level, the
    /// lines the agent sees).
    #[serde(default)]
    pub node: Option<MemoryZoom>,
    pub level: MemoryTreeLevel,
}

/// What a line opens into: the view's lines, the two lines under a line
/// (`zoom(id, n)`), or, under a one-message line, the message whole.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum MemoryTreeLevel {
    /// Summary lines, oldest first.
    Lines { nodes: Vec<MemoryTreeNode> },
    /// The one message under a `id+1` line.
    Message { message: MemoryTreeMessage },
    /// The request names no line (`n` not a power of two, `id` not a
    /// multiple of `n`, or past the chat's end).
    NoLine,
}

/// One tree node (`id+n`) with what a reader needs to pick it: its time
/// span, the kinds of messages under it, and its summary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemoryTreeNode {
    /// The first message the node covers.
    pub id: u64,
    /// How many messages it covers (a power of two).
    pub count: u64,
    /// The date (`date(id)`, RFC 3339 with the local offset) of its first
    /// message.
    pub first_date: String,
    /// The date of its last message.
    pub last_date: String,
    /// The kinds of its messages with their counts, most frequent first
    /// (ties by kind name).
    pub kinds: Vec<MemoryKindCount>,
    /// Its summary, newlines kept; `None` while it is not summarized yet.
    #[serde(default)]
    pub summary: Option<String>,
}

/// How many messages of one kind (`user`, `talk`, `tool`, `echo`, `work`,
/// ...) a node covers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemoryKindCount {
    pub kind: String,
    pub count: u64,
}

/// One logged message, whole.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemoryTreeMessage {
    pub id: u64,
    pub kind: String,
    /// RFC 3339 with the local offset.
    pub date: String,
    pub text: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memory_update_event_roundtrip() {
        crate::daemon::rt::<crate::daemon::SessionEvent>(
            r#"{"type":"memory_update","update":{"kind":"summarized","lines":[{"id":41,"count":1,"text":"user: hi"}],"viewBytes":87200}}"#,
        );
        crate::daemon::rt::<crate::daemon::SessionEvent>(
            r#"{"type":"memory_update","update":{"kind":"merged","pairs":37,"beforeBytes":128400,"afterBytes":63900}}"#,
        );
    }

    #[test]
    fn memory_reply_roundtrip() {
        crate::daemon::rt::<MemoryReply>(
            r#"{"memory":{"status":{"messages":2,"lines":2,"viewBytes":20,"unsummarized":0,"running":0,"model":"anthropic/claude-haiku-4-5","lastError":null},"text":"0+1|user: hi\n1+1|talk: hello"}}"#,
        );
        crate::daemon::rt::<MemoryReply>(r#"{"memory":null}"#);
    }

    /// The tree reply's exact wire shape: the view level, an opened line,
    /// a message leaf, a bad request, and a session without memory.
    #[test]
    fn memory_tree_reply_wire_structure() {
        let status = MemoryStatusSnapshot {
            messages: 3,
            lines: 2,
            view_bytes: 30,
            unsummarized: 1,
            running: 0,
            model: None,
            last_error: None,
        };
        let view = MemoryTreeReply {
            tree: Some(MemoryTree {
                status,
                node: None,
                level: MemoryTreeLevel::Lines {
                    nodes: vec![
                        MemoryTreeNode {
                            id: 0,
                            count: 2,
                            first_date: "2026-10-01T09:00:00.000+02:00".to_string(),
                            last_date: "2026-10-02T10:00:00.000+02:00".to_string(),
                            kinds: vec![
                                MemoryKindCount {
                                    kind: "talk".to_string(),
                                    count: 1,
                                },
                                MemoryKindCount {
                                    kind: "user".to_string(),
                                    count: 1,
                                },
                            ],
                            summary: Some("user: hi\ntalk: hello".to_string()),
                        },
                        MemoryTreeNode {
                            id: 2,
                            count: 1,
                            first_date: "2026-10-03T08:00:00.000+02:00".to_string(),
                            last_date: "2026-10-03T08:00:00.000+02:00".to_string(),
                            kinds: vec![MemoryKindCount {
                                kind: "user".to_string(),
                                count: 1,
                            }],
                            summary: None,
                        },
                    ],
                },
            }),
        };
        assert_eq!(
            serde_json::to_value(&view).unwrap(),
            serde_json::json!({ "tree": {
                "status": { "messages": 3, "lines": 2, "viewBytes": 30, "unsummarized": 1, "running": 0, "model": null, "lastError": null },
                "node": null,
                "level": { "kind": "lines", "nodes": [
                    { "id": 0, "count": 2, "firstDate": "2026-10-01T09:00:00.000+02:00", "lastDate": "2026-10-02T10:00:00.000+02:00",
                      "kinds": [{ "kind": "talk", "count": 1 }, { "kind": "user", "count": 1 }], "summary": "user: hi\ntalk: hello" },
                    { "id": 2, "count": 1, "firstDate": "2026-10-03T08:00:00.000+02:00", "lastDate": "2026-10-03T08:00:00.000+02:00",
                      "kinds": [{ "kind": "user", "count": 1 }], "summary": null },
                ] },
            } })
        );
        crate::daemon::rt::<MemoryTreeReply>(
            r#"{"tree":{"status":{"messages":3,"lines":2,"viewBytes":30,"unsummarized":1,"running":0,"model":null,"lastError":null},"node":{"id":2,"count":1},"level":{"kind":"message","message":{"id":2,"kind":"user","date":"2026-10-03T08:00:00.000+02:00","text":"what now?"}}}}"#,
        );
        crate::daemon::rt::<MemoryTreeReply>(
            r#"{"tree":{"status":{"messages":3,"lines":2,"viewBytes":30,"unsummarized":1,"running":0,"model":null,"lastError":null},"node":{"id":1,"count":2},"level":{"kind":"no_line"}}}"#,
        );
        crate::daemon::rt::<MemoryTreeReply>(r#"{"tree":null}"#);
    }
}
