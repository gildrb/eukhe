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

/// One `memory_update` session event.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename = "memory_update")]
pub struct MemoryUpdateEvent {
    pub update: MemoryUpdate,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memory_update_event_roundtrip() {
        crate::daemon::rt::<MemoryUpdateEvent>(
            r#"{"type":"memory_update","update":{"kind":"summarized","lines":[{"id":41,"count":1,"text":"user: hi"}],"viewBytes":87200}}"#,
        );
        crate::daemon::rt::<MemoryUpdateEvent>(
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
}
