//! The `get_chat_view` reply (Rust-native, advertised by the
//! [`CHAT_VIEW_CAPABILITY`] server capability): the chat memory's view as
//! the session's next fresh turn sees it, for the interactive client's
//! startup block (`OptChat` spec §10: "On start, print the view, so you see what
//! the agent sees").

use serde::{Deserialize, Serialize};

/// The server capability that advertises the `get_chat_view` command.
pub const CHAT_VIEW_CAPABILITY: &str = "chat_view";

/// The `get_chat_view` response data.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ChatViewReply {
    /// `None` when the session keeps no chat memory: a subagent (its view
    /// rides its own first message) or the faux verification harness.
    #[serde(default)]
    pub view: Option<ChatViewSnapshot>,
}

/// The chat view at the moment of the request.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ChatViewSnapshot {
    /// The agent's rendering: `<chat>`, one `id+n|text` line per part,
    /// `</chat>`.
    pub text: String,
    /// Messages the view covers.
    pub messages: u64,
    /// View lines (one per part).
    pub lines: u64,
    /// The rendered text's size in bytes.
    pub bytes: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chat_view_reply_roundtrip() {
        crate::daemon::rt::<ChatViewReply>(
            r#"{"view":{"text":"<chat>\n0+1|hello\n</chat>","messages":1,"lines":1,"bytes":25}}"#,
        );
        crate::daemon::rt::<ChatViewReply>(r#"{"view":null}"#);
    }

    /// A reply without the `view` key (an older or partial answer) reads
    /// as no view instead of a decode failure.
    #[test]
    fn a_reply_without_a_view_reads_as_none() {
        let reply: ChatViewReply = serde_json::from_str("{}").expect("decodes");
        assert_eq!(reply, ChatViewReply { view: None });
    }
}
