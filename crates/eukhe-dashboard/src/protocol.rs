//! The browser bridge's frames: JSON text messages on the tab's
//! WebSocket. The tab sends numbered requests; the server answers each
//! with a reply or a failure under the same number, and pushes the bound
//! session's events as they come.

use eukhe_types::daemon::{MemoryZoom, SessionEvent};
use serde::{Deserialize, Serialize};
use serde_json::Value;

/// One request from the tab.
#[derive(Debug, Clone, PartialEq, Deserialize)]
pub(crate) struct ClientFrame {
    pub(crate) id: u64,
    #[serde(flatten)]
    pub(crate) request: Request,
}

/// What the tab asks for.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", rename_all_fields = "camelCase")]
pub(crate) enum Request {
    /// The saved root sessions, newest first.
    Sessions,
    /// Bind the tab to a saved session (`path`), or to the newest root
    /// session (`None`; a new one when none is saved), and answer its
    /// transcript and state.
    Open {
        #[serde(default)]
        path: Option<String>,
    },
    /// Bind the tab to a new session.
    New,
    /// Send a message to the bound session; while a turn runs it waits as
    /// a steer (between tool calls) or a follow-up (after the turn).
    Prompt { text: String, mode: PromptMode },
    /// Stop the bound session's turn.
    Abort,
    /// One level of the chat memory's tree (`node` `None`: the view).
    Memory {
        #[serde(default)]
        node: Option<MemoryZoom>,
    },
}

/// How a message sent while a turn runs waits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) enum PromptMode {
    Steer,
    FollowUp,
}

/// One frame to the tab.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub(crate) enum ServerFrame<'a> {
    /// Request `id` succeeded.
    Reply { id: u64, data: Value },
    /// Request `id` failed.
    Failure { id: u64, error: String },
    /// One event of the bound session.
    Event { event: &'a SessionEvent },
    /// The bound session moved (a worker replacement) or closed: the tab
    /// opens it again.
    Resync { reason: String },
    /// The daemon is not reachable: the server closes the socket next and
    /// the tab tries again.
    Unavailable { error: String },
}

impl ServerFrame<'_> {
    /// The frame as JSON text; a frame that cannot encode becomes a
    /// failure (the encodings are total, so this never happens in
    /// practice).
    pub(crate) fn to_text(&self) -> String {
        serde_json::to_string(self).unwrap_or_else(|error| {
            serde_json::json!({ "type": "failure", "id": 0, "error": format!("encode: {error}") })
                .to_string()
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn requests_decode_from_the_tab_shapes() {
        let decode = |text: &str| serde_json::from_str::<ClientFrame>(text).unwrap();
        assert_eq!(
            decode(r#"{"id":1,"op":"open","path":null}"#),
            ClientFrame {
                id: 1,
                request: Request::Open { path: None }
            }
        );
        assert_eq!(
            decode(r#"{"id":2,"op":"prompt","text":"hi","mode":"followUp"}"#),
            ClientFrame {
                id: 2,
                request: Request::Prompt {
                    text: "hi".to_string(),
                    mode: PromptMode::FollowUp
                }
            }
        );
        assert_eq!(
            decode(r#"{"id":3,"op":"memory","node":{"id":8,"count":4}}"#),
            ClientFrame {
                id: 3,
                request: Request::Memory {
                    node: Some(MemoryZoom { id: 8, count: 4 })
                }
            }
        );
        assert_eq!(
            decode(r#"{"id":4,"op":"abort"}"#),
            ClientFrame {
                id: 4,
                request: Request::Abort
            }
        );
    }

    #[test]
    fn server_frames_encode_tagged() {
        assert_eq!(
            serde_json::to_value(ServerFrame::Failure {
                id: 7,
                error: "no".to_string()
            })
            .unwrap(),
            serde_json::json!({ "type": "failure", "id": 7, "error": "no" })
        );
        assert_eq!(
            serde_json::to_value(ServerFrame::Event {
                event: &SessionEvent::AgentStart
            })
            .unwrap(),
            serde_json::json!({ "type": "event", "event": { "type": "agent_start" } })
        );
    }
}
