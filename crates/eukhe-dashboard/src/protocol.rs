//! The browser bridge's frames (protocol 3): JSON text messages on the
//! tab's WebSocket. The tab's first frame pairs (`pair` with the token);
//! the server answers `unpaired` and closes, or greets with `hello`. Then
//! the tab sends numbered requests, which run concurrently, and the
//! server answers each with a reply or a failure under the same number.
//! The bound session's events, approval questions and resyncs are pushed
//! as they come.

use eukhe_types::daemon::{DaemonResumeCursor, MemoryZoom, SessionEvent};
use eukhe_types::shell::ShellApprovalRequest;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};

/// The protocol version `hello` announces.
pub(crate) const PROTOCOL_VERSION: u32 = 3;

/// The ops a tab may send, as `hello` lists them.
pub(crate) const OPS: [&str; 10] = [
    "sessions", "open", "new", "prompt", "abort", "memory", "run", "export", "delete", "rename",
];

/// The tab's first frame: the pairing token from the page's URL
/// fragment.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub(crate) enum Pairing {
    Pair { token: String },
}

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
    /// Bind the tab to a saved root session (by `session_id` or `path`),
    /// or to the newest one (neither; a new one when none is saved), and
    /// answer its transcript, state and resume cursor. With `resume` (the
    /// cursor of the last event the tab saw) the reply says whether the
    /// tab missed anything.
    Open {
        #[serde(default)]
        session_id: Option<String>,
        #[serde(default)]
        path: Option<String>,
        #[serde(default)]
        resume: Option<DaemonResumeCursor>,
    },
    /// Bind the tab to a new session in `cwd` (the dashboard's new-session
    /// folder when absent).
    New {
        #[serde(default)]
        cwd: Option<String>,
    },
    /// Send a message to the bound session; while a turn runs it waits as
    /// a steer (between tool calls) or a follow-up (after the turn). The
    /// tab's `admission_id` makes a retried send idempotent.
    Prompt {
        text: String,
        mode: PromptMode,
        #[serde(default)]
        admission_id: Option<String>,
        #[serde(default)]
        images: Vec<PromptImage>,
    },
    /// Stop the bound session's turn.
    Abort,
    /// One level of the chat memory's tree (`node` `None`: the view).
    Memory {
        #[serde(default)]
        node: Option<MemoryZoom>,
    },
    /// One daemon command for the bound session (`type`-tagged, camelCase
    /// fields, without `activeSessionId`: the bridge sets it).
    Run { command: Map<String, Value> },
    /// The bound session's transcript as a file the browser saves: the
    /// daemon writes it into a private temporary folder and the bridge
    /// answers its bytes.
    Export { format: ExportFormat },
    /// Delete a saved root session. A worker that hosts it is stopped
    /// first when no other client is attached to it; the tab's own
    /// binding lets it go.
    Delete { session_id: String },
    /// Rename a saved root session: through the worker that hosts it, else
    /// in the saved file.
    Rename { session_id: String, name: String },
}

/// The file an `export` makes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ExportFormat {
    /// The standalone viewer page.
    Html,
    /// The history as a linear session file.
    Jsonl,
}

/// How a message sent while a turn runs waits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) enum PromptMode {
    Steer,
    FollowUp,
}

/// One image a message carries.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct PromptImage {
    /// Base64, without a `data:` prefix.
    pub(crate) data: String,
    pub(crate) mime_type: String,
}

/// Where an event sits in the session's event stream: the tab's resume
/// cursor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) struct EventCursor<'a> {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) generation: Option<&'a str>,
    pub(crate) sequence: u64,
}

/// One frame to the tab.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub(crate) enum ServerFrame<'a> {
    /// The first frame on every socket.
    Hello {
        protocol: u32,
        /// Changes whenever the eukhe build or any web file does.
        build: &'a str,
        ops: &'a [&'a str],
    },
    /// Request `id` succeeded.
    Reply { id: u64, data: Value },
    /// Request `id` failed.
    Failure { id: u64, error: String },
    /// One event of the bound session, with its cursor when the daemon
    /// gave one.
    Event {
        event: &'a SessionEvent,
        #[serde(skip_serializing_if = "Option::is_none")]
        cursor: Option<EventCursor<'a>>,
    },
    /// The bound session's `bash` tool asks whether one step may run; the
    /// tab answers with `run` `answer_shell_approval`.
    Approval { request: &'a ShellApprovalRequest },
    /// The bound session no longer waits on question `request_id` (a
    /// client answered it, its step ended, or it went elsewhere): the tab
    /// drops its card.
    ApprovalSettled { request_id: &'a str },
    /// The bound session moved (a worker replacement), lost its worker
    /// link, or closed: the tab opens it again.
    Resync { reason: String },
    /// The daemon is not reachable: the server closes the socket next and
    /// the tab tries again.
    Unavailable { error: String },
    /// The socket did not present the current pairing token: nothing ran,
    /// and the server closes the socket next. The tab asks for the
    /// pairing link.
    Unpaired { error: &'a str },
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
    use eukhe_types::shell::{ShellEffect, ShellEffects};
    use serde_json::json;

    #[test]
    fn requests_decode_from_the_tab_shapes() {
        let decode = |text: &str| serde_json::from_str::<ClientFrame>(text).unwrap();
        assert_eq!(
            decode(r#"{"id":1,"op":"open","path":null}"#),
            ClientFrame {
                id: 1,
                request: Request::Open {
                    session_id: None,
                    path: None,
                    resume: None
                }
            }
        );
        assert_eq!(
            decode(
                r#"{"id":1,"op":"open","sessionId":"s","resume":{"generation":"g","sequence":4}}"#
            ),
            ClientFrame {
                id: 1,
                request: Request::Open {
                    session_id: Some("s".to_string()),
                    path: None,
                    resume: Some(DaemonResumeCursor {
                        active_session_id: None,
                        generation: Some("g".to_string()),
                        sequence: Some(4),
                        event_sequence: None,
                    })
                }
            }
        );
        assert_eq!(
            decode(r#"{"id":2,"op":"new"}"#),
            ClientFrame {
                id: 2,
                request: Request::New { cwd: None }
            }
        );
        assert_eq!(
            decode(r#"{"id":2,"op":"new","cwd":"/w"}"#),
            ClientFrame {
                id: 2,
                request: Request::New {
                    cwd: Some("/w".to_string())
                }
            }
        );
        assert_eq!(
            decode(r#"{"id":2,"op":"prompt","text":"hi","mode":"followUp"}"#),
            ClientFrame {
                id: 2,
                request: Request::Prompt {
                    text: "hi".to_string(),
                    mode: PromptMode::FollowUp,
                    admission_id: None,
                    images: Vec::new(),
                }
            }
        );
        assert_eq!(
            decode(
                r#"{"id":2,"op":"prompt","text":"hi","mode":"steer","admissionId":"a1","images":[{"data":"AA==","mimeType":"image/png"}]}"#
            ),
            ClientFrame {
                id: 2,
                request: Request::Prompt {
                    text: "hi".to_string(),
                    mode: PromptMode::Steer,
                    admission_id: Some("a1".to_string()),
                    images: vec![PromptImage {
                        data: "AA==".to_string(),
                        mime_type: "image/png".to_string()
                    }],
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
        assert_eq!(
            decode(r#"{"id":5,"op":"run","command":{"type":"get_queue"}}"#),
            ClientFrame {
                id: 5,
                request: Request::Run {
                    command: Map::from_iter([("type".to_string(), json!("get_queue"))])
                }
            }
        );
    }

    #[test]
    fn export_requests_decode_by_format() {
        let decode = |text: &str| serde_json::from_str::<ClientFrame>(text).unwrap();
        assert_eq!(
            [
                decode(r#"{"id":6,"op":"export","format":"html"}"#),
                decode(r#"{"id":7,"op":"export","format":"jsonl"}"#),
            ],
            [
                ClientFrame {
                    id: 6,
                    request: Request::Export {
                        format: ExportFormat::Html
                    }
                },
                ClientFrame {
                    id: 7,
                    request: Request::Export {
                        format: ExportFormat::Jsonl
                    }
                },
            ]
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
            json!({ "type": "failure", "id": 7, "error": "no" })
        );
        assert_eq!(
            serde_json::to_value(ServerFrame::Event {
                event: &SessionEvent::AgentStart,
                cursor: None,
            })
            .unwrap(),
            json!({ "type": "event", "event": { "type": "agent_start" } })
        );
        assert_eq!(
            serde_json::to_value(ServerFrame::Event {
                event: &SessionEvent::AgentStart,
                cursor: Some(EventCursor {
                    generation: Some("g"),
                    sequence: 9
                }),
            })
            .unwrap(),
            json!({
                "type": "event",
                "event": { "type": "agent_start" },
                "cursor": { "generation": "g", "sequence": 9 },
            })
        );
        assert_eq!(
            serde_json::to_value(ServerFrame::Hello {
                protocol: PROTOCOL_VERSION,
                build: "b",
                ops: &OPS,
            })
            .unwrap(),
            json!({
                "type": "hello", "protocol": 3, "build": "b",
                "ops": ["sessions", "open", "new", "prompt", "abort", "memory", "run", "export", "delete", "rename"],
            })
        );
        assert_eq!(
            serde_json::to_value(ServerFrame::Approval {
                request: &ShellApprovalRequest {
                    request_id: "r1".to_string(),
                    step: 0,
                    command: "rm -rf build".to_string(),
                    effects: ShellEffects::of(&[ShellEffect::Write]),
                }
            })
            .unwrap(),
            json!({
                "type": "approval",
                "request": { "requestId": "r1", "step": 0, "command": "rm -rf build", "effects": ["write"] },
            })
        );
        assert_eq!(
            serde_json::to_value(ServerFrame::Unpaired { error: "no" }).unwrap(),
            json!({ "type": "unpaired", "error": "no" })
        );
    }
}
