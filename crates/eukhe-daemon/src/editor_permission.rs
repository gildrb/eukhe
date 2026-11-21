//! The editor's say on an irreversible effect (spec I12): the session's
//! `editor_permission` sink. A root session asks its attached editors (the
//! clients that attached with the `editor_permission` capability, which
//! only ACP attaches advertise) with one `editor_permission` frame; the
//! first `answer_editor_permission` for its request id decides. Allow
//! runs the effect and reject refuses it; `unsupported` (the editor has
//! no permission method) runs it, and nothing is asked again in this
//! session. With no editor attached, or when the last one detaches before
//! it answers, the effect runs. A subagent session asks no one itself: it
//! hands the question to its parent (`relay_editor_permission` over the
//! supervisor), naming itself as the subagent, and the question climbs to
//! the root.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_types::daemon::DaemonCommand;
use eukhe_types::effects::{EditorPermissionRequest, EditorVerdict};
use futures::future::BoxFuture;
use serde::Deserialize;
use serde_json::{json, Map, Value};
use tokio::sync::oneshot;

use crate::protocol::{response_failure, response_success, DaemonOutbound, DaemonResponse};
use crate::worker::{EventPump, OutboundFrame, SessionCore};

/// The private-frame `outboundType` of one question to the editors.
pub(crate) const EDITOR_PERMISSION_FRAME: &str = "editor_permission";

/// The client capability that receives the questions.
pub(crate) const EDITOR_PERMISSION_CAPABILITY: &str = "editor_permission";

const ANSWER_COMMAND: &str = "answer_editor_permission";

const RELAY_COMMAND: &str = "relay_editor_permission";

/// Sends one `relay_editor_permission` command and answers its response:
/// the worker's supervisor link (the supervisor routes the command to the
/// parent session's worker).
pub(crate) type Relay =
    Arc<dyn Fn(Value) -> BoxFuture<'static, anyhow::Result<DaemonResponse>> + Send + Sync>;

/// The session `core` is a child of, if any.
fn parent_of(core: &SessionCore) -> Option<String> {
    core.parent_session_id
        .clone()
        .or_else(|| core.parent_active_session_id.clone())
}

/// Who answers one question, as the session stands when it is asked.
enum Route {
    /// A subagent session: its parent, with the subagent named.
    Parent(String, EditorPermissionRequest),
    /// The root's editors: their answer arrives here.
    Editors(oneshot::Receiver<EditorVerdict>),
    /// No one: the effect runs.
    Nobody,
}

/// The session's open questions to its editors.
#[derive(Clone)]
pub(crate) struct EditorPermissions {
    core: Arc<Mutex<SessionCore>>,
    events: Arc<EventPump>,
    active_session_id: String,
    relay: Relay,
    /// The open questions by request id: each answer's way back.
    open: Arc<Mutex<HashMap<String, oneshot::Sender<EditorVerdict>>>>,
    /// An editor answered `unsupported`: nothing is asked again.
    unsupported: Arc<AtomicBool>,
}

impl EditorPermissions {
    pub(crate) fn new(
        core: Arc<Mutex<SessionCore>>,
        events: Arc<EventPump>,
        active_session_id: String,
        relay: Relay,
    ) -> Self {
        Self {
            core,
            events,
            active_session_id,
            relay,
            open: Arc::default(),
            unsupported: Arc::default(),
        }
    }

    fn lock_open(&self) -> MutexGuard<'_, HashMap<String, oneshot::Sender<EditorVerdict>>> {
        self.open.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// The editor's verdict on one irreversible effect of this session or
    /// of a subagent below it (the session's sink, and the answer of
    /// `relay_editor_permission`). [`EditorVerdict::Allow`] when no editor
    /// is asked or none answers.
    #[tracing::instrument(skip_all, fields(request_id = %request.request_id))]
    pub(crate) async fn ask(&self, request: EditorPermissionRequest) -> EditorVerdict {
        let route = self.route(request);
        let verdict = match route {
            Route::Parent(parent, request) => return self.relay_up(parent, request).await,
            Route::Nobody => return EditorVerdict::Allow,
            // A sender dropped unanswered: the last editor left.
            Route::Editors(answer) => answer.await.unwrap_or(EditorVerdict::Allow),
        };
        if verdict == EditorVerdict::Unsupported {
            self.unsupported.store(true, Ordering::SeqCst);
        }
        verdict
    }

    /// Who answers `request`; a question to the root's editors is open and
    /// sent when this returns. Who answers is read under the core lock,
    /// the lock the detach paths hold while they release the questions: a
    /// question asked before the last editor's detach is released by it.
    fn route(&self, mut request: EditorPermissionRequest) -> Route {
        let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(parent) = parent_of(&core) {
            if request.agent.is_none() {
                request.agent = Some(
                    core.session_name
                        .clone()
                        .or_else(|| core.rlm_child_id.clone())
                        .unwrap_or_else(|| self.active_session_id.clone()),
                );
            }
            return Route::Parent(parent, request);
        }
        if self.unsupported.load(Ordering::SeqCst) || core.editor_client_ids.is_empty() {
            return Route::Nobody;
        }
        let (answer, receiver) = oneshot::channel();
        self.lock_open().insert(request.request_id.clone(), answer);
        self.send(&request);
        Route::Editors(receiver)
    }

    /// `relay_editor_permission`: a subagent's question, handed up by a
    /// child session; answered like [`Self::ask`]. The data is
    /// `{"verdict": <EditorVerdict>}`.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn relay(&self, payload: &Value) -> DaemonResponse {
        let Some(request) = payload
            .get("request")
            .and_then(|request| EditorPermissionRequest::deserialize(request).ok())
        else {
            return response_failure(None, RELAY_COMMAND, "Invalid editor permission relay", None);
        };
        let verdict = self.ask(request).await;
        response_success(None, RELAY_COMMAND, Some(json!({ "verdict": verdict })))
    }

    /// Hand the question to the parent session and answer its verdict:
    /// [`EditorVerdict::Allow`] when the relay fails (logged), as with no
    /// editor.
    async fn relay_up(&self, parent: String, request: EditorPermissionRequest) -> EditorVerdict {
        let command = DaemonCommand::RelayEditorPermission {
            id: None,
            active_session_id: parent,
            request,
            rest: Map::default(),
        };
        let command = match serde_json::to_value(&command) {
            Ok(command) => command,
            Err(error) => {
                tracing::error!(%error, "the editor permission relay does not serialize");
                return EditorVerdict::Allow;
            }
        };
        match (self.relay)(command).await {
            Ok(DaemonResponse {
                success: true,
                data,
                ..
            }) => match data
                .as_ref()
                .and_then(|data| data.get("verdict"))
                .map(EditorVerdict::deserialize)
            {
                Some(Ok(verdict)) => verdict,
                Some(Err(error)) => {
                    tracing::warn!(%error, "the parent session's editor verdict is invalid");
                    EditorVerdict::Allow
                }
                None => {
                    tracing::warn!("the parent session's editor permission relay has no verdict");
                    EditorVerdict::Allow
                }
            },
            Ok(DaemonResponse { error, .. }) => {
                tracing::warn!(
                    ?error,
                    "the parent session refused the editor permission relay"
                );
                EditorVerdict::Allow
            }
            Err(error) => {
                tracing::warn!(error = %format!("{error:#}"), "the editor permission relay failed");
                EditorVerdict::Allow
            }
        }
    }

    /// `answer_editor_permission`: an editor's verdict on the question its
    /// frame named. An id no question is open under (answered already, or
    /// never asked) fails.
    pub(crate) fn answer(&self, payload: &Value) -> DaemonResponse {
        let request_id = payload
            .get("requestId")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let Some(verdict) = payload
            .get("verdict")
            .and_then(|verdict| EditorVerdict::deserialize(verdict).ok())
        else {
            return response_failure(
                None,
                ANSWER_COMMAND,
                "Invalid editor permission verdict",
                None,
            );
        };
        match self.lock_open().remove(request_id) {
            Some(answer) => {
                // The asking effect may have stopped waiting (its call
                // ended): the answer then reaches no one.
                let _ = answer.send(verdict);
                response_success(None, ANSWER_COMMAND, None)
            }
            None => response_failure(
                None,
                ANSWER_COMMAND,
                &format!("No open editor permission question: {request_id}"),
                None,
            ),
        }
    }

    /// A client detached (the detach paths call this with the core lock
    /// held, after the release): when no editor is left, every open
    /// question is released unanswered, and its effect runs.
    pub(crate) fn detached(&self, core: &SessionCore) {
        if core.editor_client_ids.is_empty() {
            self.lock_open().clear();
        }
    }

    /// Send one question to the session's editors.
    fn send(&self, request: &EditorPermissionRequest) {
        let outbound = DaemonOutbound::EditorPermission {
            active_session_id: self.active_session_id.clone(),
            request: request.clone(),
            rest: Map::default(),
        };
        match serde_json::to_vec(&outbound) {
            Ok(payload) => self.events.send(OutboundFrame::editor_permission(payload)),
            Err(error) => {
                tracing::error!(%error, "an editor permission frame does not serialize");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::sync::broadcast::{error::TryRecvError, Receiver};

    /// A root session's editor questions: no parent, so the relay never
    /// runs.
    fn permissions(editors: &[&str]) -> EditorPermissions {
        let mut core = SessionCore::test_core("/tmp".to_string());
        core.editor_client_ids = editors.iter().map(ToString::to_string).collect();
        EditorPermissions::new(
            Arc::new(Mutex::new(core)),
            Arc::new(EventPump::new()),
            "sess-1".to_string(),
            Arc::new(|command| panic!("a root session relayed {command}")),
        )
    }

    fn request(request_id: &str) -> EditorPermissionRequest {
        EditorPermissionRequest {
            request_id: request_id.to_string(),
            tool_call_id: Some("call-1".to_string()),
            command: "git push origin main".to_string(),
            classes: vec![eukhe_types::effects::EffectClass::Net],
            agent: None,
        }
    }

    /// The question's frame (the asking task runs concurrently).
    async fn next_frame(receiver: &mut Receiver<Arc<OutboundFrame>>) -> Value {
        let frame = tokio::time::timeout(std::time::Duration::from_secs(5), receiver.recv())
            .await
            .expect("frame in time")
            .expect("frame");
        assert_eq!(frame.outbound_type, EDITOR_PERMISSION_FRAME);
        serde_json::from_slice(&frame.payload).unwrap()
    }

    /// An editor's answer decides; `unsupported` runs the effect and
    /// nothing is asked again in the session.
    #[tokio::test]
    async fn the_editors_answer_decides_and_unsupported_asks_no_more() {
        let permissions = permissions(&["editor"]);
        let mut frames = permissions.events.subscribe();
        let mut verdicts = Vec::new();
        for (id, answer) in [("r1", "reject"), ("r2", "allow"), ("r3", "unsupported")] {
            let asking = tokio::spawn({
                let permissions = permissions.clone();
                let request = request(id);
                async move { permissions.ask(request).await }
            });
            let frame = next_frame(&mut frames).await;
            assert_eq!(
                frame,
                json!({
                    "type": "editor_permission",
                    "activeSessionId": "sess-1",
                    "request": {
                        "requestId": id,
                        "toolCallId": "call-1",
                        "command": "git push origin main",
                        "classes": ["net"],
                    },
                })
            );
            let answered = permissions.answer(&json!({ "requestId": id, "verdict": answer }));
            assert_eq!(answered, response_success(None, ANSWER_COMMAND, None));
            verdicts.push(asking.await.unwrap());
        }
        verdicts.push(permissions.ask(request("r4")).await);
        assert_eq!(
            (verdicts, frames.try_recv().err()),
            (
                vec![
                    EditorVerdict::Reject,
                    EditorVerdict::Allow,
                    EditorVerdict::Unsupported,
                    EditorVerdict::Allow,
                ],
                Some(TryRecvError::Empty)
            )
        );
    }

    /// With no editor attached nothing is asked: the effect runs.
    #[tokio::test]
    async fn with_no_editor_the_effect_runs_unasked() {
        let permissions = permissions(&[]);
        let mut frames = permissions.events.subscribe();
        assert_eq!(
            (
                permissions.ask(request("r1")).await,
                frames.try_recv().err()
            ),
            (EditorVerdict::Allow, Some(TryRecvError::Empty))
        );
    }

    /// The last editor detaches unanswered: the effect runs, and a late
    /// answer finds no question.
    #[tokio::test]
    async fn the_last_editor_detaching_unanswered_runs_the_effect() {
        let permissions = permissions(&["editor"]);
        let mut frames = permissions.events.subscribe();
        let asking = tokio::spawn({
            let permissions = permissions.clone();
            async move { permissions.ask(request("r1")).await }
        });
        next_frame(&mut frames).await;
        {
            let mut core = permissions.core.lock().unwrap();
            core.editor_client_ids.clear();
            permissions.detached(&core);
        }
        assert_eq!(
            (
                asking.await.unwrap(),
                permissions
                    .answer(&json!({ "requestId": "r1", "verdict": "reject" }))
                    .success
            ),
            (EditorVerdict::Allow, false)
        );
    }
}
