//! The worker's pending shell approvals: the `bash` tool asks the attached
//! clients whether one step may run (a `shell_approval` frame), and the
//! first `answer_shell_approval` for its request id wins. A session with no
//! attached client has no one to ask, and the last detach drops every
//! pending question: both leave the step unanswered, which the tool treats
//! as a denial.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::shell::{ShellApprovalRequest, ShellVerdict};
use serde::Deserialize;
use serde_json::{Map, Value};
use tokio::sync::oneshot;

use crate::protocol::{response_failure, response_success, DaemonOutbound, DaemonResponse};
use crate::worker::{EventPump, OutboundFrame, SessionCore};

/// The private-frame `outboundType` of one shell approval question.
pub(crate) const SHELL_APPROVAL_FRAME: &str = "shell_approval";

const ANSWER_COMMAND: &str = "answer_shell_approval";

/// Request id -> the waiting step's answer slot.
type Pending = HashMap<String, oneshot::Sender<ShellVerdict>>;

/// The session's open shell approval questions.
#[derive(Clone)]
pub(crate) struct ShellApprovals {
    core: Arc<Mutex<SessionCore>>,
    events: Arc<EventPump>,
    active_session_id: String,
    pending: Arc<Mutex<Pending>>,
}

impl ShellApprovals {
    pub(crate) fn new(
        core: Arc<Mutex<SessionCore>>,
        events: Arc<EventPump>,
        active_session_id: String,
    ) -> Self {
        Self {
            core,
            events,
            active_session_id,
            pending: Arc::default(),
        }
    }

    /// Ask the attached clients about one step (the session's
    /// `shell_approval` sink). `None` when no client is attached (no frame
    /// goes out), when the frame does not serialize (logged; no question
    /// stays pending), or when every client detached before an answer came.
    #[tracing::instrument(skip_all, fields(request_id = %request.request_id, step = request.step))]
    pub(crate) async fn ask(&self, request: ShellApprovalRequest) -> Option<ShellVerdict> {
        let request_id = request.request_id.clone();
        let outbound = DaemonOutbound::ShellApproval {
            active_session_id: self.active_session_id.clone(),
            request,
            rest: Map::default(),
        };
        let payload = match serde_json::to_vec(&outbound) {
            Ok(payload) => payload,
            Err(error) => {
                tracing::error!(%error, "the shell approval frame does not serialize");
                return None;
            }
        };
        let receiver = {
            // The attach check and the insert hold the core lock, the lock
            // the detach paths hold while they drop the pending answers: a
            // question is either refused here or dropped by the last detach.
            let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
            if core.attached_client_ids.is_empty() {
                return None;
            }
            let (sender, receiver) = oneshot::channel();
            let mut pending = self.pending.lock().unwrap_or_else(PoisonError::into_inner);
            // A step whose wait was cancelled leaves a closed slot behind.
            pending.retain(|_, slot| !slot.is_closed());
            pending.insert(request_id, sender);
            receiver
        };
        self.events.send(OutboundFrame::shell_approval(payload));
        receiver.await.ok()
    }

    /// `answer_shell_approval`: resolve the named question with the verdict.
    pub(crate) fn answer(&self, payload: &Value) -> DaemonResponse {
        let request_id = payload
            .get("requestId")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let Some(verdict) = payload
            .get("verdict")
            .and_then(|verdict| ShellVerdict::deserialize(verdict).ok())
        else {
            return response_failure(None, ANSWER_COMMAND, "Invalid shell approval verdict", None);
        };
        let slot = self
            .pending
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .remove(request_id);
        match slot.map(|slot| slot.send(verdict)) {
            Some(Ok(())) => response_success(None, ANSWER_COMMAND, None),
            Some(Err(_)) | None => response_failure(
                None,
                ANSWER_COMMAND,
                &format!("No pending shell approval: {request_id}"),
                None,
            ),
        }
    }

    /// Drop every open question once no client is attached (the detach
    /// paths call this with the core lock held, after the release).
    pub(crate) fn release_if_unattached(&self, core: &SessionCore) {
        if core.attached_client_ids.is_empty() {
            self.pending
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clear();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use tokio::sync::broadcast::{error::TryRecvError, Receiver};

    fn approvals(attached: &[&str]) -> ShellApprovals {
        let mut core = SessionCore::test_core("/tmp".to_string());
        core.attached_client_ids = attached.iter().map(ToString::to_string).collect();
        ShellApprovals::new(
            Arc::new(Mutex::new(core)),
            Arc::new(EventPump::new()),
            "sess-1".to_string(),
        )
    }

    fn request(request_id: &str) -> ShellApprovalRequest {
        ShellApprovalRequest {
            request_id: request_id.to_string(),
            step: 2,
            command: "rm -rf build".to_string(),
            effect: eukhe_types::shell::ShellEffect::Write,
        }
    }

    /// Wait for the question's frame (the ask task runs concurrently).
    async fn next_frame(receiver: &mut Receiver<Arc<OutboundFrame>>) -> Value {
        let frame = tokio::time::timeout(std::time::Duration::from_secs(5), receiver.recv())
            .await
            .expect("frame in time")
            .expect("frame");
        assert_eq!(frame.outbound_type, SHELL_APPROVAL_FRAME);
        serde_json::from_slice(&frame.payload).unwrap()
    }

    #[tokio::test]
    async fn an_answer_resolves_the_question_with_its_verdict() {
        let approvals = approvals(&["tui"]);
        let mut frames = approvals.events.subscribe();
        let asking = tokio::spawn({
            let approvals = approvals.clone();
            async move { approvals.ask(request("r1")).await }
        });
        assert_eq!(
            next_frame(&mut frames).await,
            json!({
                "type": "shell_approval",
                "activeSessionId": "sess-1",
                "request": {
                    "requestId": "r1",
                    "step": 2,
                    "command": "rm -rf build",
                    "effect": "write",
                },
            })
        );
        let response = approvals.answer(&json!({ "requestId": "r1", "verdict": "approve" }));
        assert_eq!(response, response_success(None, ANSWER_COMMAND, None));
        assert_eq!(asking.await.unwrap(), Some(ShellVerdict::Approve));
    }

    #[tokio::test]
    async fn no_attached_client_leaves_the_question_unanswered_without_a_frame() {
        let approvals = approvals(&[]);
        let mut frames = approvals.events.subscribe();
        assert_eq!(approvals.ask(request("r1")).await, None);
        assert!(matches!(frames.try_recv(), Err(TryRecvError::Empty)));
    }

    #[tokio::test]
    async fn the_last_detach_leaves_the_question_unanswered() {
        let approvals = approvals(&["tui"]);
        let mut frames = approvals.events.subscribe();
        let asking = tokio::spawn({
            let approvals = approvals.clone();
            async move { approvals.ask(request("r1")).await }
        });
        next_frame(&mut frames).await;
        {
            let mut core = approvals.core.lock().unwrap();
            core.attached_client_ids.clear();
            approvals.release_if_unattached(&core);
        }
        assert_eq!(asking.await.unwrap(), None);
    }

    #[tokio::test]
    async fn an_unknown_or_answered_id_is_an_error() {
        let approvals = approvals(&["tui"]);
        let mut frames = approvals.events.subscribe();
        let asking = tokio::spawn({
            let approvals = approvals.clone();
            async move { approvals.ask(request("r1")).await }
        });
        next_frame(&mut frames).await;
        let unknown = approvals.answer(&json!({ "requestId": "r9", "verdict": "deny" }));
        assert_eq!(
            unknown,
            response_failure(None, ANSWER_COMMAND, "No pending shell approval: r9", None)
        );
        let denied = approvals.answer(&json!({ "requestId": "r1", "verdict": "deny" }));
        assert_eq!(denied, response_success(None, ANSWER_COMMAND, None));
        assert_eq!(asking.await.unwrap(), Some(ShellVerdict::Deny));
        let again = approvals.answer(&json!({ "requestId": "r1", "verdict": "approve" }));
        assert_eq!(
            again,
            response_failure(None, ANSWER_COMMAND, "No pending shell approval: r1", None)
        );
    }
}
