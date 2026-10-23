//! The worker's pending shell approvals: the `bash` tool asks the attached
//! clients whether one step may run (a `shell_approval` frame), and the
//! first `answer_shell_approval` for its request id wins. A session whose
//! attached clients are all the phone gateway (`clientKind` `gateway`),
//! which shows no question, asks no one: it runs the step at once, or
//! refuses it at once when the step writes a protected path or reads or
//! writes a secret (the gateway rule). A session with no attached client,
//! or whose clients all detached before an answer came (the last detach
//! drops every pending question), hands the question to its parent
//! session (`relay_shell_approval` over the supervisor), which does the
//! same: the question reaches the nearest session up the chain with a
//! client, and its frame names the subagent that asks. When no session up
//! to the root answers, the step is unanswered, which the tool treats as a
//! denial (`laws/approvals.bend`, G5).

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::daemon::DaemonCommand;
use eukhe_types::shell::{ShellAnswer, ShellApprovalRequest, ShellEffect, ShellVerdict};
use futures::future::BoxFuture;
use serde::Deserialize;
use serde_json::{json, Map, Value};
use tokio::sync::oneshot;

use crate::protocol::{response_failure, response_success, DaemonOutbound, DaemonResponse};
use crate::worker::{EventPump, OutboundFrame, SessionCore};

/// The private-frame `outboundType` of one shell approval question.
pub(crate) const SHELL_APPROVAL_FRAME: &str = "shell_approval";

const ANSWER_COMMAND: &str = "answer_shell_approval";

const RELAY_COMMAND: &str = "relay_shell_approval";

/// Request id -> the waiting step's answer slot.
type Pending = HashMap<String, oneshot::Sender<ShellVerdict>>;

/// Who answers a question of the session now.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Attendance {
    /// An interactive client is attached (the TUI, the dashboard): the
    /// session asks its clients.
    Interactive,
    /// Clients are attached, and all are the phone gateway: the gateway
    /// rule answers at once.
    GatewayOnly,
    /// No client is attached: the question goes to the parent session.
    Nobody,
}

impl Attendance {
    fn of(core: &SessionCore) -> Self {
        if core.attached_client_ids.is_empty() {
            Self::Nobody
        } else if core
            .attached_client_ids
            .iter()
            .all(|id| core.gateway_client_ids.contains(id))
        {
            Self::GatewayOnly
        } else {
            Self::Interactive
        }
    }
}

/// Sends one `relay_shell_approval` command and answers its response: the
/// worker's supervisor link (the supervisor routes the command to the
/// parent session's worker).
pub(crate) type Relay =
    Arc<dyn Fn(Value) -> BoxFuture<'static, anyhow::Result<DaemonResponse>> + Send + Sync>;

/// The session's open shell approval questions.
#[derive(Clone)]
pub(crate) struct ShellApprovals {
    core: Arc<Mutex<SessionCore>>,
    events: Arc<EventPump>,
    active_session_id: String,
    pending: Arc<Mutex<Pending>>,
    relay: Relay,
}

impl ShellApprovals {
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
            pending: Arc::default(),
            relay,
        }
    }

    /// Ask about one step of this session (the session's `shell_approval`
    /// sink): its attached clients, the gateway rule, else its parent
    /// session.
    #[tracing::instrument(skip_all, fields(request_id = %request.request_id, step = request.step))]
    pub(crate) async fn ask(&self, request: ShellApprovalRequest) -> ShellAnswer {
        self.route(request, None).await
    }

    /// `relay_shell_approval`: a subagent's question, handed up by a child
    /// session; answered like [`Self::ask`], with `agent` named on the
    /// frame. The data is `{"answer": <ShellAnswer>}`.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn relay(&self, payload: &Value) -> DaemonResponse {
        let request = payload
            .get("request")
            .and_then(|request| ShellApprovalRequest::deserialize(request).ok());
        let agent = payload.get("agent").and_then(Value::as_str);
        let (Some(request), Some(agent)) = (request, agent) else {
            return response_failure(None, RELAY_COMMAND, "Invalid shell approval relay", None);
        };
        let answer = self.route(request, Some(agent.to_owned())).await;
        response_success(None, RELAY_COMMAND, Some(json!({ "answer": answer })))
    }

    /// Ask this session's attached clients (a frame naming `agent`, the
    /// subagent that asks, when the question came up from a child). When
    /// its clients are all the phone gateway, answer by the gateway rule
    /// at once. When none is attached, hand the question to the parent
    /// session. A question whose interactive clients all detach before an
    /// answer is routed again. [`ShellAnswer::Unanswered`] when the frame
    /// does not serialize (logged), when the session has no parent, or
    /// when the relay fails (logged).
    async fn route(&self, request: ShellApprovalRequest, agent: Option<String>) -> ShellAnswer {
        loop {
            let receiver = {
                // The attendance check and the insert hold the core lock,
                // the lock the detach paths hold while they drop the
                // pending answers: a question is answered by the gateway
                // rule or goes up the chain at once, or waits here until
                // an answer, or the detach of the last interactive client,
                // which routes it again.
                let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
                match Attendance::of(&core) {
                    Attendance::Interactive => {
                        let (sender, receiver) = oneshot::channel();
                        let mut pending =
                            self.pending.lock().unwrap_or_else(PoisonError::into_inner);
                        // A step whose wait was cancelled leaves a closed
                        // slot behind.
                        pending.retain(|_, slot| !slot.is_closed());
                        pending.insert(request.request_id.clone(), sender);
                        receiver
                    }
                    // The gateway shows no question, so no one waits: a
                    // step runs, unless it writes a protected path or
                    // reads or writes a secret.
                    Attendance::GatewayOnly => {
                        let guarded = request.effects.contains(ShellEffect::Protected)
                            || request.effects.contains(ShellEffect::Secret);
                        return if guarded {
                            tracing::info!(effects = %request.effects.names(), "the gateway rule refused a step");
                            ShellAnswer::GatewayRefused
                        } else {
                            ShellAnswer::Approve
                        };
                    }
                    Attendance::Nobody => break,
                }
            };
            // The question may be routed again: the frame keeps its own
            // copy.
            let outbound = DaemonOutbound::ShellApproval {
                active_session_id: self.active_session_id.clone(),
                request: request.clone(),
                agent: agent.clone(),
                rest: Map::default(),
            };
            match serde_json::to_vec(&outbound) {
                Ok(payload) => self.events.send(OutboundFrame::shell_approval(payload)),
                Err(error) => {
                    tracing::error!(%error, "the shell approval frame does not serialize");
                    return ShellAnswer::Unanswered;
                }
            }
            match receiver.await {
                Ok(ShellVerdict::Approve) => return ShellAnswer::Approve,
                Ok(ShellVerdict::Deny) => return ShellAnswer::Deny,
                // The last interactive client detached: route it again.
                Err(_) => {}
            }
        }
        let command = {
            let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
            // A root session has no one above it: no answer.
            let Some(parent) = core
                .parent_session_id
                .clone()
                .or_else(|| core.parent_active_session_id.clone())
            else {
                return ShellAnswer::Unanswered;
            };
            DaemonCommand::RelayShellApproval {
                id: None,
                active_session_id: parent,
                request,
                // The subagent that asks: the first session of the chain.
                agent: agent.unwrap_or_else(|| {
                    core.session_name
                        .clone()
                        .or_else(|| core.rlm_child_id.clone())
                        .unwrap_or_else(|| self.active_session_id.clone())
                }),
                rest: Map::default(),
            }
        };
        let command = match serde_json::to_value(&command) {
            Ok(command) => command,
            Err(error) => {
                tracing::error!(%error, "the shell approval relay does not serialize");
                return ShellAnswer::Unanswered;
            }
        };
        match (self.relay)(command).await {
            Ok(DaemonResponse {
                success: true,
                data,
                ..
            }) => match data
                .as_ref()
                .and_then(|data| data.get("answer"))
                .map(ShellAnswer::deserialize)
            {
                Some(Ok(answer)) => answer,
                Some(Err(error)) => {
                    tracing::warn!(%error, "the parent session's shell approval answer is invalid");
                    ShellAnswer::Unanswered
                }
                None => {
                    tracing::warn!("the parent session's shell approval relay has no answer");
                    ShellAnswer::Unanswered
                }
            },
            Ok(DaemonResponse { error, .. }) => {
                tracing::warn!(
                    ?error,
                    "the parent session refused the shell approval relay"
                );
                ShellAnswer::Unanswered
            }
            Err(error) => {
                tracing::warn!(error = %format!("{error:#}"), "the shell approval relay failed");
                ShellAnswer::Unanswered
            }
        }
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

    /// Drop every open question once no interactive client is attached
    /// (the detach paths call this with the core lock held, after the
    /// release): each is routed again, so the gateway rule answers it, or
    /// it goes up to the parent session, or is left unanswered at a root.
    pub(crate) fn release_if_no_interactive_client(&self, core: &SessionCore) {
        match Attendance::of(core) {
            Attendance::Interactive => {}
            Attendance::GatewayOnly | Attendance::Nobody => self
                .pending
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clear(),
        }
    }
}

#[cfg(test)]
mod bridge;

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use tokio::sync::broadcast::{error::TryRecvError, Receiver};

    /// A root session's approvals: no parent, so the relay never runs.
    fn approvals(attached: &[&str]) -> ShellApprovals {
        let mut core = SessionCore::test_core("/tmp".to_string());
        core.attached_client_ids = attached.iter().map(ToString::to_string).collect();
        ShellApprovals::new(
            Arc::new(Mutex::new(core)),
            Arc::new(EventPump::new()),
            "sess-1".to_string(),
            Arc::new(|command| panic!("a root session relayed {command}")),
        )
    }

    fn request(request_id: &str) -> ShellApprovalRequest {
        ShellApprovalRequest {
            request_id: request_id.to_string(),
            step: 2,
            command: "rm -rf build".to_string(),
            effects: eukhe_types::shell::ShellEffects::of(&[
                eukhe_types::shell::ShellEffect::Write,
                eukhe_types::shell::ShellEffect::Outside,
            ]),
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
                    "effects": ["write", "outside"],
                },
            })
        );
        let response = approvals.answer(&json!({ "requestId": "r1", "verdict": "approve" }));
        assert_eq!(response, response_success(None, ANSWER_COMMAND, None));
        assert_eq!(asking.await.unwrap(), ShellAnswer::Approve);
    }

    #[tokio::test]
    async fn no_attached_client_leaves_the_question_unanswered_without_a_frame() {
        let approvals = approvals(&[]);
        let mut frames = approvals.events.subscribe();
        assert_eq!(approvals.ask(request("r1")).await, ShellAnswer::Unanswered);
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
            approvals.release_if_no_interactive_client(&core);
        }
        assert_eq!(asking.await.unwrap(), ShellAnswer::Unanswered);
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
        assert_eq!(asking.await.unwrap(), ShellAnswer::Deny);
        let again = approvals.answer(&json!({ "requestId": "r1", "verdict": "approve" }));
        assert_eq!(
            again,
            response_failure(None, ANSWER_COMMAND, "No pending shell approval: r1", None)
        );
    }
}
