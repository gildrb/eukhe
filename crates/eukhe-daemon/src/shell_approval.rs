//! The worker's pending shell approvals: the `bash` tool asks the attached
//! clients whether one step may run (a `shell_approval` frame), and the
//! first `answer_shell_approval` for its request id wins. A session whose
//! attached clients are all the phone gateway (`clientKind` `gateway`),
//! which shows no question, asks no one: it runs the step at once, or
//! refuses it at once when the step writes a protected path or reads or
//! writes a secret (the gateway rule). A session with no attached client,
//! or whose clients all detached before an answer came, hands the question
//! to its parent session (`relay_shell_approval` over the supervisor),
//! which does the same: the question reaches the nearest session up the
//! chain with a client, and its frame names the subagent that asks. When
//! no session up to the root answers, the step is unanswered, which the
//! tool treats as a denial (`laws/approvals/`, G5). However a question's
//! wait on the session's clients ends (an answer, the last detach, the
//! step's cancellation), a `shell_approval_settled` frame tells every
//! client to drop it; an answer to a question no longer pending is refused
//! with [`DaemonErrorInfo::ShellApprovalGone`].
//!
//! This module decides none of that. The session's desk, a stepper of the
//! compiled core ([`approvals::Desk`]), keeps the open questions and
//! decides what each event means; this module is its event loop: it sends
//! each event as it arrives (a question, an answer, a detach, a step that
//! stops waiting, the parent's answer to a relay), in arrival order, and
//! does the acts the desk answers: frames to the clients, the relay to the
//! parent, and the wake of the waiting step, keyed by the desk's key.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_bend::rules::approvals::{self, Act, Here, Key, Parent};
use eukhe_bend::rules::shell::Said;
use eukhe_types::daemon::{DaemonCommand, DaemonErrorInfo};
use eukhe_types::shell::{ShellAnswer, ShellApprovalRequest, ShellVerdict};
use futures::future::BoxFuture;
use serde::Deserialize;
use serde_json::{json, Map, Value};
use tokio::sync::mpsc;

use crate::protocol::{response_failure, response_success, DaemonOutbound, DaemonResponse};
use crate::worker::{EventPump, OutboundFrame, SessionCore};

/// The private-frame `outboundType` of one shell approval question.
pub(crate) const SHELL_APPROVAL_FRAME: &str = "shell_approval";

/// The private-frame `outboundType` that drops one question from the
/// clients.
pub(crate) const SHELL_APPROVAL_SETTLED_FRAME: &str = "shell_approval_settled";

const ANSWER_COMMAND: &str = "answer_shell_approval";

const RELAY_COMMAND: &str = "relay_shell_approval";

/// Who answers a question of the session now, as attached: no client,
/// only the phone gateway, or an interactive client (the TUI, the
/// dashboard).
fn here(core: &SessionCore) -> Here {
    if core.attached_client_ids.is_empty() {
        Here::Nobody
    } else if core
        .attached_client_ids
        .iter()
        .all(|id| core.gateway_client_ids.contains(id))
    {
        Here::GatewayOnly
    } else {
        Here::Clients
    }
}

/// The session `core` is a child of, if any.
fn parent_of(core: &SessionCore) -> Option<String> {
    core.parent_session_id
        .clone()
        .or_else(|| core.parent_active_session_id.clone())
}

fn parent(core: &SessionCore) -> Parent {
    match parent_of(core) {
        Some(_) => Parent::Above,
        None => Parent::Root,
    }
}

/// Sends one `relay_shell_approval` command and answers its response: the
/// worker's supervisor link (the supervisor routes the command to the
/// parent session's worker).
pub(crate) type Relay =
    Arc<dyn Fn(Value) -> BoxFuture<'static, anyhow::Result<DaemonResponse>> + Send + Sync>;

/// What the desk tells a waiting step.
enum Turn {
    /// Hand the question to the parent session.
    Relay,
    /// The step fares this answer.
    Wake(ShellAnswer),
}

/// One open question: what its frames carry, and its step's waiter.
struct Open {
    request: ShellApprovalRequest,
    /// The subagent that asks, when the question came up from a child.
    agent: Option<String>,
    waiter: mpsc::UnboundedSender<Turn>,
}

/// The session's desk and the open questions by the desk's key.
struct Office {
    desk: approvals::Desk,
    open: HashMap<Key, Open>,
}

/// The session's open shell approval questions.
#[derive(Clone)]
pub(crate) struct ShellApprovals {
    core: Arc<Mutex<SessionCore>>,
    events: Arc<EventPump>,
    active_session_id: String,
    office: Arc<Mutex<Office>>,
    relay: Relay,
}

/// The wait of one step. Dropped before its wake (the step's
/// cancellation), it tells the desk the step stopped waiting.
struct Waiting<'a> {
    approvals: &'a ShellApprovals,
    key: Option<Key>,
}

impl Drop for Waiting<'_> {
    fn drop(&mut self) {
        if let Some(key) = self.key.take() {
            let mut office = self.approvals.lock_office();
            let acts = office.desk.cancel(key);
            self.approvals.perform(&mut office, acts);
            office.open.remove(&key);
        }
    }
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
            office: Arc::new(Mutex::new(Office {
                desk: approvals::Desk::open(),
                open: HashMap::new(),
            })),
            relay,
        }
    }

    fn lock_office(&self) -> std::sync::MutexGuard<'_, Office> {
        self.office.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Ask about one step of this session (the session's `shell_approval`
    /// sink).
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

    /// The question reaches the session's desk; wait for its wake, relaying
    /// it to the parent session when the desk says so.
    /// [`ShellAnswer::Unanswered`] when its request id is longer than the
    /// core's wire carries (logged).
    async fn route(&self, request: ShellApprovalRequest, agent: Option<String>) -> ShellAnswer {
        let (waiter, mut turns) = mpsc::unbounded_channel();
        let key = {
            // Who answers the session is read under the core lock, the lock
            // the detach paths hold while they tell the desk: the desk sees
            // the question and the detaches in the order they happened.
            let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
            let mut office = self.lock_office();
            let asked = office.desk.ask(
                &request.request_id,
                request.effects,
                here(&core),
                parent(&core),
            );
            let (key, acts) = match asked {
                Ok(asked) => asked,
                Err(error) => {
                    tracing::error!(%error, "the shell approval question does not reach the desk");
                    return ShellAnswer::Unanswered;
                }
            };
            office.open.insert(
                key,
                Open {
                    request: request.clone(),
                    agent: agent.clone(),
                    waiter,
                },
            );
            self.perform(&mut office, acts);
            key
        };
        let mut waiting = Waiting {
            approvals: self,
            key: Some(key),
        };
        loop {
            match turns.recv().await {
                Some(Turn::Wake(answer)) => {
                    waiting.key = None;
                    if answer == ShellAnswer::GatewayRefused {
                        tracing::info!(effects = %request.effects.names(), "the gateway rule refused a step");
                    }
                    return answer;
                }
                Some(Turn::Relay) => {
                    let answer = self.relay_up(&request, agent.as_deref()).await;
                    let mut office = self.lock_office();
                    let acts = office.desk.back(key, answer);
                    self.perform(&mut office, acts);
                }
                // The waiter goes only with the question's wake, which
                // comes first.
                None => {
                    waiting.key = None;
                    tracing::error!("a shell approval question lost its waiter");
                    return ShellAnswer::Unanswered;
                }
            }
        }
    }

    /// Hand the question to the parent session and answer its answer:
    /// [`ShellAnswer::Unanswered`] when the relay fails (logged).
    async fn relay_up(&self, request: &ShellApprovalRequest, agent: Option<&str>) -> ShellAnswer {
        let (parent, agent) = {
            let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
            // The subagent that asks: the first session of the chain.
            let agent = agent.map_or_else(
                || {
                    core.session_name
                        .clone()
                        .or_else(|| core.rlm_child_id.clone())
                        .unwrap_or_else(|| self.active_session_id.clone())
                },
                ToOwned::to_owned,
            );
            (parent_of(&core), agent)
        };
        let Some(parent) = parent else {
            tracing::error!("the desk relayed the question of a session with no parent");
            return ShellAnswer::Unanswered;
        };
        let command = DaemonCommand::RelayShellApproval {
            id: None,
            active_session_id: parent,
            request: request.clone(),
            agent,
            rest: Map::default(),
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

    /// `answer_shell_approval`: the verdict of a client on the question its
    /// frame named.
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
        let said = match verdict {
            ShellVerdict::Approve => Said::Yes,
            ShellVerdict::Deny => Said::No,
        };
        let mut office = self.lock_office();
        let took = match office.desk.answer(request_id, said) {
            Ok(acts) => self.perform(&mut office, acts),
            Err(error) => {
                tracing::warn!(%error, "the shell approval answer does not reach the desk");
                false
            }
        };
        if took {
            response_success(None, ANSWER_COMMAND, None)
        } else {
            response_failure(
                None,
                ANSWER_COMMAND,
                &format!("No pending shell approval: {request_id}"),
                Some(DaemonErrorInfo::ShellApprovalGone),
            )
        }
    }

    /// A client detached (the detach paths call this with the core lock
    /// held, after the release): the desk decides what becomes of the
    /// questions its clients had.
    pub(crate) fn detached(&self, core: &SessionCore) {
        let mut office = self.lock_office();
        let acts = office.desk.detach(here(core), parent(core));
        self.perform(&mut office, acts);
    }

    /// Do the desk's acts, in order; whether one took a client's answer.
    fn perform(&self, office: &mut Office, acts: Vec<Act>) -> bool {
        let mut took = false;
        for act in acts {
            match act {
                Act::Show(key) => {
                    if let Some(open) = office.open.get(&key) {
                        self.send(
                            &DaemonOutbound::ShellApproval {
                                active_session_id: self.active_session_id.clone(),
                                request: open.request.clone(),
                                agent: open.agent.clone(),
                                rest: Map::default(),
                            },
                            OutboundFrame::shell_approval,
                        );
                    }
                }
                Act::Settle(key) => {
                    if let Some(open) = office.open.get(&key) {
                        self.send(
                            &DaemonOutbound::ShellApprovalSettled {
                                active_session_id: self.active_session_id.clone(),
                                request_id: open.request.request_id.clone(),
                                rest: Map::default(),
                            },
                            OutboundFrame::shell_approval_settled,
                        );
                    }
                }
                Act::Relay(key) => {
                    if let Some(open) = office.open.get(&key) {
                        // A step that stopped waiting is gone: its cancel
                        // reaches the desk when its wait drops.
                        let _ = open.waiter.send(Turn::Relay);
                    }
                }
                Act::Wake(key, answer) => {
                    if let Some(open) = office.open.remove(&key) {
                        let _ = open.waiter.send(Turn::Wake(answer));
                    }
                }
                Act::Took => took = true,
                Act::Gone => took = false,
            }
        }
        took
    }

    /// Broadcast one frame to the session's clients.
    fn send(&self, outbound: &DaemonOutbound, frame: fn(Vec<u8>) -> OutboundFrame) {
        match serde_json::to_vec(outbound) {
            Ok(payload) => self.events.send(frame(payload)),
            Err(error) => {
                tracing::error!(%error, "a shell approval frame does not serialize");
            }
        }
    }
}

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
            approvals.detached(&core);
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
            response_failure(
                None,
                ANSWER_COMMAND,
                "No pending shell approval: r9",
                Some(DaemonErrorInfo::ShellApprovalGone)
            )
        );
        let denied = approvals.answer(&json!({ "requestId": "r1", "verdict": "deny" }));
        assert_eq!(denied, response_success(None, ANSWER_COMMAND, None));
        assert_eq!(asking.await.unwrap(), ShellAnswer::Deny);
        let again = approvals.answer(&json!({ "requestId": "r1", "verdict": "approve" }));
        assert_eq!(
            again,
            response_failure(
                None,
                ANSWER_COMMAND,
                "No pending shell approval: r1",
                Some(DaemonErrorInfo::ShellApprovalGone)
            )
        );
    }

    /// The frames after the question: `shell_approval_settled` ones.
    async fn settled_frame(receiver: &mut Receiver<Arc<OutboundFrame>>) -> Value {
        let frame = tokio::time::timeout(std::time::Duration::from_secs(5), receiver.recv())
            .await
            .expect("frame in time")
            .expect("frame");
        assert_eq!(frame.outbound_type, SHELL_APPROVAL_SETTLED_FRAME);
        serde_json::from_slice(&frame.payload).unwrap()
    }

    /// Every end of a question's wait tells the clients to drop it: the
    /// answer of one client (the others still show it), and a step whose
    /// wait was cancelled (the run aborted), whose question no one may
    /// answer any more. Before the fix the clients kept the cancelled
    /// question and each answer to it failed with an error.
    #[tokio::test]
    async fn every_end_of_a_wait_settles_the_question_for_the_clients() {
        let approvals = approvals(&["tui", "dashboard"]);
        let mut frames = approvals.events.subscribe();
        let settled = |request_id: &str| {
            json!({
                "type": "shell_approval_settled",
                "activeSessionId": "sess-1",
                "requestId": request_id,
            })
        };
        let asking = tokio::spawn({
            let approvals = approvals.clone();
            async move { approvals.ask(request("r1")).await }
        });
        next_frame(&mut frames).await;
        approvals.answer(&json!({ "requestId": "r1", "verdict": "approve" }));
        assert_eq!(asking.await.unwrap(), ShellAnswer::Approve);
        assert_eq!(settled_frame(&mut frames).await, settled("r1"));

        let cancelled = tokio::spawn({
            let approvals = approvals.clone();
            async move { approvals.ask(request("119:0")).await }
        });
        next_frame(&mut frames).await;
        cancelled.abort();
        assert!(cancelled.await.unwrap_err().is_cancelled());
        assert_eq!(settled_frame(&mut frames).await, settled("119:0"));
        assert_eq!(
            approvals.answer(&json!({ "requestId": "119:0", "verdict": "approve" })),
            response_failure(
                None,
                ANSWER_COMMAND,
                "No pending shell approval: 119:0",
                Some(DaemonErrorInfo::ShellApprovalGone)
            )
        );
        assert!(approvals.lock_office().open.is_empty());
    }

    /// A chain of real sessions, the asker first: each hands a question up
    /// through its parent's real `relay_shell_approval` handler (in place of
    /// the supervisor link, which only carries the command). Each entry:
    /// the session's attached client ids and its gateway client ids.
    fn chain(sessions: &[(&[&str], &[&str])]) -> Vec<ShellApprovals> {
        let mut built: Vec<ShellApprovals> = Vec::new();
        for (at, (attached, gateway)) in sessions.iter().enumerate().rev() {
            let mut core = SessionCore::test_core("/tmp".to_string());
            core.session_name = Some(if at == 0 {
                "scout".to_string()
            } else {
                format!("s{at}")
            });
            core.attached_client_ids = attached.iter().map(ToString::to_string).collect();
            core.gateway_client_ids = gateway.iter().map(ToString::to_string).collect();
            let relay: Relay = match built.last().cloned() {
                Some(parent) => {
                    let parent_id = format!("session-{}", at + 1);
                    core.parent_session_id = Some(parent_id.clone());
                    Arc::new(move |command: Value| {
                        let (parent, parent_id) = (parent.clone(), parent_id.clone());
                        Box::pin(async move {
                            let to = command.get("activeSessionId").and_then(Value::as_str);
                            anyhow::ensure!(to == Some(parent_id.as_str()), "relayed to {to:?}");
                            Ok(parent.relay(&command).await)
                        })
                    })
                }
                None => Arc::new(|command| panic!("a root session relayed {command}")),
            };
            built.push(ShellApprovals::new(
                Arc::new(Mutex::new(core)),
                Arc::new(EventPump::new()),
                format!("live-{at}"),
                relay,
            ));
        }
        built.reverse();
        built
    }

    /// Detach every interactive client of `approvals`' session.
    fn interactive_clients_leave(approvals: &ShellApprovals) {
        let mut guard = approvals.core.lock().unwrap();
        let core = &mut *guard;
        core.attached_client_ids
            .retain(|id| core.gateway_client_ids.contains(id));
        approvals.detached(core);
    }

    /// A subagent with no client asks: the question goes up to the root,
    /// whose frame names the subagent; the root's denial is the verdict.
    #[tokio::test(flavor = "multi_thread")]
    async fn a_subagents_question_reaches_the_root_and_its_answer_comes_back() {
        let sessions = chain(&[(&[], &[]), (&[], &[]), (&["tui"], &[])]);
        let mut root_frames = sessions[2].events.subscribe();
        let asking = tokio::spawn({
            let asker = sessions[0].clone();
            async move { asker.ask(request("call-1:0")).await }
        });
        let frame = next_frame(&mut root_frames).await;
        assert_eq!(frame["agent"], "scout");
        assert_eq!(frame["activeSessionId"], "live-2");
        let denied = sessions[2].answer(&json!({ "requestId": "call-1:0", "verdict": "deny" }));
        assert!(denied.success, "{denied:?}");
        assert_eq!(asking.await.unwrap(), ShellAnswer::Deny);
        assert!(sessions
            .iter()
            .all(|session| session.lock_office().open.is_empty()));
    }

    /// The subagent's own client sees the question and leaves: the question
    /// is settled there and goes up; the parent's client approves.
    #[tokio::test(flavor = "multi_thread")]
    async fn a_question_its_clients_leave_goes_up_the_chain() {
        let sessions = chain(&[(&["tui-0"], &[]), (&["tui-1"], &[])]);
        let mut child_frames = sessions[0].events.subscribe();
        let mut parent_frames = sessions[1].events.subscribe();
        let asking = tokio::spawn({
            let asker = sessions[0].clone();
            async move { asker.ask(request("call-1:0")).await }
        });
        assert_eq!(next_frame(&mut child_frames).await["agent"], Value::Null);
        interactive_clients_leave(&sessions[0]);
        assert_eq!(
            settled_frame(&mut child_frames).await["requestId"],
            "call-1:0"
        );
        assert_eq!(next_frame(&mut parent_frames).await["agent"], "scout");
        // The child's clients are gone: an answer there finds nothing.
        assert!(
            !sessions[0]
                .answer(&json!({ "requestId": "call-1:0", "verdict": "approve" }))
                .success
        );
        let approved =
            sessions[1].answer(&json!({ "requestId": "call-1:0", "verdict": "approve" }));
        assert!(approved.success, "{approved:?}");
        assert_eq!(asking.await.unwrap(), ShellAnswer::Approve);
    }

    /// The interactive client leaves while the phone gateway stays: the
    /// gateway rule answers there (a secret read is refused), and nothing
    /// goes up the chain (the parent would panic on a relay).
    #[tokio::test(flavor = "multi_thread")]
    async fn a_question_left_to_the_gateway_is_ruled_there() {
        let sessions = chain(&[(&["tui", "phone"], &["phone"])]);
        let mut frames = sessions[0].events.subscribe();
        let asking = tokio::spawn({
            let asker = sessions[0].clone();
            async move {
                asker
                    .ask(ShellApprovalRequest {
                        effects: eukhe_types::shell::ShellEffects::of(&[
                            eukhe_types::shell::ShellEffect::Read,
                            eukhe_types::shell::ShellEffect::Secret,
                        ]),
                        ..request("call-1:0")
                    })
                    .await
            }
        });
        next_frame(&mut frames).await;
        interactive_clients_leave(&sessions[0]);
        assert_eq!(asking.await.unwrap(), ShellAnswer::GatewayRefused);
    }

    /// Two questions with the same request id (two subagents' first steps)
    /// on one session: an answer goes to the oldest, the next to the other,
    /// a third finds none.
    #[tokio::test(flavor = "multi_thread")]
    async fn each_answer_wakes_one_question_once() {
        let approvals = approvals(&["tui"]);
        let mut frames = approvals.events.subscribe();
        let first = tokio::spawn({
            let approvals = approvals.clone();
            async move { approvals.ask(request("call-1:0")).await }
        });
        next_frame(&mut frames).await;
        let second = tokio::spawn({
            let approvals = approvals.clone();
            async move { approvals.ask(request("call-1:0")).await }
        });
        next_frame(&mut frames).await;
        let answer = |verdict: &str| {
            approvals
                .answer(&json!({ "requestId": "call-1:0", "verdict": verdict }))
                .success
        };
        assert_eq!(
            (answer("deny"), answer("approve"), answer("approve")),
            (true, true, false)
        );
        assert_eq!(
            (first.await.unwrap(), second.await.unwrap()),
            (ShellAnswer::Deny, ShellAnswer::Approve)
        );
    }

    /// A subagent's step cancelled while its question waits on the root's
    /// clients: the relay is dropped, and the root's clients are told the
    /// question is settled.
    #[tokio::test(flavor = "multi_thread")]
    async fn a_cancelled_subagent_step_settles_its_question_up_the_chain() {
        let sessions = chain(&[(&[], &[]), (&["tui"], &[])]);
        let mut root_frames = sessions[1].events.subscribe();
        let asking = tokio::spawn({
            let asker = sessions[0].clone();
            async move { asker.ask(request("call-1:0")).await }
        });
        next_frame(&mut root_frames).await;
        asking.abort();
        assert!(asking.await.unwrap_err().is_cancelled());
        assert_eq!(
            settled_frame(&mut root_frames).await["requestId"],
            "call-1:0"
        );
        assert!(sessions
            .iter()
            .all(|session| session.lock_office().open.is_empty()));
    }
}
