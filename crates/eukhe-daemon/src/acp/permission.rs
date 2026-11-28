//! The editor's say on irreversible effects (spec I12): the ACP connection
//! attaches with the `editor_permission` capability, and each
//! `editor_permission` frame the daemon sends becomes one ACP
//! `session/request_permission` request to the editor. The editor's answer
//! goes back as `answer_editor_permission`: allow runs the effect; reject,
//! a cancelled turn, or any other answer refuses it. An editor that does
//! not serve the method (-32601) is answered `unsupported` and never asked
//! again in that ACP session; an editor that leaves unanswered gets no
//! answer at all (the daemon then runs the effect).

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use eukhe_types::daemon::DaemonCommand;
use eukhe_types::effects::{EditorPermissionRequest, EditorVerdict, EffectClass};
use serde::Deserialize as _;
use serde_json::{json, Map, Value};
use tokio::sync::{oneshot, Mutex};

use super::daemon::{DaemonAcpState, DaemonLink};
use super::jsonrpc;
use super::types::{AcpToolKind, AcpToolStatus};

/// The daemon client capability an ACP attach advertises.
pub(crate) const CAPABILITY: &str = "editor_permission";
/// The outbound daemon frame that asks.
pub(crate) const FRAME: &str = "editor_permission";
/// The ACP client method (a client baseline method in ACP v1).
const METHOD: &str = "session/request_permission";
const ALLOW_OPTION: &str = "allow";

/// The editor's `outcome` in a permission answer.
#[derive(serde::Deserialize)]
#[serde(tag = "outcome", rename_all = "lowercase")]
enum PermissionOutcome<'a> {
    Selected {
        #[serde(rename = "optionId", borrow)]
        option_id: &'a str,
    },
    #[serde(other)]
    Other,
}
const REJECT_OPTION: &str = "reject";

/// One `editor_permission` frame off the daemon link.
#[derive(Debug, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct PermissionFrame {
    pub(crate) active_session_id: String,
    pub(crate) request: EditorPermissionRequest,
}

/// The editor's answer to one request: its `result`, or its `error`.
type Reply = Result<Value, Value>;

/// The requests this agent sent the editor and has no answer for yet.
/// `None` once the editor left (stdin closed): nothing more is asked, and
/// every pending question ends unanswered.
pub(crate) struct EditorRequests {
    next_id: AtomicU64,
    pending: std::sync::Mutex<Option<HashMap<String, oneshot::Sender<Reply>>>>,
}

impl Default for EditorRequests {
    fn default() -> Self {
        EditorRequests {
            next_id: AtomicU64::new(0),
            pending: std::sync::Mutex::new(Some(HashMap::new())),
        }
    }
}

impl EditorRequests {
    /// Reserve the id of one request to the editor; `None` once it left.
    fn open(&self) -> Option<(String, oneshot::Receiver<Reply>)> {
        let id = format!(
            "eukhe-permission-{}",
            self.next_id.fetch_add(1, Ordering::SeqCst) + 1
        );
        let (tx, rx) = oneshot::channel();
        self.pending
            .lock()
            .unwrap()
            .as_mut()?
            .insert(id.clone(), tx);
        Some((id, rx))
    }

    fn forget(&self, id: &str) {
        if let Some(pending) = self.pending.lock().unwrap().as_mut() {
            pending.remove(id);
        }
    }

    /// The editor answered request `id`; an id this agent never sent (or
    /// already settled) is dropped.
    pub(crate) fn settle(&self, id: &Value, reply: Reply) {
        let Some(id) = id.as_str() else {
            return;
        };
        let sender = self
            .pending
            .lock()
            .unwrap()
            .as_mut()
            .and_then(|pending| pending.remove(id));
        if let Some(sender) = sender {
            let _ = sender.send(reply);
        }
    }

    /// The editor left: every pending question ends unanswered.
    pub(crate) fn close(&self) {
        self.pending.lock().unwrap().take();
    }
}

/// The editor's verdict from its answer. Only the allow option allows:
/// the reject option, a cancelled turn, an unknown outcome, and an error
/// refuse; method-not-found means the editor cannot be asked.
fn verdict(reply: &Reply) -> EditorVerdict {
    match reply {
        Ok(result) => match PermissionOutcome::deserialize(&result["outcome"]) {
            Ok(PermissionOutcome::Selected { option_id }) if option_id == ALLOW_OPTION => {
                EditorVerdict::Allow
            }
            Ok(PermissionOutcome::Selected { .. } | PermissionOutcome::Other) | Err(_) => {
                EditorVerdict::Reject
            }
        },
        Err(error) if error["code"].as_i64() == Some(jsonrpc::METHOD_NOT_FOUND) => {
            EditorVerdict::Unsupported
        }
        Err(_) => EditorVerdict::Reject,
    }
}

/// The ACP tool kind the editor shows for an effect of `classes`.
fn kind(classes: &[EffectClass]) -> AcpToolKind {
    let has = |class: EffectClass| classes.contains(&class);
    if has(EffectClass::Exec) {
        AcpToolKind::Execute
    } else if has(EffectClass::Net) {
        AcpToolKind::Fetch
    } else if has(EffectClass::Write) || has(EffectClass::Outside) || has(EffectClass::Protected) {
        AcpToolKind::Edit
    } else {
        AcpToolKind::Other
    }
}

/// The `session/request_permission` params (ACP v1): the tool call the
/// effect belongs to, pending until the editor answers, titled with the
/// command, and the allow / reject options. The tool call is the root
/// session's own (the editor is shown it as a `tool_call`); a subagent's
/// tool call, or an effect of no tool call, gets an id of its own.
pub(crate) fn request_params(acp_session_id: &str, request: &EditorPermissionRequest) -> Value {
    let tool_call_id = match request.tool_call_id.as_deref() {
        Some(id) if request.agent.is_none() => id.to_string(),
        _ => format!("eukhe-effect-{}", request.request_id),
    };
    let title = match request.agent.as_deref() {
        Some(agent) => format!("{} (subagent {agent})", request.command),
        None => request.command.clone(),
    };
    json!({
        "sessionId": acp_session_id,
        "toolCall": {
            "toolCallId": tool_call_id,
            "title": title,
            "kind": kind(&request.classes),
            "status": AcpToolStatus::Pending,
        },
        "options": [
            { "optionId": ALLOW_OPTION, "name": "Allow", "kind": "allow_once" },
            { "optionId": REJECT_OPTION, "name": "Reject", "kind": "reject_once" },
        ],
    })
}

/// Ask the editor and wait for its verdict; `None` when the editor left
/// before answering (nothing is answered then).
async fn ask_editor(
    requests: &EditorRequests,
    sink: &tokio::sync::mpsc::WeakUnboundedSender<Value>,
    params: &Value,
) -> Option<EditorVerdict> {
    let (id, answer) = requests.open()?;
    let sent = sink.upgrade().is_some_and(|sink| {
        sink.send(jsonrpc::request(&json!(id), METHOD, params))
            .is_ok()
    });
    if !sent {
        requests.forget(&id);
        return None;
    }
    answer.await.ok().map(|reply| verdict(&reply))
}

/// Who answers one `editor_permission` frame: the editor of the hosted ACP
/// session (its id and the request params), or no one.
pub(crate) struct Asked {
    pub(crate) acp_session_id: String,
    pub(crate) params: Value,
}

/// Answer one `editor_permission` frame on the daemon link. `asked` is
/// `None` when there is no editor to ask (no hosted ACP session, or its
/// editor does not serve the method): the answer is `unsupported` at
/// once and the effect runs. An editor that answers the method as unknown
/// is never asked again in that ACP session. An editor that leaves
/// unanswered gets no answer sent for it.
pub(crate) async fn answer(
    link: Arc<DaemonLink>,
    state: Arc<Mutex<DaemonAcpState>>,
    requests: Arc<EditorRequests>,
    sink: tokio::sync::mpsc::WeakUnboundedSender<Value>,
    frame: PermissionFrame,
    asked: Option<Asked>,
) {
    let verdict = match asked {
        None => EditorVerdict::Unsupported,
        Some(asked) => {
            let Some(verdict) = ask_editor(&requests, &sink, &asked.params).await else {
                return;
            };
            if verdict == EditorVerdict::Unsupported {
                if let Some(hosted) = state
                    .lock()
                    .await
                    .session
                    .as_mut()
                    .filter(|hosted| hosted.acp_session_id == asked.acp_session_id)
                {
                    hosted.editor_unsupported = true;
                }
            }
            verdict
        }
    };
    // A question the daemon already dropped (its step was cancelled)
    // refuses the answer; nothing waits on it any more.
    let _ = link
        .request(DaemonCommand::AnswerEditorPermission {
            id: None,
            active_session_id: frame.active_session_id,
            request_id: frame.request.request_id,
            verdict,
            rest: Map::default(),
        })
        .await;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(agent: Option<&str>, classes: Vec<EffectClass>) -> EditorPermissionRequest {
        EditorPermissionRequest {
            request_id: "r1".to_string(),
            tool_call_id: Some("call-1".to_string()),
            command: "git push origin main".to_string(),
            classes,
            agent: agent.map(str::to_string),
        }
    }

    #[test]
    fn the_request_is_the_acp_v1_permission_shape() {
        let params = request_params(
            "s1",
            &request(None, vec![EffectClass::Exec, EffectClass::Net]),
        );
        assert_eq!(
            params,
            json!({
                "sessionId": "s1",
                "toolCall": {
                    "toolCallId": "call-1",
                    "title": "git push origin main",
                    "kind": "execute",
                    "status": "pending",
                },
                "options": [
                    { "optionId": "allow", "name": "Allow", "kind": "allow_once" },
                    { "optionId": "reject", "name": "Reject", "kind": "reject_once" },
                ],
            })
        );
        // A subagent's tool call never reached the editor: the request
        // carries an id of its own, and so does an effect of no tool call.
        let child = request_params("s1", &request(Some("fix-tests"), vec![EffectClass::Net]));
        assert_eq!(child["toolCall"]["toolCallId"], "eukhe-effect-r1");
        assert_eq!(
            child["toolCall"]["title"],
            "git push origin main (subagent fix-tests)"
        );
        assert_eq!(child["toolCall"]["kind"], "fetch");
        let untooled = EditorPermissionRequest {
            tool_call_id: None,
            ..request(None, vec![EffectClass::Unknown])
        };
        assert_eq!(
            request_params("s1", &untooled)["toolCall"]["toolCallId"],
            "eukhe-effect-r1"
        );
    }

    #[test]
    fn the_kind_follows_the_classes() {
        assert_eq!(
            kind(&[EffectClass::Write, EffectClass::Outside]),
            AcpToolKind::Edit
        );
        assert_eq!(
            kind(&[EffectClass::Write, EffectClass::Protected]),
            AcpToolKind::Edit
        );
        assert_eq!(
            kind(&[EffectClass::Read, EffectClass::Secret]),
            AcpToolKind::Other
        );
        assert_eq!(kind(&[EffectClass::Unknown]), AcpToolKind::Other);
    }

    #[test]
    fn only_the_allow_option_allows() {
        let selected =
            |option: &str| Ok(json!({ "outcome": { "outcome": "selected", "optionId": option } }));
        assert_eq!(verdict(&selected("allow")), EditorVerdict::Allow);
        assert_eq!(verdict(&selected("reject")), EditorVerdict::Reject);
        assert_eq!(verdict(&selected("other")), EditorVerdict::Reject);
        assert_eq!(
            verdict(&Ok(json!({ "outcome": { "outcome": "cancelled" } }))),
            EditorVerdict::Reject
        );
        assert_eq!(verdict(&Ok(json!({}))), EditorVerdict::Reject);
        assert_eq!(
            verdict(&Err(
                json!({ "code": -32601, "message": "Method not found" })
            )),
            EditorVerdict::Unsupported
        );
        assert_eq!(
            verdict(&Err(json!({ "code": -32603, "message": "Internal error" }))),
            EditorVerdict::Reject
        );
    }

    #[tokio::test]
    async fn the_editor_leaving_answers_nothing() {
        let requests = std::sync::Arc::new(EditorRequests::default());
        let (sink, mut frames) = tokio::sync::mpsc::unbounded_channel();
        let weak = sink.downgrade();
        let asking = {
            let requests = std::sync::Arc::clone(&requests);
            tokio::spawn(async move { ask_editor(&requests, &weak, &json!({})).await })
        };
        let sent = frames.recv().await.expect("the request reached the editor");
        assert_eq!(sent["method"], "session/request_permission");
        requests.close();
        assert_eq!(asking.await.unwrap(), None);
        // Nothing is asked once the editor left.
        assert_eq!(
            ask_editor(&requests, &sink.downgrade(), &json!({})).await,
            None
        );
        drop(sink);
    }

    #[tokio::test]
    async fn the_answer_settles_its_request() {
        let requests = std::sync::Arc::new(EditorRequests::default());
        let (sink, mut frames) = tokio::sync::mpsc::unbounded_channel();
        let weak = sink.downgrade();
        let asking = {
            let requests = std::sync::Arc::clone(&requests);
            tokio::spawn(async move { ask_editor(&requests, &weak, &json!({})).await })
        };
        let sent = frames.recv().await.expect("the request reached the editor");
        requests.settle(&json!("unknown"), Ok(json!({})));
        requests.settle(
            &sent["id"],
            Ok(json!({ "outcome": { "outcome": "selected", "optionId": "allow" } })),
        );
        assert_eq!(asking.await.unwrap(), Some(EditorVerdict::Allow));
    }
}
