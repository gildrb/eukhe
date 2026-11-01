//! The `agent_message.send` controller (moved with its concern): the
//! parent and children roster + message delivery through the supervisor,
//! the direct peer transport with the supervisor-routed fallback, and the
//! wire receipt mapping.
use super::family::{family_of, row_active_id, row_target};
use super::{
    json, row_str, AgentFamilyMember, AgentFamilyRelationship, AgentMessageController,
    AgentMessageDeliveryStatus, AgentMessageReceipt, AgentMessageSendInput, Arc, FamilyIdentity,
    SupervisorLink, Value,
};

/// `agent_message.send` controller for daemon workers. The family roster
/// and message delivery both go through the supervisor; a send first tries
/// the direct worker-to-worker peer transport (thin-supervisor stage 3) and
/// falls back to the supervisor-routed `send_message` (the TS worker's
/// `sendRemoteAgentSessionMessage` path). Neither path is retried: daemon
/// commands are not idempotent.
/// Exposed for the agent-family e2e verifier (`tests/agent_family_e2e.rs)`:
/// the same controller construction the worker engine wires.
pub struct LinkAgentMessageController {
    pub(super) link: Arc<SupervisorLink>,
    pub(super) active_session_id: String,
    pub(super) worker_token: String,
    /// This worker's own session summary, pushed by the worker at create
    /// (and rename); the sender identity block for direct deliveries.
    pub(super) own_summary: Arc<std::sync::Mutex<Option<Value>>>,
    /// This session's resident RLM children (the same registry
    /// `rlm.list_subagents` reads); `None` for standalone workers.
    pub(super) children: Option<Arc<crate::rlm_children::SupervisorChildSessions>>,
}

impl LinkAgentMessageController {
    pub fn new(
        link: Arc<SupervisorLink>,
        active_session_id: String,
        worker_token: String,
        own_summary: Arc<std::sync::Mutex<Option<Value>>>,
        children: Option<Arc<crate::rlm_children::SupervisorChildSessions>>,
    ) -> Self {
        LinkAgentMessageController {
            link,
            active_session_id,
            worker_token,
            own_summary,
            children,
        }
    }
}

/// Budget for the peer-ticket request on the supervisor link (the TS
/// `get_direct_worker_transport` window).
const PEER_TICKET_TIMEOUT_MS: u64 = 5_000;

/// The supervisor roster read behind `family()`: every roster row (live
/// sessions, seeded passivated children, and the caller's own row), so
/// idle and passivated parents and children are reached too.
async fn roster_summaries(
    link: &Arc<crate::supervisor_link::SupervisorLink>,
    worker_token: &str,
) -> anyhow::Result<Vec<Value>> {
    // Surface an unavailable supervisor instead of silently claiming the
    // caller has no family.
    let data = link
        .request_success(
            json!({ "type": "list_agent_peers", "workerToken": worker_token, "scope": "roster" }),
            std::time::Duration::from_secs(5),
        )
        .await?;
    Ok(data
        .get("peers")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default())
}

/// Whether the registry child `child` owns roster `row`. The join is
/// durable-keyed so a child worker replacement (a new live id, the same
/// rlm child id / persisted session id) still matches its record.
fn registry_owns(child: &crate::rlm_children::RlmChildIdentity, row: &Value) -> bool {
    row_active_id(row)
        .or_else(|| row_str(row, "id"))
        .is_some_and(|id| id == child.active_session_id)
        || row_str(row, "rlmChildId").is_some_and(|id| id == child.rlm_child_id)
        || row_str(row, "sessionId").is_some_and(|id| child.session_id.as_deref() == Some(id))
}

/// Push `alias` onto `aliases` unless it is empty, the member id, or
/// already listed.
fn push_alias(aliases: &mut Vec<String>, id: &str, alias: &str) {
    if !alias.is_empty() && alias != id && !aliases.iter().any(|known| known == alias) {
        aliases.push(alias.to_string());
    }
}

/// The member order: the parent, then the children (each by name).
fn relationship_rank(relationship: AgentFamilyRelationship) -> u8 {
    match relationship {
        AgentFamilyRelationship::Parent => 0,
        AgentFamilyRelationship::Child => 1,
    }
}

impl AgentMessageController for LinkAgentMessageController {
    async fn family(&self) -> anyhow::Result<Vec<AgentFamilyMember>> {
        let sessions = roster_summaries(&self.link, &self.worker_token).await?;
        // The calling session's durable family identity (its own ids and
        // its recorded parent edge); never derived from names.
        let identity = self.family_identity();
        // This session's children, keyed for the roster join: the registry
        // plus the durable children roster - the same sources
        // `rlm.list_subagents` reads, so the family view and the RLM roster
        // can never disagree on which children exist.
        let mut children = match &self.children {
            Some(children) => children.family_child_identities().await?,
            None => Vec::new(),
        };
        let family = family_of(&sessions, &identity, |row| {
            children.iter().any(|child| registry_owns(child, row))
        });
        let mut members = Vec::with_capacity(family.members.len() + children.len());
        for family_row in &family.members {
            let session = &sessions[family_row.index];
            let Some(id) = row_target(session) else {
                continue;
            };
            if id == self.active_session_id {
                continue;
            }
            let mut name = row_str(session, "sessionName").map(str::to_string);
            let mut aliases = Vec::new();
            // A roster row owned by this session's children registry keeps
            // the registry's RLM child id and persisted session id as
            // aliases (every identifier `rlm.list_subagents` exposes); the
            // member keys on the row's CURRENT address, never the replaced
            // spawn-time live id (which stays an alias).
            let registry_child = children
                .iter()
                .position(|child| registry_owns(child, session))
                .map(|position| children.swap_remove(position));
            if let Some(child) = &registry_child {
                push_alias(&mut aliases, &id, &child.rlm_child_id);
                if let Some(session_id) = &child.session_id {
                    push_alias(&mut aliases, &id, session_id);
                }
                push_alias(&mut aliases, &id, &child.active_session_id);
                if name.is_none() && !child.session_name.is_empty() {
                    name = Some(child.session_name.clone());
                }
            }
            for key in ["sessionId", "rlmChildId", "agentId"] {
                if let Some(alias) = row_str(session, key) {
                    push_alias(&mut aliases, &id, alias);
                }
            }
            members.push(AgentFamilyMember {
                relationship: family_row.relationship,
                id,
                name,
                aliases,
                path: family_row.path.clone(),
            });
        }
        // Children the roster does not list (a passivated or
        // mid-registration child worker) are addressed by their DURABLE
        // id, like TS family entries (`id: agent.sessionId`): the
        // supervisor's send_message wake resolves it through the spawn
        // ledger and relaunches a passivated child. The spawn-time live id
        // stays an alias selector.
        for child in children {
            let id = crate::rlm_children::durable_child_selector(
                child.session_id.as_deref(),
                &child.rlm_child_id,
            );
            let mut aliases = Vec::new();
            push_alias(&mut aliases, &id, &child.rlm_child_id);
            if let Some(session_id) = &child.session_id {
                push_alias(&mut aliases, &id, session_id);
            }
            push_alias(&mut aliases, &id, &child.active_session_id);
            let name = (!child.session_name.is_empty()).then(|| child.session_name.clone());
            let path = identity
                .session_name
                .as_deref()
                .zip(name.as_deref())
                .map(|(parent, name)| format!("{parent}/{name}"));
            members.push(AgentFamilyMember {
                relationship: AgentFamilyRelationship::Child,
                id,
                name,
                aliases,
                path,
            });
        }
        members.sort_by(|left, right| {
            relationship_rank(left.relationship)
                .cmp(&relationship_rank(right.relationship))
                .then_with(|| left.member_name().cmp(right.member_name()))
        });
        Ok(members)
    }

    async fn send_agent_message(
        &self,
        input: AgentMessageSendInput,
    ) -> anyhow::Result<AgentMessageReceipt> {
        if input.target == self.active_session_id {
            anyhow::bail!("Agent messaging cannot target the sending session");
        }
        // Direct peer delivery first (stage 3): a single-use `worker`
        // grant on the target's own socket, bypassing the supervisor's
        // route plane. Falls back to the supervisor-routed send (the TS
        // remote path) whenever the direct link cannot be established -
        // but never after the delivery command was sent: the grant burns
        // on first use, so an in-flight delivery's outcome is final.
        let receipt = match self.deliver_direct(&input).await {
            DirectDelivery::Delivered(receipt) => receipt,
            DirectDelivery::Unavailable => self.deliver_via_supervisor(input.clone()).await?,
            DirectDelivery::Failed(error) => return Err(anyhow::anyhow!(error)),
        };
        Ok(receipt)
    }
}

/// The outcome of the direct-delivery attempt.
enum DirectDelivery {
    /// The target answered with a receipt.
    Delivered(AgentMessageReceipt),
    /// No direct link could be established; the supervisor route may take
    /// over.
    Unavailable,
    /// The attempt reached the target and is final: the grant burned, so
    /// the error surfaces instead of a fallback.
    Failed(String),
}

impl LinkAgentMessageController {
    /// Try the direct worker-to-worker path. `Unavailable` only when the
    /// delivery command never reached the target (no ticket, connect
    /// failure, or failed grant burn - the message was not delivered);
    /// once the command is sent the outcome is final either way.
    async fn deliver_direct(&self, input: &AgentMessageSendInput) -> DirectDelivery {
        let ticket = match self
            .link
            .request_success(
                json!({
                    "type": "get_worker_peer_transport",
                    "workerToken": self.worker_token,
                    "targetActiveSessionId": input.target,
                }),
                std::time::Duration::from_millis(PEER_TICKET_TIMEOUT_MS),
            )
            .await
        {
            Ok(data) => {
                match serde_json::from_value::<eukhe_types::daemon::DaemonPeerTransportTicket>(data)
                {
                    Ok(ticket) => ticket,
                    Err(_) => return DirectDelivery::Unavailable,
                }
            }
            // A ticket refusal (worker without direct transport, target
            // unavailable) is the fallback trigger, not an error.
            Err(_) => return DirectDelivery::Unavailable,
        };
        match crate::peer_client::deliver_message_over_peer_transport(
            &ticket,
            &input.message,
            &self.sender_block(),
            None,
        )
        .await
        {
            crate::peer_client::PeerDeliveryOutcome::NotEstablished => DirectDelivery::Unavailable,
            crate::peer_client::PeerDeliveryOutcome::Lost => DirectDelivery::Failed(
                "Peer delivery to the target session was sent but not acknowledged".to_string(),
            ),
            crate::peer_client::PeerDeliveryOutcome::Answered(response) => {
                let response = *response;
                if !response.success {
                    return DirectDelivery::Failed(
                        response
                            .error
                            .unwrap_or_else(|| "Agent message was not accepted".to_string()),
                    );
                }
                match response
                    .data
                    .as_ref()
                    .and_then(|data| receipt_from_wire(data, input.clone()))
                {
                    Some(receipt) => DirectDelivery::Delivered(receipt),
                    None => DirectDelivery::Failed(
                        "Target session returned an invalid agent-message receipt".to_string(),
                    ),
                }
            }
        }
    }

    /// The supervisor-routed fallback (TS `sendRemoteAgentSessionMessage`).
    async fn deliver_via_supervisor(
        &self,
        input: AgentMessageSendInput,
    ) -> anyhow::Result<AgentMessageReceipt> {
        let data = self
            .link
            .request_success(
                json!({
                    "type": "send_message",
                    "targetActiveSessionId": input.target,
                    "message": input.message,
                    "fromActiveSessionId": self.active_session_id,
                    "agentOrigin": true,
                }),
                std::time::Duration::from_secs(30),
            )
            .await?;
        receipt_from_wire(&data, input)
            .ok_or_else(|| anyhow::anyhow!("Supervisor returned an invalid agent-message receipt"))
    }

    /// This session's durable family identity from its own pushed summary:
    /// the ids its family references it by, and its recorded parent edge.
    /// `None` fields degrade; the active session id always comes from the
    /// worker's own link config (the summary may lag a rename).
    fn family_identity(&self) -> FamilyIdentity {
        let summary = self
            .own_summary
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        FamilyIdentity::from_summary(summary.as_ref(), &self.active_session_id)
    }

    /// The TS `createAgentSessionMessageSender` shape for agent-origin
    /// sends: the sending session's endpoint fields plus the `agent`
    /// client identity (the TS daemon attributes kernel sends this way
    /// when no client id is in play).
    fn sender_block(&self) -> Value {
        let summary = self
            .own_summary
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        let mut sender = json!({
            "activeSessionId": self.active_session_id,
            "runtimeKind": "top-level",
            "clientId": "agent",
        });
        if let Some(summary) = summary {
            if let Some(session_id) = summary.get("sessionId").filter(|value| !value.is_null()) {
                sender["sessionId"] = session_id.clone();
            }
            if let Some(name) = summary
                .get("sessionName")
                .and_then(Value::as_str)
                .filter(|name| !name.is_empty())
            {
                sender["sessionName"] = json!(name);
            }
            if let Some(kind) = summary
                .get("runtimeKind")
                .and_then(Value::as_str)
                .filter(|kind| !kind.is_empty())
            {
                sender["runtimeKind"] = json!(kind);
            }
            // The sender's durable parent edge rides the block so the
            // receiving session can label the delivery by its TRUE
            // relationship (a child only when this sender's recorded
            // parent is the recipient), never by runtime kind alone.
            for (field, summary_field) in [
                ("parentActiveSessionId", "parentActiveSessionId"),
                ("parentSessionId", "parentSessionId"),
                ("parentSessionPath", "parentSessionPath"),
            ] {
                if let Some(value) = summary
                    .get(summary_field)
                    .and_then(Value::as_str)
                    .filter(|value| !value.is_empty())
                {
                    sender[field] = json!(value);
                }
            }
        }
        sender
    }
}

/// Map a delivery receipt payload (the `worker_deliver_message` response
/// data, both delivery paths) onto the kernel receipt shape. `None` marks
/// a payload that does not carry the TS receipt fields.
fn receipt_from_wire(data: &Value, input: AgentMessageSendInput) -> Option<AgentMessageReceipt> {
    let target = data.get("target")?;
    let id = data.get("id")?.as_str()?.to_string();
    let delivery_status = if data.get("deliveryStatus").and_then(Value::as_str) == Some("delivered")
    {
        AgentMessageDeliveryStatus::Delivered
    } else {
        AgentMessageDeliveryStatus::Queued
    };
    let delivery_mode = match data.get("deliveryMode").and_then(Value::as_str) {
        Some("follow_up") => "follow_up",
        _ => "steer",
    };
    Some(AgentMessageReceipt {
        id,
        target: target
            .get("activeSessionId")
            .and_then(Value::as_str)
            .filter(|value| !value.is_empty())
            .unwrap_or(&input.target)
            .to_string(),
        target_session_id: target
            .get("sessionId")
            .and_then(Value::as_str)
            .map(str::to_string),
        target_session_name: target
            .get("sessionName")
            .and_then(Value::as_str)
            .map(str::to_string),
        target_runtime_kind: target
            .get("runtimeKind")
            .and_then(Value::as_str)
            .map(str::to_string),
        message: input.message,
        delivery_status,
        delivery_mode: Some(delivery_mode),
        receiver_role: input.receiver_role,
        delivered_at: data
            .get("deliveredAt")
            .and_then(Value::as_str)
            .map(str::to_string),
        queued_at: data
            .get("queuedAt")
            .and_then(Value::as_str)
            .map(str::to_string),
    })
}
