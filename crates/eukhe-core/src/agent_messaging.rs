//! Agent messaging and observation host requests: validation helpers, message
//! ids and prompts, controller traits, and kernel host-handler registration.
//! Port of core/agent-messages.ts (validation/prompt half) and
//! core/agent-observe.ts.

use std::future::Future;

use eukhe_types::input_origin::{Kin, Report};
use serde_json::{json, Value};

use crate::kernel::shared::{host_handler, HostRequestHandlers};

pub const AGENT_MESSAGE_CUSTOM_TYPE: &str = "agent_message";
/// TS `AGENT_MESSAGE_RECEIVED_PREVIEW_LABEL`: the queue-strip preview label
/// for a delivered agent message (`queuedAgentMessagePreview` renders
/// "<label>: <details.message>").
pub const AGENT_MESSAGE_RECEIVED_PREVIEW_LABEL: &str = "Agent message received";
pub const AGENT_MESSAGE_SOURCE: &str = "agent_message";
pub const AGENT_MESSAGE_ID_PREFIX: &str = "agentmsg_";
pub const DEFAULT_AGENT_MESSAGE_MAX_CHARS: usize = 16_384;
pub const DEFAULT_AGENT_MESSAGE_MAX_PENDING_PER_SESSION: usize = 20;
/// The per-sender token bucket capacity (TS
/// `DEFAULT_AGENT_MESSAGE_RATE_LIMIT_CAPACITY`): three deliveries burst
/// before the refill paces them.
pub const DEFAULT_AGENT_MESSAGE_RATE_LIMIT_CAPACITY: usize = 3;
/// One rate-limit token per sender per this window (TS
/// `DEFAULT_AGENT_MESSAGE_RATE_LIMIT_REFILL_MS`).
pub const DEFAULT_AGENT_MESSAGE_RATE_LIMIT_REFILL_MS: u64 = 1_000;
/// The row an agent's final answer to a user's `@name` message leaves in
/// the session the user sent it from: shown to the user, logged to chat
/// memory as `[name] answer`, model context for the next turn, never a
/// turn of its own.
pub const AGENT_REPLY_CUSTOM_TYPE: &str = "agent_reply";
/// The answering agent's own bookkeeping row (display-only, hidden): its
/// run owes the user's session the final answer (`details.id`,
/// `details.replyTo`).
pub const AGENT_REPLY_OWED_CUSTOM_TYPE: &str = "agent_reply_owed";

/// The two relationships an agent messages along: its parent and its own
/// children. Agents never reach siblings, relatives, or other trees.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgentFamilyRelationship {
    Parent,
    Child,
}

impl std::fmt::Display for AgentFamilyRelationship {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.as_str())
    }
}

impl AgentFamilyRelationship {
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            AgentFamilyRelationship::Parent => "parent",
            AgentFamilyRelationship::Child => "child",
        }
    }

    #[must_use]
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "parent" => Some(AgentFamilyRelationship::Parent),
            "child" => Some(AgentFamilyRelationship::Child),
            _ => None,
        }
    }
}

/// Delivery status for a sent agent message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgentMessageDeliveryStatus {
    Delivered,
    Queued,
}

impl AgentMessageDeliveryStatus {
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            AgentMessageDeliveryStatus::Delivered => "delivered",
            AgentMessageDeliveryStatus::Queued => "queued",
        }
    }
}

/// `agent_message.send` input.
#[derive(Debug, Clone)]
pub struct AgentMessageSendInput {
    pub target: String,
    pub message: String,
    pub receiver_role: Option<AgentFamilyRelationship>,
}

/// The receipt returned after sending an agent message.
#[derive(Debug, Clone)]
pub struct AgentMessageReceipt {
    pub id: String,
    /// The target's active session id (TS `target.activeSessionId`).
    pub target: String,
    /// The target endpoint's session id (TS `target.sessionId`).
    pub target_session_id: Option<String>,
    pub target_session_name: Option<String>,
    pub target_runtime_kind: Option<String>,
    pub message: String,
    pub delivery_status: AgentMessageDeliveryStatus,
    pub delivery_mode: Option<&'static str>,
    pub receiver_role: Option<AgentFamilyRelationship>,
    pub delivered_at: Option<String>,
    pub queued_at: Option<String>,
}

/// One addressable member (TS `AgentFamilyMember`): the caller's parent or
/// one of its own children, keyed by a routable target selector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AgentFamilyMember {
    pub relationship: AgentFamilyRelationship,
    /// The target selector the controller can deliver to (session id for
    /// local family members, the active session id for peers served by
    /// another worker).
    pub id: String,
    pub name: Option<String>,
    /// Extra selector forms that resolve to this same member (empty for
    /// the TS shape). The supervisor-backed controller lists a child's
    /// RLM child id and persisted session id here so every identifier the
    /// roster exposes addresses the child, while broadcast sends stay
    /// one-per-member.
    pub aliases: Vec<String>,
    /// The `parent/child` path form (the parent's name, `/`, this
    /// member's name); `None` for a member without a named parent.
    pub path: Option<String>,
}

impl AgentFamilyMember {
    /// TS `agentFamilyMemberName`: the name, else the id.
    #[must_use]
    pub fn member_name(&self) -> &str {
        self.name.as_deref().unwrap_or(&self.id)
    }

    /// Whether `selector` addresses this member by name, id, alias, or
    /// `parent/child` path.
    fn matches_selector(&self, selector: &str) -> bool {
        self.member_name() == selector
            || self.id == selector
            || self.aliases.iter().any(|alias| alias == selector)
            || self.path.as_deref() == Some(selector)
    }
}

/// The controller the daemon supplies for `agent_message.*` requests.
pub trait AgentMessageController: Send + Sync {
    /// The addressable members (TS `controller.family()`): this session's
    /// parent and its own children, never the session itself.
    fn family(&self) -> impl Future<Output = anyhow::Result<Vec<AgentFamilyMember>>> + Send;
    fn send_agent_message(
        &self,
        input: AgentMessageSendInput,
    ) -> impl Future<Output = anyhow::Result<AgentMessageReceipt>> + Send;
}

/// Message payload for the rendered `[agent-message from ...]` prompt.
#[derive(Debug, Clone)]
pub struct AgentMessagePromptPayload {
    pub message: String,
    pub sender_name: String,
    /// Who the sender is to the recipient.
    pub from: Kin,
}

#[must_use]
pub fn create_agent_session_message_id() -> String {
    format!("{AGENT_MESSAGE_ID_PREFIX}{}", uuid::Uuid::new_v4())
}

/// Normalize and validate an outgoing message body.
///
/// # Errors
///
/// Returns an error when the message is empty after trimming or longer
/// than the default message limit.
pub fn normalize_agent_session_message(message: &str) -> anyhow::Result<String> {
    normalize_agent_session_message_limited(message, DEFAULT_AGENT_MESSAGE_MAX_CHARS)
}

/// Normalize and validate an outgoing message body with an explicit
/// character limit.
///
/// # Errors
///
/// Returns an error when the message is empty after trimming or longer
/// than `max_chars`.
pub fn normalize_agent_session_message_limited(
    message: &str,
    max_chars: usize,
) -> anyhow::Result<String> {
    let trimmed = message.trim();
    if trimmed.is_empty() {
        anyhow::bail!("Agent session message cannot be empty");
    }
    if trimmed.chars().count() > max_chars {
        anyhow::bail!(
            "Agent session message is too long: {} chars exceeds {max_chars}",
            trimmed.chars().count()
        );
    }
    Ok(trimmed.to_string())
}

/// Reject broadcast targets: only direct messaging is supported.
/// Normalize a direct-messaging target and reject broadcast wildcards.
///
/// # Errors
///
/// Returns an error when the target is empty after trimming or names the
/// broadcast wildcard.
pub fn assert_direct_agent_message_target(target: &str) -> anyhow::Result<String> {
    let normalized = target.trim();
    if normalized.is_empty() {
        anyhow::bail!("Agent message target cannot be empty");
    }
    if normalized == "*"
        || normalized.eq_ignore_ascii_case("all")
        || normalized.eq_ignore_ascii_case("broadcast")
    {
        anyhow::bail!("Broadcast agent messaging is not supported");
    }
    Ok(normalized.to_string())
}

/// Guard the target session's pending-work capacity.
///
/// # Errors
///
/// Returns an error when the target's unfinished action count has reached
/// the pending-work limit.
pub fn assert_agent_message_queue_capacity(
    unfinished_action_count: usize,
    max_pending: usize,
) -> anyhow::Result<()> {
    if unfinished_action_count >= max_pending {
        anyhow::bail!(
            "Target session has too many pending messages: {unfinished_action_count} unfinished, limit is {max_pending}"
        );
    }
    Ok(())
}

/// Names interpolated into a `[<kind> ...]` header line must not carry the
/// characters that delimit the header itself (brackets, newlines, commas,
/// or the relationship separator ":"): runs of those collapse into one
/// space, then the value trims (TS `sanitizeMessageHeaderValue`).
pub(crate) fn sanitize_message_header_value(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    let mut pending_space = false;
    for char in value.chars() {
        let delimiter = char.is_whitespace() || matches!(char, ',' | ':' | '[' | ']');
        if delimiter {
            pending_space = true;
        } else {
            if pending_space && !out.is_empty() {
                out.push(' ');
            }
            pending_space = false;
            out.push(char);
        }
    }
    out
}

/// The report a receiving context gets; its prompt is
/// `report.render(&payload.message)`.
#[must_use]
pub fn agent_session_message_report(payload: &AgentMessagePromptPayload) -> Report {
    let sender = sanitize_message_header_value(&payload.sender_name);
    let sender = if sender.is_empty() {
        "unknown".to_string()
    } else {
        sender
    };
    Report::AgentMessage {
        from: payload.from,
        name: sender,
    }
}

/// The model text of an [`AGENT_REPLY_CUSTOM_TYPE`] row:
/// `[agent-reply from <name>]`, a blank line, the answer.
#[must_use]
pub fn create_agent_reply_prompt(from: &str, answer: &str) -> String {
    let from = sanitize_message_header_value(from);
    let from = if from.is_empty() {
        "unknown".to_string()
    } else {
        from
    };
    format!("[agent-reply from {from}]\n\n{answer}")
}

/// The receiving side's custom-row inputs (TS
/// `AgentSessionMessagePayload` at `createAgentSessionMessage` time).
#[derive(Debug, Clone)]
pub struct AgentSessionMessageRowPayload<'a> {
    pub id: &'a str,
    /// The rendered prompt (TS stores `createAgentSessionMessagePrompt`'s
    /// output as the row `content`; the model context reads it).
    pub prompt: &'a str,
    /// The raw delivered body (TS `details.message`).
    pub message: &'a str,
    /// The sender endpoint (TS `details.from`).
    pub from: &'a Value,
    /// Who the sender is to the recipient (`details.fromRelationship`
    /// names a parent or a child; a user's message carries none).
    pub from_kin: Kin,
    /// The receiver endpoint (TS `details.target`); `None` omits the key
    /// (TS `spawnMessage` carries none).
    pub target: Option<&'a Value>,
    /// Unix timestamp in milliseconds (TS `Date.now()`).
    pub timestamp: u64,
}

/// TS `createAgentSessionMessage`: the `role: "custom"` agent-message row
/// the receiving session's transcript holds. `content` is the rendered
/// prompt, so the turn's model context (the loop-boundary user-role
/// conversion of the custom row) matches the plain-prompt delivery, while
/// the details carry the identity the `agent_message` UI reads.
#[must_use]
pub fn create_agent_session_message_row(payload: &AgentSessionMessageRowPayload<'_>) -> Value {
    let mut details = serde_json::Map::new();
    details.insert("id".to_string(), json!(payload.id));
    details.insert("message".to_string(), json!(payload.message));
    details.insert("from".to_string(), payload.from.clone());
    match payload.from_kin {
        Kin::Parent => {
            details.insert("fromRelationship".to_string(), json!("parent"));
        }
        Kin::Child => {
            details.insert("fromRelationship".to_string(), json!("child"));
        }
        Kin::User => {}
    }
    if let Some(target) = payload.target {
        details.insert("target".to_string(), target.clone());
    }
    json!({
        "role": "custom",
        "customType": AGENT_MESSAGE_CUSTOM_TYPE,
        "content": payload.prompt,
        "display": true,
        "details": Value::Object(details),
        "timestamp": payload.timestamp,
    })
}

/// The TS `AgentSessionMessageEndpoint` the receipt carries as `target`.
fn receipt_target_value(receipt: &AgentMessageReceipt) -> Value {
    let mut target = json!({
        "activeSessionId": receipt.target,
        "sessionId": receipt.target_session_id.clone().unwrap_or_default(),
    });
    if let Some(name) = receipt
        .target_session_name
        .as_deref()
        .filter(|name| !name.is_empty())
    {
        target["sessionName"] = json!(name);
    }
    if let Some(kind) = receipt
        .target_runtime_kind
        .as_deref()
        .filter(|kind| !kind.is_empty())
    {
        target["runtimeKind"] = json!(kind);
    }
    target
}

fn receipt_value(receipt: &AgentMessageReceipt) -> Value {
    json!({
        "id": receipt.id,
        "source": AGENT_MESSAGE_SOURCE,
        "target": receipt_target_value(receipt),
        "message": receipt.message,
        "deliveryStatus": receipt.delivery_status.as_str(),
        "deliveredAt": receipt.delivered_at,
        "queuedAt": receipt.queued_at,
        "deliveryMode": receipt.delivery_mode,
        "receiverRole": receipt.receiver_role.map(|role| role.as_str()),
    })
}

/// The receiver an addressed `agent_message.send` names: the parent, or
/// one of the caller's own children.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AgentMessageReceiver {
    /// The parent (`receiver_role="parent"`, no name).
    Parent,
    /// One own child by selector (`receiver_name`, with or without
    /// `receiver_role="child"`): its name, one of its ids, or its
    /// `parent/child` path.
    Child { selector: String },
}

/// Parse the addressed-send fields of an `agent_message.send` payload.
///
/// # Errors
///
/// Returns the contract error for an unknown `receiver_role`, a parent
/// send carrying a name, or a child send without a `receiver_name`.
pub fn parse_receiver(data: &Value) -> anyhow::Result<AgentMessageReceiver> {
    let role = match data.get("receiver_role").filter(|value| !value.is_null()) {
        None => None,
        Some(value) => match value.as_str().and_then(AgentFamilyRelationship::parse) {
            Some(role) => Some(role),
            None => anyhow::bail!(
                "agent_message.send receiver_role must be \"parent\" or \"child\"; agents message only their parent and their own children"
            ),
        },
    };
    let receiver_name = data.get("receiver_name").filter(|value| !value.is_null());
    if role == Some(AgentFamilyRelationship::Parent) {
        if receiver_name.is_some() {
            anyhow::bail!("agent_message.send receiver_name must be omitted for parent messages");
        }
        return Ok(AgentMessageReceiver::Parent);
    }
    match receiver_name
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|name| !name.is_empty())
    {
        Some(selector) => Ok(AgentMessageReceiver::Child {
            selector: selector.to_string(),
        }),
        None => anyhow::bail!(
            "agent_message.send needs receiver_role=\"parent\" or receiver_name (one of your children: its name, id, or parent/child path)"
        ),
    }
}

/// Resolve `receiver` against the caller's parent and children: exactly
/// one member resolves; none or several is an error. Spawn names are
/// unique per parent only by convention, so a name two children share is
/// ambiguous and the error lists the id that addresses each.
///
/// # Errors
///
/// Returns an error when no member or more than one member matches.
pub fn resolve_receiver(
    family: Vec<AgentFamilyMember>,
    receiver: &AgentMessageReceiver,
) -> anyhow::Result<AgentFamilyMember> {
    let mut matches: Vec<AgentFamilyMember> = family
        .into_iter()
        .filter(|member| match receiver {
            AgentMessageReceiver::Parent => member.relationship == AgentFamilyRelationship::Parent,
            AgentMessageReceiver::Child { selector } => {
                member.relationship == AgentFamilyRelationship::Child
                    && member.matches_selector(selector)
            }
        })
        .collect();
    if matches.len() == 1 {
        return Ok(matches.remove(0));
    }
    let none = matches.is_empty();
    Err(match receiver {
        AgentMessageReceiver::Parent => anyhow::anyhow!("This agent has no parent to message"),
        AgentMessageReceiver::Child { selector } if none => anyhow::anyhow!(
            "No child of this agent matches \"{selector}\"; agents message only their parent and their own children"
        ),
        AgentMessageReceiver::Child { selector } => {
            let candidates: Vec<String> = matches.iter().map(|member| member.id.clone()).collect();
            anyhow::anyhow!(
                "Child selector \"{selector}\" is ambiguous; address one by id: {}",
                candidates.join(", ")
            )
        }
    })
}

/// Register `agent_message.*` handlers onto a handler map. The `send`
/// contract matches the kernel skill: `receiver_role="parent"` addresses
/// the parent, `receiver_name` (with or without `receiver_role="child"`)
/// one of the caller's own children (name, id, or `parent/child` path),
/// and `target: "all"` sends to every own child. Positional targets other
/// than `"all"` are rejected exactly like the TS handler.
pub fn register_agent_message_host_handlers<C: AgentMessageController + 'static>(
    controller: std::sync::Arc<C>,
    handlers: &mut HostRequestHandlers,
) {
    handlers.register(
        "agent_message.list_agents",
        host_handler(|_payload| {
            Box::pin(async {
                Err(anyhow::anyhow!(
                    "agent_message.list_agents was removed; the family roster now lives in agent_observe.list_agents(). Restart the Python kernel to load the current skills, then call await agent_observe.list_agents()."
                ))
            })
        }),
    );
    handlers.register(
        "agent_message.send",
        host_handler(move |payload| {
            let controller = controller.clone();
            Box::pin(async move {
                let data = payload.data;
                let Some(message) = data.get("message").and_then(Value::as_str) else {
                    return Err(anyhow::anyhow!(
                        "agent_message.send message must be a string"
                    ));
                };
                // TS normalizes inside every send (broadcast included), so
                // normalizing up front is behaviorally identical.
                let message = normalize_agent_session_message(message)?;
                // Broadcast form (`target: "all"`): one send per own
                // child, all-settled into a receipts array.
                if let Some(target) = data.get("target").and_then(Value::as_str) {
                    if target != "all" {
                        return Err(anyhow::anyhow!(
                            "positional agent_message.send targets are not supported; use receiver_role and receiver_name"
                        ));
                    }
                    if data.get("receiver_role").is_some() || data.get("receiver_name").is_some() {
                        return Err(anyhow::anyhow!(
                            "agent_message.send broadcast cannot be combined with receiver_role/receiver_name"
                        ));
                    }
                    let children: Vec<AgentFamilyMember> = controller
                        .family()
                        .await?
                        .into_iter()
                        .filter(|member| member.relationship == AgentFamilyRelationship::Child)
                        .collect();
                    let mut receipts = Vec::with_capacity(children.len());
                    for member in children {
                        let result = controller
                            .send_agent_message(AgentMessageSendInput {
                                target: member.id.clone(),
                                message: message.clone(),
                                receiver_role: Some(member.relationship),
                            })
                            .await;
                        receipts.push(match result {
                            Ok(receipt) => receipt_value(&receipt),
                            Err(error) => json!({
                                "target": member.id,
                                "error": error.to_string(),
                            }),
                        });
                    }
                    return Ok(json!({ "receipts": receipts }));
                }
                // Addressed form: resolve the receiver among the parent
                // and the own children, then send once.
                let receiver = parse_receiver(&data)?;
                let family = controller.family().await?;
                let member = resolve_receiver(family, &receiver)?;
                let receipt = controller
                    .send_agent_message(AgentMessageSendInput {
                        target: member.id.clone(),
                        message: message.clone(),
                        receiver_role: Some(member.relationship),
                    })
                    .await?;
                Ok(receipt_value(&receipt))
            })
        }),
    );
}

// ---------------------------------------------------------------------------
// Agent observation
// ---------------------------------------------------------------------------

/// The family lifecycle status every observation row carries (TS #2493
/// `AgentFamilyStatus`, the roster's `AgentRosterStatus`): `running` while
// The observe half (TS agent-observe.ts) lives in the child module
// (agent_messaging::observe); the pub use re-exports keep every external
// agent_messaging:: path stable (the eukhe-daemon importers).
mod observe;
pub use observe::{
    create_agent_observe_message_preview, normalize_observe_limit, normalize_observe_max_chars,
    register_agent_observe_host_handlers, AgentFamilyStatus, AgentObserveActivity,
    AgentObserveController, AgentObserveMessagePreview, AgentObserveSummary,
};

// The unit battery lives in the child module (agent_messaging::tests);
// its use-super glob resolves through this facade's bindings and re-exports.
#[cfg(test)]
mod tests;
