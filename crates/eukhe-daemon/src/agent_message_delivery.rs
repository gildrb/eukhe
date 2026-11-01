//! One agent message delivered into a session's main conversation, the
//! one path both recipients run: a daemon worker's
//! `worker_deliver_message` arm and a headless parent's
//! `headless_parent_delivery` frame ([`crate::headless_parent`]). The
//! `[agent-message from ...]` prompt is admitted as an input on the
//! requested lane with the `agent_message` card as the entry it is placed
//! as; the answer is the delivery receipt: `queued` while a run is busy,
//! else `delivered`.

use std::path::Path;

use eukhe_core::agent_messaging::{
    agent_session_message_report, assert_agent_message_queue_capacity,
    create_agent_session_message_id, create_agent_session_message_row,
    normalize_agent_session_message, AgentFamilyRelationship, AgentMessagePromptPayload,
    AgentSessionMessageRowPayload, AGENT_MESSAGE_SOURCE,
    DEFAULT_AGENT_MESSAGE_MAX_PENDING_PER_SESSION,
};
use eukhe_durable::harness::types::WhenBusy;
use eukhe_durable::harness::{Conversation, Harness};
use eukhe_types::input_origin::InputOrigin;
use serde_json::{json, Value};

use crate::worker::InputRequest;

/// The recipient's durable identity, which a sender's parent edge is read
/// against.
pub(crate) struct Recipient<'a> {
    /// The persisted session id (`None` when not known yet).
    pub(crate) session_id: Option<&'a str>,
    /// The live session id.
    pub(crate) active_session_id: &'a str,
    /// The session's storage.
    pub(crate) session_file: Option<&'a Path>,
}

/// Whether the recipient's main conversation runs a turn when the message
/// arrives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RecipientRun {
    /// A run is busy: the message waits for its boundary.
    Busy,
    /// Idle: the message wakes the conversation into a turn.
    Idle,
}

/// One message ready to admit, and its receipt.
pub(crate) struct AgentMessageDelivery {
    /// The input that carries the message (its card is the entry).
    pub(crate) request: InputRequest,
    id: String,
    message: String,
    sender: Value,
    target: Value,
    /// The lane's wire name (`steer` or `follow_up`).
    delivery_mode: &'static str,
    /// The sender's ids when it is one of the recipient's children.
    child_sender_ids: Option<Vec<String>>,
}

impl AgentMessageDelivery {
    /// The message a delivery payload carries, once it passes the message
    /// limits.
    ///
    /// # Errors
    ///
    /// The limit error text (an empty or oversized message).
    pub(crate) fn validated_message(payload: &Value) -> Result<&str, String> {
        let message = payload
            .get("message")
            .and_then(Value::as_str)
            .unwrap_or_default();
        normalize_agent_session_message(message).map_err(|error| error.to_string())?;
        Ok(message)
    }

    /// The delivery of `message` (from [`Self::validated_message`] over
    /// `payload`, which also carries the `sender` block and the
    /// `deliveryMode`) to `recipient`, which holds `pending` queued inputs;
    /// `target` is the receipt's description of the recipient.
    ///
    /// # Errors
    ///
    /// The queue-capacity error text when the recipient's inbox is full.
    pub(crate) fn prepare(
        payload: &Value,
        message: &str,
        recipient: &Recipient<'_>,
        pending: usize,
        target: Value,
    ) -> Result<Self, String> {
        let sender = payload.get("sender").cloned().unwrap_or(Value::Null);
        // Sender label precedence: session name, session id, active session
        // id, client id.
        let sender_name = ["sessionName", "sessionId", "activeSessionId", "clientId"]
            .iter()
            .find_map(|key| sender.get(*key).and_then(Value::as_str))
            .unwrap_or("unknown")
            .to_string();
        let from_relationship =
            sender_parent_edge_is(&sender, recipient).then_some(AgentFamilyRelationship::Child);
        assert_agent_message_queue_capacity(pending, DEFAULT_AGENT_MESSAGE_MAX_PENDING_PER_SESSION)
            .map_err(|error| error.to_string())?;
        let child_sender_ids =
            (from_relationship == Some(AgentFamilyRelationship::Child)).then(|| {
                ["activeSessionId", "sessionId"]
                    .iter()
                    .filter_map(|key| sender.get(*key).and_then(Value::as_str))
                    .map(str::to_string)
                    .collect()
            });
        let report = agent_session_message_report(&AgentMessagePromptPayload {
            message: message.to_string(),
            sender_name,
            from_relationship,
        });
        let prompt = report.render(message);
        let id = create_agent_session_message_id();
        let row = create_agent_session_message_row(&AgentSessionMessageRowPayload {
            id: &id,
            prompt: &prompt,
            message,
            from: &sender,
            from_relationship,
            target: Some(&target),
            timestamp: crate::util::now_ms(),
        });
        let (when_busy, delivery_mode) =
            if payload.get("deliveryMode").and_then(Value::as_str) == Some("follow_up") {
                (WhenBusy::FollowUp, "follow_up")
            } else {
                (WhenBusy::Steer, "steer")
            };
        let request = InputRequest {
            text: prompt,
            images: Vec::new(),
            custom_row: Some(row),
            when_busy,
            request_id: Some(format!("agent-message:{id}")),
            origin: InputOrigin::Report { report },
        };
        Ok(Self {
            request,
            id,
            message: message.to_string(),
            sender,
            target,
            delivery_mode,
            child_sender_ids,
        })
    }

    /// A child's message to this parent is its reply: its settle owes no
    /// no-reply notice (and so no extra parent turn restating it). The
    /// mark commits on the child's durable row before the receipt answers,
    /// so the child's own settle can never overtake it. A failed mark is
    /// logged; the message still delivers.
    pub(crate) async fn record_child_reply(
        &self,
        harness: &Harness,
        main: impl FnOnce() -> anyhow::Result<Conversation>,
    ) {
        let Some(sender_ids) = &self.child_sender_ids else {
            return;
        };
        let marked = async {
            eukhe_core::durable::children::mark_child_replied(
                harness,
                main()?.id(),
                sender_ids.clone(),
            )
            .await
        }
        .await;
        if let Err(error) = marked {
            eprintln!("eukhe: recording the child's reply failed: {error:#}");
        }
    }

    /// The receipt of the admitted message, by whether the recipient was
    /// running when it arrived.
    pub(crate) fn receipt(&self, run: RecipientRun) -> Value {
        let timestamp = crate::util::now_iso();
        let mut receipt = json!({
            "id": self.id,
            "source": AGENT_MESSAGE_SOURCE,
            "target": self.target,
            "message": self.message,
            "deliveryMode": self.delivery_mode,
        });
        match run {
            RecipientRun::Busy => {
                receipt["deliveryStatus"] = json!("queued");
                receipt["queuedAt"] = json!(timestamp);
            }
            RecipientRun::Idle => {
                receipt["deliveryStatus"] = json!("delivered");
                receipt["deliveredAt"] = json!(timestamp);
            }
        }
        if !self.sender.is_null() {
            receipt["from"] = self.sender.clone();
        }
        receipt
    }
}

/// Whether a delivery's sender is one of `recipient`'s children, by the
/// sender block's recorded durable parent edge: the persisted session id
/// first, then the live active id, then the session-storage alias.
fn sender_parent_edge_is(sender: &Value, recipient: &Recipient<'_>) -> bool {
    let text = |key: &str| sender.get(key).and_then(Value::as_str);
    if let (Some(parent), Some(own)) = (text("parentSessionId"), recipient.session_id) {
        if parent == own {
            return true;
        }
    }
    if text("parentActiveSessionId") == Some(recipient.active_session_id) {
        return true;
    }
    match (text("parentSessionPath"), recipient.session_file) {
        (Some(parent), Some(own)) => Path::new(parent) == own,
        (Some(_), None) | (None, Some(_) | None) => false,
    }
}
