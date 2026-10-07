//! The agent-message ingestion surface (protocol breadth wave b7): the
//! worker arms for `agent_messages_status`, `agent_messages_pause`,
//! `agent_messages_resume`, and `agent_messages_clear` (TS daemon-mode
//! `case "agent_messages_status"` ... `case "agent_messages_clear"`, over
//! `getAgentMessageSafetyStatus` / the `agentMessagesPaused` flag /
//! `clearQueuedAgentMessages`), plus the paused gate the delivery path
//! answers ("Agent messaging is paused", TS `sendAgentSessionMessage`).
//!
//! A delivered agent message is two submissions on the main conversation
//! (`worker_deliver_message`): the `agent_message` card as an `eukhe.custom`
//! write (`agent-message:<id>:row`) and the prompt as an input
//! (`agent-message:<id>`). The clear withdraws both while they wait in the
//! Harness inbox; [`withdraw_queued`] is the shared inbox withdrawal the
//! bash notices and the scheduled fires use too.
//!
//! Porting note (rate limiter): the TS worker also paces deliveries through
//! a per-sender token bucket (`AgentSessionMessageRateLimiter`, capacity 3
//! / refill 1s). The status arm reports the TS constants verbatim; this
//! port does not refuse deliveries on the bucket (the daemon's queue
//! capacity bound is the enforced limit), a documented deviation from the
//! TS ingestion behavior.

use std::sync::atomic::{AtomicBool, Ordering};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::harness::{AbortSubmissionResult, InboxItem, InboxState, INBOX_DOC};
use eukhe_durable::types::SubmissionId;
use eukhe_types::pi_ai::UserContent;
use serde_json::{json, Value};

use eukhe_core::session_engine::agent_messaging::{
    DEFAULT_AGENT_MESSAGE_MAX_CHARS, DEFAULT_AGENT_MESSAGE_MAX_PENDING_PER_SESSION,
    DEFAULT_AGENT_MESSAGE_RATE_LIMIT_CAPACITY, DEFAULT_AGENT_MESSAGE_RATE_LIMIT_REFILL_MS,
};

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::durable_host::bridge::content_preview;
use crate::worker::{HostedSession, Worker};

/// The request-id prefix of agent-message submissions.
const AGENT_MESSAGE_REQUEST_PREFIX: &str = "agent-message:";

/// The worker's agent-message ingestion state: the pause flag all four
/// arms read and the delivery gate checks.
pub(crate) struct AgentMessageIngest {
    paused: AtomicBool,
}

impl AgentMessageIngest {
    pub(crate) fn new() -> Self {
        AgentMessageIngest {
            paused: AtomicBool::new(false),
        }
    }

    pub(crate) fn paused(&self) -> bool {
        self.paused.load(Ordering::SeqCst)
    }

    fn set_paused(&self, paused: bool) {
        self.paused.store(paused, Ordering::SeqCst);
    }
}

impl Default for AgentMessageIngest {
    fn default() -> Self {
        Self::new()
    }
}

/// The inbox lane a withdrawn submission waited on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WithdrawnLane {
    Steer,
    FollowUp,
    /// A passive entry write (a display row).
    Write,
}

/// One submission [`withdraw_queued`] took out of the inbox.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Withdrawn {
    pub(crate) request_id: String,
    pub(crate) lane: WithdrawnLane,
    /// The input's preview text (empty for writes).
    pub(crate) text: String,
}

/// Withdraw the main conversation's queued submissions whose request id
/// `select` accepts, in inbox order. A submission a boundary placed in the
/// meantime stays (it is no longer queued).
///
/// # Errors
///
/// The main conversation, the `pi.inbox` document, or a submission record
/// cannot be read, or an abort fails.
pub(crate) async fn withdraw_queued(
    hosted: &HostedSession,
    mut select: impl FnMut(&str) -> bool,
) -> anyhow::Result<Vec<Withdrawn>> {
    let cx = &BACKGROUND_CONTEXT;
    let main = hosted.main()?;
    let harness = hosted.harness();
    let Some(value) = harness.snapshot(&INBOX_DOC, main.id(), cx).await? else {
        return Ok(Vec::new());
    };
    let inbox: InboxState = from_json(&JsonValue::Object(value))?;
    let mut withdrawn = Vec::new();
    for item in inbox.items {
        let (id, lane, content): (SubmissionId, WithdrawnLane, Option<UserContent>) = match item {
            InboxItem::Steer { id, content } => (id, WithdrawnLane::Steer, Some(content)),
            InboxItem::FollowUp { id, content } => (id, WithdrawnLane::FollowUp, Some(content)),
            InboxItem::Write { id, .. } => (id, WithdrawnLane::Write, None),
        };
        let Some(handle) = harness.submission(id, cx).await? else {
            continue;
        };
        let Some(request_id) = handle.status(cx).await?.request_id else {
            continue;
        };
        if !select(&request_id) {
            continue;
        }
        match harness.abort_submission(id, Some(main.id()), cx).await? {
            AbortSubmissionResult::Aborted => withdrawn.push(Withdrawn {
                request_id,
                lane,
                text: content.as_ref().map(content_preview).unwrap_or_default(),
            }),
            AbortSubmissionResult::AlreadyPlaced
            | AbortSubmissionResult::Settled
            | AbortSubmissionResult::NotFound => {}
        }
    }
    Ok(withdrawn)
}

impl Worker {
    /// The TS `getAgentMessageSafetyStatus` wire object: the pause flag
    /// plus the four ingestion limits (the TS constants; see the module
    /// note for the rate-limiter deviation).
    fn agent_message_safety_status(&self) -> Value {
        json!({
            "paused": self.agent_messages.paused(),
            "maxMessageChars": DEFAULT_AGENT_MESSAGE_MAX_CHARS,
            "maxPendingPerSession": DEFAULT_AGENT_MESSAGE_MAX_PENDING_PER_SESSION,
            "rateLimitCapacity": DEFAULT_AGENT_MESSAGE_RATE_LIMIT_CAPACITY,
            "rateLimitRefillMs": DEFAULT_AGENT_MESSAGE_RATE_LIMIT_REFILL_MS,
        })
    }

    /// `agent_messages_status`: the safety status, no side effects.
    pub(crate) fn handle_agent_messages_status(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("agent_messages_status") {
            return response;
        }
        response_success(
            None,
            "agent_messages_status",
            Some(self.agent_message_safety_status()),
        )
    }

    /// `agent_messages_pause`: set the flag, then drop every queued
    /// agent-message submission (TS also clears the rate limiter - see the
    /// module note) and answer the safety status.
    pub(crate) async fn handle_agent_messages_pause(&self) -> DaemonResponse {
        let hosted = match self.hosted("agent_messages_pause") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        self.agent_messages.set_paused(true);
        if let Err(error) = clear_queued_agent_messages(&hosted).await {
            return response_failure(None, "agent_messages_pause", &format!("{error:#}"), None);
        }
        response_success(
            None,
            "agent_messages_pause",
            Some(self.agent_message_safety_status()),
        )
    }

    /// `agent_messages_resume`: clear the flag and answer the safety
    /// status.
    pub(crate) fn handle_agent_messages_resume(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("agent_messages_resume") {
            return response;
        }
        self.agent_messages.set_paused(false);
        response_success(
            None,
            "agent_messages_resume",
            Some(self.agent_message_safety_status()),
        )
    }

    /// `agent_messages_clear`: drop this session's queued agent-message
    /// submissions and answer the TS `clearQueuedAgentMessages` shape (the
    /// removed prompts per lane).
    pub(crate) async fn handle_agent_messages_clear(&self) -> DaemonResponse {
        let hosted = match self.hosted("agent_messages_clear") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        match clear_queued_agent_messages(&hosted).await {
            Ok(cleared) => response_success(None, "agent_messages_clear", Some(cleared)),
            Err(error) => {
                response_failure(None, "agent_messages_clear", &format!("{error:#}"), None)
            }
        }
    }

    /// The delivery gate (TS `sendAgentSessionMessage`'s paused check):
    /// the exact TS error string, surfaced through the worker's private
    /// `worker_deliver_message` arm so a client's `send_message` fails
    /// with it.
    // DaemonResponse is the wide wire response; the error channel carries it.
    #[allow(clippy::result_large_err)]
    pub(crate) fn refuse_delivery_if_paused(&self) -> Result<(), DaemonResponse> {
        if self.agent_messages.paused() {
            return Err(response_failure(
                None,
                "worker_deliver_message",
                "Agent messaging is paused",
                None,
            ));
        }
        Ok(())
    }
}

/// Withdraw the queued agent-message submissions (TS
/// `clearQueuedAgentMessages`: only agent-message prompts and their cards,
/// never client-queued prompts) and answer the removed prompts per lane,
/// exactly the TS `{ steering, followUp }` shape.
async fn clear_queued_agent_messages(hosted: &HostedSession) -> anyhow::Result<Value> {
    let withdrawn = withdraw_queued(hosted, |request_id| {
        request_id.starts_with(AGENT_MESSAGE_REQUEST_PREFIX)
    })
    .await?;
    let texts = |lane: WithdrawnLane| {
        withdrawn
            .iter()
            .filter(|item| item.lane == lane)
            .map(|item| item.text.clone())
            .collect::<Vec<_>>()
    };
    Ok(json!({
        "steering": texts(WithdrawnLane::Steer),
        "followUp": texts(WithdrawnLane::FollowUp),
    }))
}

#[cfg(test)]
mod tests;
