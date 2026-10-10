//! The input handlers behind dispatch: prompts, steer / follow-up, and
//! agent-message delivery. Every input is a durable submission on the main
//! conversation (`whenBusy` steer / follow-up; the prompt admission id is
//! the submission request id, so a retried command never admits twice);
//! the Harness inbox queues it while a run is busy.

use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_core::durable::input_row_draft;
use eukhe_core::session_engine::agent_messaging::{
    AgentFamilyRelationship, AgentMessagePromptPayload, AGENT_MESSAGE_SOURCE,
    DEFAULT_AGENT_MESSAGE_MAX_PENDING_PER_SESSION,
};
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy, WriteSubmissionDraft};
use eukhe_durable::harness::{Conversation, SubmissionHandle};
use eukhe_durable::types::SubmissionStatus;
use eukhe_types::pi_ai::{ImageContent, TextContent, UserContent, UserContentBlock};
use serde_json::{json, Value};

use super::durable_host::suspended::WithdrawnInput;
use super::{sender_is_child_of, HostedSession, Worker};
use crate::protocol::{response_failure, response_success, DaemonResponse};

/// One input to admit on the main conversation.
pub(crate) struct InputRequest {
    pub(crate) text: String,
    pub(crate) images: Vec<ImageContent>,
    /// A display row admitted (as an `eukhe.custom` write) right before the
    /// input: agent-message cards, heartbeat and notice rows.
    pub(crate) custom_row: Option<Value>,
    pub(crate) when_busy: WhenBusy,
    /// Submission dedupe key (the prompt admission id, `rlm:<task>:...`).
    pub(crate) request_id: Option<String>,
}

impl InputRequest {
    fn content(&self) -> UserContent {
        if self.images.is_empty() {
            return UserContent::Text(self.text.clone());
        }
        let mut blocks = Vec::with_capacity(self.images.len() + 1);
        if !self.text.is_empty() {
            blocks.push(UserContentBlock::Text(TextContent::new(self.text.clone())));
        }
        blocks.extend(self.images.iter().cloned().map(UserContentBlock::Image));
        UserContent::Blocks(blocks)
    }
}

/// Parse the wire `images` array of a prompt-family command (each entry
/// `{type: "image", data, mimeType}`); malformed entries are dropped.
pub(crate) fn parse_prompt_images(payload: &Value) -> Vec<ImageContent> {
    let Some(images) = payload.get("images").and_then(Value::as_array) else {
        return Vec::new();
    };
    images
        .iter()
        .filter_map(|image| {
            if image.get("type").and_then(Value::as_str) != Some("image") {
                return None;
            }
            Some(ImageContent {
                data: image.get("data").and_then(Value::as_str)?.to_string(),
                mime_type: image.get("mimeType").and_then(Value::as_str)?.to_string(),
            })
        })
        .collect()
}

/// The wire `customMessage` of a prompt/follow-up command: a custom row
/// (`role: "custom"` with a non-empty `customType`).
///
/// # Errors
///
/// The wire message of a malformed row (never silently degraded into a
/// plain prompt).
pub(crate) fn parse_custom_message(value: Option<&Value>) -> Result<Option<Value>, String> {
    let Some(value) = value.filter(|value| !value.is_null()) else {
        return Ok(None);
    };
    let invalid = "Invalid customMessage: expected a custom message object with a customType";
    let object = value.as_object().ok_or(invalid)?;
    if object.get("role").and_then(Value::as_str) != Some("custom") {
        return Err(invalid.to_string());
    }
    if object
        .get("customType")
        .and_then(Value::as_str)
        .is_none_or(str::is_empty)
    {
        return Err(invalid.to_string());
    }
    Ok(Some(value.clone()))
}

/// Admit `request` on `conversation`: the display row (if any) as an
/// `eukhe.custom` input row that stands for the input (no model text of its
/// own), then the input submission, which carries the model context.
///
/// # Errors
///
/// The admission fails (closed Harness, rejected busy input, bad row).
pub(crate) async fn submit_input(
    conversation: &Conversation,
    request: &InputRequest,
    cx: &Context,
) -> anyhow::Result<SubmissionHandle> {
    write_input_row(conversation, request, cx).await?;
    let handle = conversation
        .submit(
            InputSubmissionDraft {
                request_id: request.request_id.clone(),
                content: request.content(),
                when_busy: Some(request.when_busy),
            },
            cx,
        )
        .await?;
    Ok(handle)
}

/// The display row (if any) of `request` as an `eukhe.custom` input row
/// that stands for the input submitted right after it (no model text of
/// its own).
///
/// # Errors
///
/// The row write fails (closed Harness, bad row).
pub(crate) async fn write_input_row(
    conversation: &Conversation,
    request: &InputRequest,
    cx: &Context,
) -> anyhow::Result<()> {
    if let Some(row) = &request.custom_row {
        let custom_type = row
            .get("customType")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        let content: UserContent = row
            .get("content")
            .cloned()
            .map(serde_json::from_value)
            .transpose()?
            .unwrap_or_else(|| UserContent::Text(request.text.clone()));
        let display = row.get("display").and_then(Value::as_bool).unwrap_or(true);
        let details = row.get("details").cloned().filter(|value| !value.is_null());
        let entry = input_row_draft(custom_type, content, display, details)?;
        conversation
            .submit(
                WriteSubmissionDraft {
                    request_id: request.request_id.as_ref().map(|id| format!("{id}:row")),
                    entry,
                },
                cx,
            )
            .await?;
    }
    Ok(())
}

/// The rider provenance of one admission's custom row (the queue strip's
/// typed marks): the reserved child-status kinds are daemon-authentic
/// (only the minted capability admits them), a heartbeat fire is the
/// engine-minted internal prompt. Agent messages and plain prompts stay
/// user rows — a same-text human row never flags.
pub(crate) fn injection_kind(
    custom_row: Option<&Value>,
) -> Option<super::session_core::InjectionKind> {
    let row = custom_row?;
    if crate::child_status_notices::is_reserved_child_status_custom_type(row) {
        return Some(super::session_core::InjectionKind::ChildStatusNotice);
    }
    (row.get("customType").and_then(Value::as_str) == Some("heartbeat_prompt"))
        .then_some(super::session_core::InjectionKind::InjectedPrompt)
}

impl Worker {
    /// Admit one input on the hosted session's main conversation.
    ///
    /// # Errors
    ///
    /// The admission failure text.
    pub(crate) async fn admit_input(
        &self,
        hosted: &HostedSession,
        request: &InputRequest,
    ) -> Result<SubmissionHandle, String> {
        let main = hosted.main().map_err(|error| error.to_string())?;
        let handle = submit_input(&main, request, &BACKGROUND_CONTEXT)
            .await
            .map_err(|error| format!("{error:#}"))?;
        // The rider provenance of a daemon-classified admission: the
        // queue strip's marks ride by submission id.
        if let Some(kind) = injection_kind(request.custom_row.as_ref()) {
            self.core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .injected
                .insert(handle.id(), kind);
        }
        Ok(handle)
    }

    /// Hold one admission under a live input-pause lease (TS
    /// `_sessionInputAdmissionPauses`): the display row (if any) commits,
    /// the input parks in the durable held list — visible in the queue
    /// strip — and the release delivers it. A waiting prompt cannot wait
    /// the lease out: it answers the pause error while the input stays
    /// held.
    async fn hold_input(
        &self,
        hosted: &HostedSession,
        request: &InputRequest,
        command: &str,
        wait: bool,
        queued_payload: bool,
    ) -> DaemonResponse {
        let held = WithdrawnInput {
            id: None,
            mode: request.when_busy.into(),
            content: request.content(),
        };
        let held = (|| async {
            let main = hosted.main().map_err(|error| error.to_string())?;
            write_input_row(&main, request, &BACKGROUND_CONTEXT)
                .await
                .map_err(|error| format!("{error:#}"))?;
            super::mutate_withdrawn(hosted, &self.core, &self.events, move |mut state| {
                state.held.push(held);
                (state, ())
            })
            .await
        })()
        .await;
        if let Err(error) = held {
            return response_failure(None, command, &error, None);
        }
        if wait {
            return response_failure(None, command, "Session input is paused", None);
        }
        if queued_payload {
            return response_success(None, command, Some(json!({ "queued": true })));
        }
        response_success(None, command, None)
    }

    pub(crate) async fn handle_prompt(&self, payload: &Value, wait: bool) -> DaemonResponse {
        let command = if wait { "prompt_and_wait" } else { "prompt" };
        let hosted = match self.hosted(command) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let message = payload
            .get("message")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let images = parse_prompt_images(payload);
        if message.is_empty() && images.is_empty() {
            return response_failure(None, "prompt", "Prompt cannot be empty", None);
        }
        let custom_row = match parse_custom_message(payload.get("customMessage")) {
            Ok(row) => row,
            Err(error) => return response_failure(None, command, &error, None),
        };
        // The reserved child-status kinds are daemon provenance: a prompt
        // row claiming one is a spoof, answered loudly.
        if custom_row
            .as_ref()
            .is_some_and(crate::child_status_notices::is_reserved_child_status_custom_type)
        {
            return response_failure(
                None,
                command,
                &crate::child_status_notices::reserved_intake_error(),
                None,
            );
        }
        let admission_id = payload
            .get("admissionId")
            .and_then(Value::as_str)
            .filter(|id| !id.is_empty())
            .map(str::to_string);
        if let Some(id) = &admission_id {
            self.register_prompt_admission(id);
            if !self.prompt_admissions.commit(id) {
                return response_failure(None, command, "Prompt admission was cancelled.", None);
            }
        }
        // Typed session commands (`/compact`, `/goal`, ...) run on the
        // session instead of becoming model input.
        if images.is_empty() && custom_row.is_none() {
            if let Some(session_command) = eukhe_core::durable::classify_session_command(message) {
                return self
                    .run_session_command(&hosted, command, &session_command)
                    .await;
            }
        }
        let when_busy = match payload.get("streamingBehavior").and_then(Value::as_str) {
            Some("steer") => WhenBusy::Steer,
            Some(_) | None => WhenBusy::FollowUp,
        };
        let request = InputRequest {
            text: message.to_string(),
            images,
            custom_row,
            when_busy,
            request_id: admission_id.clone(),
        };
        // A live input-pause lease holds the admission (TS
        // `_sessionInputAdmissionPauses`): the input parks durable-held
        // until the release delivers it; a waiting prompt answers the
        // pause error instead of waiting the lease out.
        if self.input_pauses.paused() {
            return self
                .hold_input(&hosted, &request, command, wait, false)
                .await;
        }
        let handle = match self.admit_input(&hosted, &request).await {
            Ok(handle) => handle,
            Err(error) => return response_failure(None, command, &error, None),
        };
        if let Some(id) = &admission_id {
            // The admission stays owned until its submission settles.
            self.prompt_admissions.admitted(id, handle.id());
            let admissions = self.prompt_admissions.clone();
            let (id, settled) = (id.clone(), handle.clone());
            tokio::spawn(async move {
                let _ = settled.wait(&BACKGROUND_CONTEXT).await;
                admissions.clear(&id);
            });
        }
        if !wait {
            return response_success(None, "prompt", None);
        }
        match handle.wait(&BACKGROUND_CONTEXT).await {
            Ok(settled) => match settled.record().state.status() {
                SubmissionStatus::Done => {
                    hosted.events_delivered().await;
                    response_success(None, "prompt_and_wait", None)
                }
                SubmissionStatus::Unanswered
                | SubmissionStatus::Queued
                | SubmissionStatus::Placed => {
                    hosted.events_delivered().await;
                    let reason = settled
                        .record()
                        .state
                        .reason()
                        .unwrap_or("Prompt did not complete")
                        .to_string();
                    response_failure(None, "prompt_and_wait", &reason, None)
                }
            },
            Err(error) => response_failure(None, "prompt_and_wait", &error.to_string(), None),
        }
    }

    /// Run one typed session command on the main conversation.
    async fn run_session_command(
        &self,
        hosted: &Arc<HostedSession>,
        command: &str,
        session_command: &eukhe_core::durable::SessionCommand,
    ) -> DaemonResponse {
        let session = match hosted.session() {
            Ok(session) => session,
            Err(error) => return response_failure(None, command, &error.to_string(), None),
        };
        let main = session.main();
        let outcome = eukhe_core::durable::execute_session_command(
            &session,
            &main,
            session_command,
            &BACKGROUND_CONTEXT,
        )
        .await;
        hosted.events_delivered().await;
        match outcome.error {
            Some(error) => response_failure(None, command, &error, None),
            None => response_success(None, command, None),
        }
    }

    pub(crate) async fn handle_queue(
        &self,
        payload: &Value,
        when_busy: WhenBusy,
    ) -> DaemonResponse {
        let command = match when_busy {
            WhenBusy::Steer => "steer",
            WhenBusy::FollowUp | WhenBusy::Reject => "follow_up",
        };
        let hosted = match self.hosted(command) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let message = payload
            .get("message")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let custom_row = match parse_custom_message(payload.get("customMessage")) {
            Ok(row) => row,
            Err(error) => return response_failure(None, command, &error, None),
        };
        // The daemon's own child-status notices carry a one-shot minted
        // capability; any other row claiming the reserved kinds is refused.
        if custom_row
            .as_ref()
            .is_some_and(crate::child_status_notices::is_reserved_child_status_custom_type)
            && !crate::child_status_notices::consume(
                payload.get("rlmNoticeNonce").and_then(Value::as_str),
            )
        {
            return response_failure(
                None,
                command,
                &crate::child_status_notices::reserved_intake_error(),
                None,
            );
        }
        let request = InputRequest {
            text: message.to_string(),
            images: parse_prompt_images(payload),
            custom_row,
            when_busy,
            request_id: payload
                .get("requestId")
                .and_then(Value::as_str)
                .map(str::to_string),
        };
        // A live input-pause lease holds the delivery like any admission;
        // the release delivers it.
        if self.input_pauses.paused() {
            return self
                .hold_input(&hosted, &request, command, false, true)
                .await;
        }
        match self.admit_input(&hosted, &request).await {
            Ok(_) => response_success(None, command, Some(json!({ "queued": true }))),
            Err(error) => response_failure(None, command, &error, None),
        }
    }

    /// Agent-to-agent message delivery, routed by the supervisor's
    /// `send_message` arm: the `[agent-message from ...]` prompt is admitted
    /// as input on the requested lane, preceded by the `agent_message`
    /// display row (the collapsed card). Answers with the delivery receipt:
    /// `queued` while a run is busy, else `delivered`.
    pub(crate) async fn handle_worker_deliver_message(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "worker_deliver_message";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let message = payload
            .get("message")
            .and_then(Value::as_str)
            .unwrap_or_default();
        if let Err(error) =
            eukhe_core::session_engine::agent_messaging::normalize_agent_session_message(message)
        {
            return response_failure(None, COMMAND, &error.to_string(), None);
        }
        if let Err(response) = self.refuse_delivery_if_paused() {
            return response;
        }
        let sender = payload.get("sender").cloned().unwrap_or(Value::Null);
        // Sender label precedence: session name, session id, active session
        // id, client id.
        let sender_name = ["sessionName", "sessionId", "activeSessionId", "clientId"]
            .iter()
            .find_map(|key| sender.get(*key).and_then(Value::as_str))
            .unwrap_or("unknown")
            .to_string();
        let (from_relationship, pending, queued, summary) = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            (
                sender_is_child_of(&sender, &core).then_some(AgentFamilyRelationship::Child),
                core.view.as_ref().map_or(0, |view| view.inbox.len()),
                core.is_busy(),
                self.summary_locked(&core),
            )
        };
        if let Err(error) =
            eukhe_core::session_engine::agent_messaging::assert_agent_message_queue_capacity(
                pending,
                DEFAULT_AGENT_MESSAGE_MAX_PENDING_PER_SESSION,
            )
        {
            return response_failure(None, COMMAND, &error.to_string(), None);
        }
        let prompt =
            eukhe_core::session_engine::agent_messaging::create_agent_session_message_prompt(
                &AgentMessagePromptPayload {
                    message: message.to_string(),
                    sender_name,
                    from_relationship,
                },
            );
        let id = eukhe_core::session_engine::agent_messaging::create_agent_session_message_id();
        let mut target = json!({
            "activeSessionId": summary.active_session_id.clone().unwrap_or_default(),
            "sessionId": summary.session_id,
            "runtimeKind": summary
                .runtime_kind
                .clone()
                .unwrap_or_else(|| "top-level".to_string()),
        });
        if let Some(name) = summary.session_name.filter(|name| !name.is_empty()) {
            target["sessionName"] = json!(name);
        }
        let row = eukhe_core::session_engine::agent_messaging::create_agent_session_message_row(
            &eukhe_core::session_engine::agent_messaging::AgentSessionMessageRowPayload {
                id: &id,
                prompt: &prompt,
                message,
                from: &sender,
                from_relationship,
                target: Some(&target),
                timestamp: crate::util::now_ms(),
            },
        );
        let follow_up = payload.get("deliveryMode").and_then(Value::as_str) == Some("follow_up");
        let request = InputRequest {
            text: prompt,
            images: Vec::new(),
            custom_row: Some(row),
            when_busy: if follow_up {
                WhenBusy::FollowUp
            } else {
                WhenBusy::Steer
            },
            request_id: Some(format!("agent-message:{id}")),
        };
        // A live input-pause lease holds the delivery's input like any
        // admission; the card row above already committed, and the
        // release delivers the prompt.
        if self.input_pauses.paused() {
            return self
                .hold_input(&hosted, &request, COMMAND, false, false)
                .await;
        }
        if let Err(error) = self.admit_input(&hosted, &request).await {
            return response_failure(None, COMMAND, &error, None);
        }
        let timestamp = crate::util::now_iso();
        let mut receipt = json!({
            "id": id,
            "source": AGENT_MESSAGE_SOURCE,
            "target": target,
            "message": message,
            "deliveryMode": if follow_up { "follow_up" } else { "steer" },
        });
        if queued {
            receipt["deliveryStatus"] = json!("queued");
            receipt["queuedAt"] = json!(timestamp);
        } else {
            receipt["deliveryStatus"] = json!("delivered");
            receipt["deliveredAt"] = json!(timestamp);
        }
        if !sender.is_null() {
            receipt["from"] = json!(sender);
        }
        response_success(None, COMMAND, Some(receipt))
    }
}
