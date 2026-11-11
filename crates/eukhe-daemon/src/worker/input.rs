//! The input handlers behind dispatch: prompts, steer / follow-up, and
//! agent-message delivery. Every input is a durable submission on the main
//! conversation (`whenBusy` steer / follow-up; the prompt admission id is
//! the submission request id, so a retried command never admits twice);
//! the Harness inbox queues it while a run is busy.

use std::sync::Arc;
use std::time::Duration;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_core::durable::children::Wake;
use eukhe_core::durable::input_entry;
use eukhe_durable::harness::types::{InputEntry, InputSubmissionDraft, WhenBusy};
use eukhe_durable::harness::{Conversation, SubmissionHandle};
use eukhe_durable::session::SessionError;
use eukhe_durable::types::SubmissionStatus;
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{ImageContent, TextContent, UserContent, UserContentBlock};
use serde_json::{json, Value};

use super::durable_host::suspended::WithdrawnInput;
use super::{HostedSession, RunAdmission, Worker};
use crate::agent_message_delivery::{AgentMessageDelivery, Recipient, RecipientRun};
use crate::compaction::durable::ManualCompactionError;
use crate::compaction::{CompactionManager, RunningTurn};
use crate::error_chain::ErrorChain;
use crate::protocol::{response_failure, response_success, DaemonResponse};

/// Why an input's display row does not build its input entry.
#[derive(Debug, thiserror::Error)]
pub(crate) enum InputRowError {
    /// The row's `content` is not user content.
    #[error(transparent)]
    Content(#[from] serde_json::Error),
    /// The row's `details` are not strict JSON.
    #[error(transparent)]
    Details(#[from] eukhe_chord::json::JsonError),
}

/// Why an input was not admitted.
#[derive(Debug, thiserror::Error)]
pub(crate) enum AdmitError {
    #[error(transparent)]
    Row(#[from] InputRowError),
    /// A closed Harness, a rejected busy input, a failed commit.
    #[error(transparent)]
    Session(#[from] SessionError),
}

/// The wire `customMessage` is not a custom row.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Invalid customMessage: expected a custom message object with a customType")]
pub(crate) struct InvalidCustomMessage;

/// One input to admit on the main conversation.
pub(crate) struct InputRequest {
    pub(crate) text: String,
    pub(crate) images: Vec<ImageContent>,
    /// The display row the input is placed as (an `eukhe.custom` input
    /// entry): agent-message cards, heartbeat and notice rows.
    pub(crate) custom_row: Option<Value>,
    pub(crate) when_busy: WhenBusy,
    /// Submission dedupe key (the prompt admission id, `rlm:<task>:...`).
    pub(crate) request_id: Option<String>,
    pub(crate) origin: InputOrigin,
}

impl InputRequest {
    /// The prompt as TS `AgentSession.prompt` sends it: the text block
    /// (empty for an image-only prompt), then the images.
    fn content(&self) -> UserContent {
        let mut blocks = Vec::with_capacity(self.images.len() + 1);
        blocks.push(UserContentBlock::Text(TextContent::new(self.text.clone())));
        blocks.extend(self.images.iter().cloned().map(UserContentBlock::Image));
        UserContent::Blocks(blocks)
    }

    /// The entry the input is placed as: its display row as an
    /// `eukhe.custom` input entry, or none for a plain `pi.user` input.
    ///
    /// # Errors
    ///
    /// The row's content or details are malformed.
    fn entry(&self) -> Result<Option<InputEntry>, InputRowError> {
        let Some(row) = &self.custom_row else {
            return Ok(None);
        };
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
            .unwrap_or_else(|| UserContent::Text(self.text.clone()));
        let display = row.get("display").and_then(Value::as_bool).unwrap_or(true);
        let details = row.get("details").cloned().filter(|value| !value.is_null());
        Ok(Some(input_entry(
            custom_type,
            content,
            display,
            details,
            self.origin.clone(),
        )?))
    }

    /// The input as one submission draft.
    ///
    /// # Errors
    ///
    /// The row's content or details are malformed.
    pub(crate) fn draft(&self) -> Result<InputSubmissionDraft, InputRowError> {
        Ok(InputSubmissionDraft {
            request_id: self.request_id.clone(),
            content: self.content(),
            when_busy: Some(self.when_busy),
            origin: self.origin.clone(),
            entry: self.entry()?,
        })
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
/// A malformed row (never silently degraded into a plain prompt).
pub(crate) fn parse_custom_message(
    value: Option<&Value>,
) -> Result<Option<Value>, InvalidCustomMessage> {
    let Some(value) = value.filter(|value| !value.is_null()) else {
        return Ok(None);
    };
    let object = value.as_object().ok_or(InvalidCustomMessage)?;
    if object.get("role").and_then(Value::as_str) != Some("custom") {
        return Err(InvalidCustomMessage);
    }
    if object
        .get("customType")
        .and_then(Value::as_str)
        .is_none_or(str::is_empty)
    {
        return Err(InvalidCustomMessage);
    }
    Ok(Some(value.clone()))
}

/// Admit `request` on `conversation` as one input submission; its display
/// row (if any) is the entry the input is placed as (an `eukhe.custom`
/// input entry whose model message is the input). The caller passed the
/// run gate (`_admission`) and keeps the admission until this returns.
///
/// # Errors
///
/// The admission fails (closed Harness, rejected busy input, bad row).
pub(crate) async fn submit_input(
    conversation: &Conversation,
    request: &InputRequest,
    _admission: &RunAdmission,
    cx: &Context,
) -> Result<SubmissionHandle, AdmitError> {
    Ok(conversation.submit(request.draft()?, cx).await?)
}

/// The failure text of a waited prompt that ended unanswered: the run's
/// error (pi-durable settles a failed run `model_error` with the provider
/// error text as its detail), else the
/// bare reason.
fn unsettled_text(state: &eukhe_durable::types::SubmissionState) -> String {
    state
        .detail()
        .and_then(eukhe_chord::json::JsonValue::as_str)
        .filter(|detail| !detail.is_empty())
        .or_else(|| state.reason())
        .unwrap_or("Prompt did not complete")
        .to_owned()
}

/// The `/compact [instructions]` run: the echo row, then the `compact`
/// command's manual compaction with its frame pair (the loader's
/// `compaction_start` carries the instructions; a skip ends with its
/// warning, a cancel with its aborted end). A skip or a cancel succeeds:
/// the end frame is the one report, as omp's `executeCompaction` shows one
/// `Compaction cancelled` error and keeps the command out of the editor
/// (command-controller.ts:2297-2300). A failure records the
/// `Command failed: <e>` result row and answers the error. The caller
/// passed the run gate (`admission`).
async fn compact_session_command(
    compaction: &CompactionManager,
    hosted: &HostedSession,
    main: &Conversation,
    session_command: &eukhe_core::durable::SessionCommand,
    running_turn: RunningTurn,
    admission: &RunAdmission,
) -> Result<(), String> {
    let cx = &BACKGROUND_CONTEXT;
    eukhe_core::durable::commit_session_command_echo(main, session_command, cx)
        .await
        .map_err(|error| error.to_string())?;
    let instructions = (!session_command.args.is_empty()).then(|| session_command.args.clone());
    let outcome = match compaction
        .compact(instructions, running_turn, admission)
        .await
    {
        Ok(_) | Err(ManualCompactionError::Skipped(_) | ManualCompactionError::Aborted) => Ok(()),
        Err(error @ ManualCompactionError::Failed(_)) => {
            let message = error.to_string();
            match eukhe_core::durable::commit_session_command_failure(
                main,
                session_command,
                &message,
                cx,
            )
            .await
            {
                Ok(()) => Err(message),
                Err(commit) => Err(commit.to_string()),
            }
        }
    };
    hosted.events_delivered().await;
    outcome
}

impl Worker {
    /// Admit one input on the hosted session's main conversation.
    ///
    /// # Errors
    ///
    /// The admission failure.
    pub(crate) async fn admit_input(
        &self,
        hosted: &HostedSession,
        request: &InputRequest,
    ) -> Result<SubmissionHandle, AdmitError> {
        let main = hosted.main()?;
        let admission = RunAdmission::enter(&self.core).await;
        submit_input(&main, request, &admission, &BACKGROUND_CONTEXT).await
    }

    /// Hold one admission under a live input-pause lease (TS
    /// `_sessionInputAdmissionPauses`): the input, with the entry its
    /// display row (if any) is placed as, parks in the durable held list —
    /// visible in the queue strip — and the release delivers it. A waiting
    /// prompt cannot wait the lease out: it answers the pause error while
    /// the input stays held.
    async fn hold_input(
        &self,
        hosted: &HostedSession,
        request: &InputRequest,
        command: &str,
        wait: bool,
        queued_payload: bool,
    ) -> DaemonResponse {
        let entry = match request.entry() {
            Ok(entry) => entry,
            Err(error) => {
                return response_failure(None, command, &ErrorChain(&error).to_string(), None)
            }
        };
        let held = WithdrawnInput {
            id: None,
            mode: request.when_busy.into(),
            content: request.content(),
            entry,
            origin: request.origin.clone(),
            // The sender's own key when it gave one (a retried send then
            // delivers once), else one minted for this hold.
            request: Some(
                request
                    .request_id
                    .clone()
                    .unwrap_or_else(|| format!("held:{}", uuid::Uuid::new_v4())),
            ),
        };
        if let Err(error) =
            super::mutate_withdrawn(hosted, &self.core, &self.events, move |mut state| {
                state.held.push(held);
                (state, ())
            })
            .await
        {
            return response_failure(None, command, &error.to_string(), None);
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
            Err(error) => return response_failure(None, command, &error.to_string(), None),
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
        // session instead of becoming model input. The follow-up key
        // queues a `/compact` behind a running turn.
        if images.is_empty() && custom_row.is_none() {
            if let Some(session_command) = eukhe_core::durable::classify_session_command(message) {
                let queue_behind_turn =
                    payload.get("streamingBehavior").and_then(Value::as_str) == Some("followUp");
                return self
                    .run_session_command(&hosted, command, &session_command, queue_behind_turn)
                    .await;
            }
        }
        // The first prompt of an unnamed top-level session starts its
        // generated title in the background (never awaited here).
        if custom_row.is_none() {
            self.start_title(&hosted, message);
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
            origin: InputOrigin::User,
        };
        // A user's `@name` message from another session owes that session
        // the run's final answer: the bookkeeping row commits before the
        // input it stands beside.
        if let Some(reply_to) = payload
            .get("replyTo")
            .and_then(Value::as_str)
            .filter(|id| !id.is_empty())
        {
            if let Err(error) = self.write_owed_reply(&hosted, reply_to).await {
                return response_failure(None, command, &format!("{error:#}"), None);
            }
        }
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
            Err(error) => {
                return response_failure(None, command, &ErrorChain(&error).to_string(), None)
            }
        };
        // A prompt is the user's words or main's hand-over: it wakes a
        // paused run, which places it at the boundary it parked at.
        self.heard_waking(&hosted).await;
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
                    let reason = unsettled_text(&settled.record().state);
                    response_failure(None, "prompt_and_wait", &reason, None)
                }
            },
            Err(error) => response_failure(None, "prompt_and_wait", &error.to_string(), None),
        }
    }

    /// Run one typed session command on the main conversation. The answer
    /// settles with the command (TS `_executeSelectedSessionCommand` awaits
    /// it): no turn runs, so the ack is the client's completion signal.
    /// `queue_behind_turn`: the prompt came with the follow-up key.
    async fn run_session_command(
        &self,
        hosted: &Arc<HostedSession>,
        command: &str,
        session_command: &eukhe_core::durable::SessionCommand,
        queue_behind_turn: bool,
    ) -> DaemonResponse {
        let session = match hosted.session() {
            Ok(session) => session,
            Err(error) => return response_failure(None, command, &error.to_string(), None),
        };
        let main = session.main();
        if session_command.name == eukhe_core::durable::SessionCommandName::Compact {
            return self
                .run_compact_command(hosted, &main, command, session_command, queue_behind_turn)
                .await;
        }
        let outcome = eukhe_core::durable::execute_session_command(
            &session,
            &main,
            session_command,
            &BACKGROUND_CONTEXT,
        )
        .await;
        hosted.events_delivered().await;
        // A successful `/refine` surfaces `refine_complete` through its
        // committed audit row; a failed run commits no audit, so the
        // failure event (TS `refine_failed`) is emitted here.
        if let Some(error) = outcome.refinement_failed() {
            self.emit_worker_event(eukhe_types::daemon::SessionEvent::RefineFailed {
                error: error.to_string(),
            });
        }
        match outcome.error {
            Some(error) => response_failure(None, command, &error.to_string(), None),
            None => response_success(None, command, None),
        }
    }

    /// `/compact [instructions]`, as omp's TUI `/compact`
    /// (builtin-lifecycle.ts:288-318). Sent with the follow-up key
    /// (`queue_behind_turn`) while a turn runs, it waits for the turn to
    /// yield and never touches it ("Queued compaction for when the agent
    /// yields", :305-316): a `prompt` answers at once with
    /// `compactionQueued` and the compaction runs in the background once
    /// the conversation is idle; a `prompt_and_wait` answers once it ran.
    /// Otherwise it runs now (`handleCompactCommand`, :318), interrupting a
    /// running turn and resuming it after ([`RunningTurn::Interrupt`]).
    async fn run_compact_command(
        &self,
        hosted: &Arc<HostedSession>,
        main: &Conversation,
        command: &str,
        session_command: &eukhe_core::durable::SessionCommand,
        queue_behind_turn: bool,
    ) -> DaemonResponse {
        let busy = self.core.lock().unwrap().is_busy();
        if !(busy && queue_behind_turn) {
            // A compaction is work a stop interrupts: it holds the run
            // gate until it ends.
            let admission = RunAdmission::enter(&self.core).await;
            return match compact_session_command(
                &self.compaction,
                hosted,
                main,
                session_command,
                RunningTurn::Interrupt,
                &admission,
            )
            .await
            {
                Ok(()) => response_success(None, command, None),
                Err(error) => response_failure(None, command, &error, None),
            };
        }
        let (compaction, core, hosted, main, session_command) = (
            self.compaction.clone(),
            Arc::clone(&self.core),
            Arc::clone(hosted),
            main.clone(),
            session_command.clone(),
        );
        let queued = async move {
            main.wait_for_idle(&BACKGROUND_CONTEXT)
                .await
                .map_err(|error| error.to_string())?;
            let admission = RunAdmission::enter(&core).await;
            compact_session_command(
                &compaction,
                &hosted,
                &main,
                &session_command,
                RunningTurn::Keep,
                &admission,
            )
            .await
        };
        if command == "prompt_and_wait" {
            return match queued.await {
                Ok(()) => response_success(None, command, None),
                Err(error) => response_failure(None, command, &error, None),
            };
        }
        tokio::spawn(async move {
            if let Err(error) = queued.await {
                eprintln!("eukhe-daemon: the queued /compact failed: {error}");
            }
        });
        response_success(None, command, Some(json!({ "compactionQueued": true })))
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
            Err(error) => return response_failure(None, command, &error.to_string(), None),
        };
        // Only the daemon's own durable notice producer writes the reserved
        // child-status kinds; any row claiming them on intake is refused.
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
        let request = InputRequest {
            text: message.to_string(),
            images: parse_prompt_images(payload),
            custom_row,
            when_busy,
            request_id: payload
                .get("requestId")
                .and_then(Value::as_str)
                .map(str::to_string),
            origin: InputOrigin::User,
        };
        // A live input-pause lease holds the delivery like any admission;
        // the release delivers it.
        if self.input_pauses.paused() {
            return self
                .hold_input(&hosted, &request, command, false, true)
                .await;
        }
        match self.admit_input(&hosted, &request).await {
            Ok(_) => {
                self.heard_waking(&hosted).await;
                response_success(None, command, Some(json!({ "queued": true })))
            }
            Err(error) => response_failure(None, command, &ErrorChain(&error).to_string(), None),
        }
    }

    /// Agent-to-agent message delivery, routed by the supervisor's
    /// `send_message` arm: the shared delivery
    /// ([`AgentMessageDelivery`]) behind this worker's pause gate and
    /// input-pause lease. Answers with the delivery receipt: `queued`
    /// while a run is busy, else `delivered`.
    pub(crate) async fn handle_worker_deliver_message(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "worker_deliver_message";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let message = match AgentMessageDelivery::validated_message(payload) {
            Ok(message) => message,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        if let Err(response) = self.refuse_delivery_if_paused() {
            return response;
        }
        let prepared = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let summary = self.summary_locked(&core);
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
            let recipient = Recipient {
                session_id: (!core.session_id.is_empty()).then_some(core.session_id.as_str()),
                active_session_id: &core.active_session_id,
                session_file: core.session_dir.as_deref(),
            };
            let pending = core.view.as_ref().map_or(0, |view| view.inbox.len());
            let run = if core.is_busy() {
                RecipientRun::Busy
            } else {
                RecipientRun::Idle
            };
            AgentMessageDelivery::prepare(payload, message, &recipient, pending, target)
                .map(|delivery| (delivery, run))
        };
        let (delivery, run) = match prepared {
            Ok(prepared) => prepared,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        delivery
            .record_child_reply(hosted.harness(), || Ok(hosted.main()?))
            .await;
        // A live input-pause lease holds the delivery's input like any
        // admission; the card row above already committed, and the
        // release delivers the prompt.
        if self.input_pauses.paused() {
            return self
                .hold_input(&hosted, &delivery.request, COMMAND, false, false)
                .await;
        }
        if let Err(error) = self.admit_input(&hosted, &delivery.request).await {
            return response_failure(None, COMMAND, &ErrorChain(&error).to_string(), None);
        }
        // An agent's message waits while the run is paused: the held
        // boundary places it when the run goes on.
        heard(&hosted, Wake::Waits).await;
        response_success(None, COMMAND, Some(delivery.receipt(run)))
    }
}

/// Tell the session's run pause that a message arrived (after it was
/// queued). A failure leaves the message queued: it is placed whenever the
/// run goes on.
async fn heard(hosted: &HostedSession, wake: Wake) {
    if let Err(error) = hosted
        .deps()
        .run_pause
        .message(wake, &BACKGROUND_CONTEXT)
        .await
    {
        eprintln!("eukhe-daemon worker: the run pause missed a message: {error:#}");
    }
}

/// How long main may take to take a woken worker's resume.
const RESUME_MAIN_TIMEOUT: Duration = Duration::from_secs(30);

impl Worker {
    /// A user's message or main's forward reached the session (after it
    /// was queued): it wakes a paused run. When it woke main's worker,
    /// main's tree pause ends with it, as a forward from main ends it:
    /// main's `workers` rows show the worker running again, and every
    /// paused worker tree goes on.
    async fn heard_waking(&self, hosted: &HostedSession) {
        let pause = &hosted.deps().run_pause;
        let was_paused = pause.view().paused;
        heard(hosted, Wake::Wakes).await;
        if !(was_paused && !pause.view().paused && hosted.deps().role.worker) {
            return;
        }
        let socket = self.config.supervisor_socket_path.clone();
        let main = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            core.parent_active_session_id
                .clone()
                .or_else(|| core.parent_session_id.clone())
                .or_else(|| {
                    core.parent_session_path.as_deref().map(|path| {
                        super::durable_host::storage_for_path(std::path::Path::new(path)).0
                    })
                })
        };
        let Some(main) = main.filter(|_| !socket.as_os_str().is_empty()) else {
            return;
        };
        // In the background: main's resume reaches back to this worker.
        tokio::spawn(async move {
            let resumed = crate::supervisor_link::SupervisorLink::new(socket)
                .request_success(
                    json!({ "type": "resume_workers", "activeSessionId": main }),
                    RESUME_MAIN_TIMEOUT,
                )
                .await;
            if let Err(error) = resumed {
                eprintln!(
                    "eukhe-daemon worker: ending main {main}'s worker pause failed: {error:#}"
                );
            }
        });
    }
}
