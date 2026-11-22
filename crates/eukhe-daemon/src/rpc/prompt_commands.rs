//! The RPC command surface, part two: the prompt-family handlers —
//! `prompt` (with the session commands it admits) and `steer`/`follow_up`
//! — as durable input submissions on the main conversation (TS
//! `prompt`/`steer`/`followUp`). The conversation's inbox owns the queued
//! inputs and their delivery.

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_core::durable::{
    classify_session_command, execute_session_command, EukheSession, SessionCommand,
};
use eukhe_durable::errors::ConversationBusy;
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_durable::harness::Conversation;
use eukhe_durable::session::SessionError;
use eukhe_durable::types::TaskOutcome;
use eukhe_types::budget::RunKind;
use eukhe_types::input_origin::InputOrigin;
use serde_json::Value;

use super::commands::RpcState;
use super::error::RpcCommandError;
use super::protocol::{self, ResponseData};
use super::reads::{is_busy, rpc_context};

/// `prompt` (TS `connection.prompt(message, {images, streamingBehavior,
/// source: "rpc"})`): admission-level success — the response fires once
/// the input is durably admitted (TS `preflightResult` over
/// `returnAfterAccepted: true`; the run's events follow on the ordered
/// stream, buffered behind the response). A busy conversation queues the
/// input per `streamingBehavior` and refuses it without one. Session
/// commands (`/compact`, `/refine`, `/auto`, `/autonomous`) execute
/// through the shared durable executor, which commits their rows.
///
/// # Errors
///
/// A missing message, the busy refusal, the admission failure, and the
/// admitted session command's own error.
pub(crate) async fn prompt(
    state: &Arc<RpcState>,
    payload: &Value,
) -> Result<ResponseData, RpcCommandError> {
    let message = payload
        .get("message")
        .and_then(Value::as_str)
        .ok_or_else(|| RpcCommandError::missing("prompt", "a message"))?;
    let images = protocol::command_images(payload);
    let behavior = protocol::command_streaming_behavior(payload);
    // The handle guard stays held through the admission (and a session
    // command's execution): a concurrent replacement cannot close the
    // session under it.
    let handle = state.session.handle().await;
    let session = &handle.session;
    let main = session.main();
    let cx = rpc_context();
    if let Some(command) = classify_session_command(message) {
        run_session_command(state, session, &main, &command, &cx).await?;
        return Ok(ResponseData::Absent);
    }
    // A prompt without a `streamingBehavior` that reaches a busy
    // conversation is refused below: its prefix asks nothing of the run.
    let message = if behavior.is_none() && is_busy(session.harness(), main.id(), &cx).await? {
        message.to_owned()
    } else {
        begin_message(session, &main, message, &cx).await?
    };
    let draft = InputSubmissionDraft {
        request_id: None,
        content: protocol::command_content(&message, images),
        when_busy: Some(behavior.unwrap_or(WhenBusy::Reject)),
        origin: InputOrigin::User,
        entry: None,
    };
    main.submit(draft, &cx).await.map_err(|error| {
        if is_busy_refusal(&error) {
            RpcCommandError::PromptWhileBusy { source: error }
        } else {
            RpcCommandError::Session(error)
        }
    })?;
    Ok(ResponseData::Absent)
}

/// Whether a submission failed because the conversation was busy.
fn is_busy_refusal(error: &SessionError) -> bool {
    match error {
        SessionError::Other(inner) => inner.downcast_ref::<ConversationBusy>().is_some(),
        _ => false,
    }
}

/// Execute one session command the prompt admitted. A `/compact` waits
/// for its compaction task, so the response reports the compaction's
/// failure and the compaction frames (buffered behind the response) are
/// all published once the response is.
async fn run_session_command(
    state: &RpcState,
    session: &EukheSession,
    main: &Conversation,
    command: &SessionCommand,
    cx: &Context,
) -> Result<(), RpcCommandError> {
    let outcome = {
        let _ops = state.session_ops.lock().await;
        execute_session_command(session, main, command, cx).await
    };
    if let Some(error) = outcome.error {
        return Err(error.into());
    }
    if let Some(task) = outcome.compaction {
        let settled = session.harness().wait_for_task(task, cx).await?;
        match settled.outcome {
            TaskOutcome::Completed { .. } => {}
            TaskOutcome::Failed { error, .. } | TaskOutcome::Faulted { error } => {
                return Err(RpcCommandError::CompactionFailed {
                    message: error.message,
                });
            }
            TaskOutcome::Aborted { reason, .. } => {
                return Err(RpcCommandError::CompactionAborted { reason });
            }
            TaskOutcome::Orphaned { reason } => {
                return Err(RpcCommandError::CompactionOrphaned { reason });
            }
        }
    }
    Ok(())
}

/// `steer` / `follow_up` (TS `connection.steer/followUp(message,
/// images)`): admit the input with `whenBusy` steer/followUp — a busy
/// conversation queues it for its boundary, an idle one starts a run with
/// it.
///
/// # Errors
///
/// The missing-message error, or the admission failure.
pub(crate) async fn steer_or_follow_up(
    state: &Arc<RpcState>,
    payload: &Value,
    name: &str,
) -> Result<ResponseData, RpcCommandError> {
    let message = payload
        .get("message")
        .and_then(Value::as_str)
        .ok_or_else(|| RpcCommandError::missing(name, "a message"))?;
    let images = protocol::command_images(payload);
    let when_busy = if name == "steer" {
        WhenBusy::Steer
    } else {
        WhenBusy::FollowUp
    };
    let handle = state.session.handle().await;
    let session = &handle.session;
    let main = session.main();
    let cx = rpc_context();
    let message = begin_message(session, &main, message, &cx).await?;
    let draft = InputSubmissionDraft {
        request_id: None,
        content: protocol::command_content(&message, images),
        when_busy: Some(when_busy),
        origin: InputOrigin::User,
        entry: None,
    };
    main.submit(draft, &cx).await?;
    Ok(ResponseData::Absent)
}

/// Begin the principal's message `text` on `session`'s budget
/// (`BudgetGate::begin_message`): sent while `main` runs nothing it starts
/// a run of the session's kind, else the running run takes what its `/b`
/// prefix asks. Returns what follows the prefix.
async fn begin_message(
    session: &EukheSession,
    main: &Conversation,
    text: &str,
    cx: &Context,
) -> Result<String, RpcCommandError> {
    let joins = is_busy(session.harness(), main.id(), cx).await?;
    let gate = session.budget();
    let text = text.to_owned();
    Ok(tokio::task::spawn_blocking(move || {
        let kind = gate.run_kind().unwrap_or(RunKind::Interactive);
        gate.begin_message(kind, joins, &text)
    })
    .await??)
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_durable::types::ConversationId;

    #[test]
    fn busy_refusals_are_recognized() {
        let busy = SessionError::other(ConversationBusy::new(ConversationId::from_number(1)));
        assert!(is_busy_refusal(&busy));
        assert!(!is_busy_refusal(&SessionError::error("other")));
    }
}
