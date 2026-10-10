//! Run helpers shared by admission, generation, compaction, and scheduler
//! cleanup (TS `generation.ts`: `startRun`, `createGeneration`, `handOver`,
//! `convertPartial`, `appendAssistant`; `compaction.ts`: `createCompaction`).
//! They live with `pi.live` so admission and conversations do not depend on
//! the built-in task modules; the built-in definitions come from the
//! registry's [`crate::harness::types::BuiltinTasks`].

use eukhe_chord::delta::Draft;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_types::pi_ai::{AssistantMessage, Message, StopReason};
use serde::{Deserialize, Serialize};

use super::{add_compaction_status, child_draft, run_task_id, CompactionStatus, LiveRun, LIVE_DOC};
use crate::entries::ASSISTANT_ENTRY;
use crate::harness::types::{CompactionReason, CompactionResult};
use crate::harness::usage::{record_usage, UsageBucket};
use crate::session::{SessionError, SessionResult, Tx};
use crate::tasks::AnyTask;
use crate::types::{
    ConversationId, NoData, SubmissionId, TaskId, TaskOptions, TaskOwnership, TypedEntry,
    TypedEntryDraft,
};

/// A Harness clock reading as a pi-ai message timestamp. pi-ai timestamps are
/// integral milliseconds (`u64`); TS would store any number, so a clock that
/// returns a negative or fractional value is rejected explicitly.
///
/// # Errors
///
/// `now` is not a non-negative safe integer.
pub(crate) fn timestamp(now: f64) -> SessionResult<u64> {
    let integral = now.fract() == 0.0 && (0.0..=eukhe_chord::json::MAX_SAFE_INTEGER).contains(&now);
    if !integral {
        return Err(SessionError::type_error(format!(
            "Timestamp {now} is not a non-negative integer"
        )));
    }
    // A non-negative safe integer converts exactly.
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "checked above: a non-negative integer within 2^53"
    )]
    Ok(now as u64)
}

/// Start a run for `inputs`, placed input submissions: a new generation
/// takes `pi.live.run`.
///
/// # Errors
///
/// Task creation, tracker, and JSON failures.
pub async fn start_run(
    tx: &Tx,
    generation: &AnyTask,
    conversation_id: ConversationId,
    live: &Draft,
    inputs: Vec<SubmissionId>,
) -> SessionResult<()> {
    let task_id = create_generation(tx, generation, conversation_id).await?;
    live.set("run", to_json(&LiveRun { task_id, inputs })?)?;
    Ok(())
}

/// A generation owned by its conversation.
///
/// # Errors
///
/// Task creation failures.
pub async fn create_generation(
    tx: &Tx,
    generation: &AnyTask,
    conversation_id: ConversationId,
) -> SessionResult<TaskId> {
    tx.create_task(
        generation.as_definition_ref(),
        JsonValue::object(),
        TaskOptions {
            ownership: TaskOwnership::Conversation,
            conversation_id: Some(conversation_id),
            background: None,
            abandon_on_restart: None,
        },
    )
    .await
}

/// Hand run control from `from` to `to`; the run's inputs move with it.
///
/// # Errors
///
/// Tracker and JSON failures.
pub fn hand_over(live: &Draft, from: TaskId, to: TaskId) -> SessionResult<()> {
    if run_task_id(live)? == Some(from) {
        live.child("run")?.set("taskId", to_json(&to)?)?;
    }
    Ok(())
}

/// Append a committed partial left by an interrupted, aborted, faulted, or
/// orphaned attempt as an aborted assistant entry; the caller replaces or
/// removes `generation`.
///
/// # Errors
///
/// Tracker, JSON, and append failures.
pub async fn convert_partial(
    tx: &Tx,
    live: &Draft,
    conversation_id: ConversationId,
) -> SessionResult<()> {
    let Some(generation) = child_draft(live, "generation")? else {
        return Ok(());
    };
    let Some(partial) = generation.get("message")? else {
        return Ok(());
    };
    let mut message: AssistantMessage = from_json(&partial.to_value()?)?;
    message.stop_reason = StopReason::Aborted;
    append_assistant(tx, conversation_id, message).await?;
    Ok(())
}

/// Append a provider result and add its usage to `pi.usage` in the same
/// commit.
///
/// REMINDER: every built-in writer of assistant entries goes through here, so
/// the usage ledger stays complete.
///
/// # Errors
///
/// Document and append failures.
pub async fn append_assistant(
    tx: &Tx,
    conversation_id: ConversationId,
    message: AssistantMessage,
) -> SessionResult<TypedEntry<NoData>> {
    let key = format!("{}/{}", message.provider, message.model);
    record_usage(
        tx,
        conversation_id,
        UsageBucket::Models,
        &key,
        &message.usage,
    )
    .await?;
    tx.append_typed_entry(
        &ASSISTANT_ENTRY,
        conversation_id,
        TypedEntryDraft {
            model: Some(vec![Message::Assistant(message)]),
            ..TypedEntryDraft::default()
        },
    )
    .await
}

/// Input of the built-in compaction task (TS `CompactionInput`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactionInput {
    pub reason: CompactionReason,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instructions: Option<String>,
}

/// Create a compaction task with its status in this commit. `owner` is the
/// generation that waits for it (a blocking compaction); without one it is
/// conversation-owned, and `background` unless it is manual.
///
/// # Errors
///
/// Task creation, document, and JSON failures.
pub async fn create_compaction(
    tx: &Tx,
    compaction: &AnyTask,
    conversation_id: ConversationId,
    input: CompactionInput,
    owner: Option<TaskId>,
) -> SessionResult<TaskId<CompactionResult>> {
    let ownership = match owner {
        None => TaskOwnership::Conversation,
        Some(task_id) => TaskOwnership::Task { task_id },
    };
    let background = owner.is_none() && input.reason != CompactionReason::Manual;
    let task_id = tx
        .create_task(
            compaction.as_definition_ref(),
            to_json(&input)?,
            TaskOptions {
                ownership,
                conversation_id: Some(conversation_id),
                background: Some(background),
                abandon_on_restart: None,
            },
        )
        .await?;
    let status = CompactionStatus {
        task_id,
        reason: input.reason,
        blocking: owner.is_some(),
        attempt: 1,
        retry: None,
    };
    add_compaction_status(&tx.doc(&LIVE_DOC, conversation_id).await?, &status)?;
    Ok(TaskId::from_number(task_id.get()))
}
