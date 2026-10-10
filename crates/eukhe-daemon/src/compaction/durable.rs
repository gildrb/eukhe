//! Manual compaction on the durable Harness: the `compact` command admits a
//! `pi.compaction` task through [`Conversation::compact`] and answers the TS
//! `CompactionResult`; `abort_compaction` aborts every live compaction task
//! of the conversation. The `compaction_start`/`compaction_end` frames come
//! from the event translator (the task's `pi.live` status), not from here.

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_core::durable::HostDeps;
use eukhe_durable::entries::COMPACTION_ENTRY;
use eukhe_durable::harness::agent::resolve_settings;
use eukhe_durable::harness::compaction::{estimate_context, select_cut};
use eukhe_durable::harness::types::{CompactionResult, ContextView};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness, LiveState, LIVE_DOC};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::SubmissionState;
use eukhe_durable::types::{
    DocumentReaderExt, EntryId, EntryRecord, TaskId, TaskOutcome, WriteSubmission,
};
use serde_json::{json, Value};

use crate::worker::durable_host::wire_messages::compaction_summary_text;

/// The skip of a session with no history before the keep window (TS
/// `CompactionSkippedError`).
pub(crate) const TOO_SHORT_TO_COMPACT: &str =
    "Session is too short to compact -- try again once it grows";
/// The skip of a context that already starts at its compaction summary.
pub(crate) const ALREADY_COMPACTED: &str = "Already compacted";
/// The skip of a chat-memory root (the old `CompactSkip::ChatMemory`).
pub(crate) const CHAT_MEMORY_SKIP: &str =
    "Nothing to compact: the chat memory keeps this chat, and every turn starts fresh from its view";
/// The error of an aborted manual compaction (TS `compact()` abort arm).
pub(crate) const COMPACTION_CANCELLED: &str = "Compaction cancelled";

/// Why a manual compaction produced no summary.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum ManualCompactionError {
    /// Nothing to compact; the TS skip message.
    #[error("{0}")]
    Skipped(&'static str),
    /// `abort_compaction` (or a conversation abort) ended the task.
    #[error("{COMPACTION_CANCELLED}")]
    Aborted,
    /// The summarizer or the Harness failed.
    #[error("{0}")]
    Failed(String),
}

impl ManualCompactionError {
    fn session(error: &SessionError) -> Self {
        Self::Failed(error.to_string())
    }
}

/// The client-facing `CompactionResult` (TS `_performCompaction`'s return)
/// of a `pi.compaction` entry: summary, the first kept entry, and the
/// context estimate before the compaction. Durable entries carry no file-op
/// `details`, so the key is absent (TS's `undefined`).
pub(crate) fn compaction_result_value(entry: &EntryRecord, tokens_before: u64) -> Value {
    json!({
        "summary": compaction_summary_text(entry),
        "firstKeptEntryId": entry.head.map_or_else(String::new, |head| head.to_string()),
        "tokensBefore": tokens_before,
    })
}

/// Whether the newest entry of the context is its compaction summary (TS
/// `prepareCompaction`: the last entry is a compaction). The kept tail the
/// summary retains was appended before it, so only an entry appended after
/// the summary makes the context compactable again.
fn already_compacted(view: &ContextView) -> bool {
    view.head.as_ref().is_some_and(|head| {
        COMPACTION_ENTRY.is(Some(head)) && view.entries.iter().all(|entry| entry.id <= head.id)
    })
}

/// Run one manual compaction of `conversation` and answer its TS
/// `CompactionResult`. The task summarizes while the conversation keeps
/// working; its summary is placed at once when idle, otherwise at the next
/// boundary, and this resolves once the summary entry exists.
///
/// # Errors
///
/// [`ManualCompactionError::Skipped`] when there is nothing to compact,
/// `Aborted` when the task was aborted, `Failed` otherwise.
pub(crate) async fn run_manual_compaction(
    harness: &Harness,
    deps: &HostDeps,
    conversation: &Conversation,
    instructions: Option<String>,
    cx: &Context,
) -> Result<Value, ManualCompactionError> {
    let view = conversation
        .context(cx, eukhe_durable::harness::types::ContextOptions::default())
        .await
        .map_err(|error| ManualCompactionError::session(&error))?;
    // A chat-memory root between calls: its next turn starts fresh from
    // the view, so there is no carried context to compact (the old
    // engine's `CompactSkip::ChatMemory`).
    if eukhe_core::durable::compaction::chat_memory_root(deps, conversation.id(), cx)
        .await
        .unwrap_or(false)
    {
        return Err(ManualCompactionError::Skipped(CHAT_MEMORY_SKIP));
    }
    if already_compacted(&view) {
        return Err(ManualCompactionError::Skipped(ALREADY_COMPACTED));
    }
    let keep_recent = resolve_settings(Some(&deps.settings.harness()))
        .compaction
        .keep_recent_tokens;
    if select_cut(&view, keep_recent).is_none() {
        return Err(ManualCompactionError::Skipped(TOO_SHORT_TO_COMPACT));
    }
    let task = conversation
        .compact(instructions, cx)
        .await
        .map_err(|error| ManualCompactionError::session(&error))?;
    // The context estimate before the summary (TS `tokensBefore`), over the
    // view read above: computed after the task commit, so the
    // `compaction_start` frame never waits on it.
    let tokens_before = estimate_context(&view, &[]);
    let settled = harness
        .wait_for_task(task, cx)
        .await
        .map_err(|error| ManualCompactionError::session(&error))?;
    let result: CompactionResult = match settled.outcome {
        TaskOutcome::Completed { result } => {
            from_json(&result).map_err(|error| ManualCompactionError::Failed(error.to_string()))?
        }
        TaskOutcome::Aborted { .. } => return Err(ManualCompactionError::Aborted),
        TaskOutcome::Failed { error, .. } | TaskOutcome::Faulted { error } => {
            return Err(ManualCompactionError::Failed(error.message));
        }
        TaskOutcome::Orphaned { reason } => return Err(ManualCompactionError::Failed(reason)),
    };
    let entry_id = summary_entry_id(harness, &result, cx).await?;
    let Some(entry_id) = entry_id else {
        // The summarizer declined (an extension hook) or the summary went
        // stale before it could be placed.
        return Err(ManualCompactionError::Skipped(ALREADY_COMPACTED));
    };
    let entry = read_entry(conversation, entry_id, cx)
        .await
        .map_err(|error| ManualCompactionError::session(&error))?
        .ok_or_else(|| {
            ManualCompactionError::Failed(format!("compaction entry {entry_id} is missing"))
        })?;
    Ok(compaction_result_value(&entry, tokens_before))
}

/// The summary entry of a completed compaction: appended directly, or
/// placed through its write submission (waited for here).
async fn summary_entry_id(
    harness: &Harness,
    result: &CompactionResult,
    cx: &Context,
) -> Result<Option<EntryId>, ManualCompactionError> {
    if let Some(entry_id) = result.entry_id {
        return Ok(Some(entry_id));
    }
    let Some(submission_id) = result.submission_id else {
        return Ok(None);
    };
    let handle = harness
        .submission(submission_id, cx)
        .await
        .map_err(|error| ManualCompactionError::session(&error))?
        .ok_or_else(|| {
            ManualCompactionError::Failed(format!(
                "compaction submission {submission_id} is missing"
            ))
        })?;
    let settled = handle
        .wait(cx)
        .await
        .map_err(|error| ManualCompactionError::session(&error))?;
    match &settled.record().state {
        SubmissionState::Write(WriteSubmission::Done { entry }) => Ok(Some(*entry)),
        SubmissionState::Write(WriteSubmission::Unanswered { .. }) => Ok(None),
        SubmissionState::Write(WriteSubmission::Queued) | SubmissionState::Input(_) => {
            Err(ManualCompactionError::Failed(format!(
                "compaction submission {submission_id} settled without an entry"
            )))
        }
    }
}

/// One entry of `conversation` by id.
pub(crate) async fn read_entry(
    conversation: &Conversation,
    id: EntryId,
    cx: &Context,
) -> SessionResult<Option<EntryRecord>> {
    let page = conversation
        .entries(
            ConversationEntryQuery {
                min_entry_id: Some(id),
                max_entry_id: Some(id),
                order: None,
            },
            1,
            None,
            cx,
        )
        .await?;
    Ok(page.items.into_iter().find(|entry| entry.id == id))
}

/// `abort_compaction`: abort every live compaction task of `conversation`
/// (the manual run and the automatic threshold/overflow runs alike). Answers
/// the aborted tasks; none live is a success (the TS handler always replies
/// success).
///
/// # Errors
///
/// The `pi.live` read or an abort fails.
pub(crate) async fn abort_compactions(
    harness: &Harness,
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<Vec<TaskId>> {
    let live: LiveState = match harness.snapshot(&LIVE_DOC, conversation.id(), cx).await? {
        Some(value) => from_json(&JsonValue::Object(value))?,
        None => LiveState::default(),
    };
    let tasks: Vec<TaskId> = live
        .compactions
        .unwrap_or_default()
        .iter()
        .map(|status| status.task_id)
        .collect();
    for task in &tasks {
        harness.abort_task(*task, cx).await?;
    }
    Ok(tasks)
}

#[cfg(test)]
mod tests;
