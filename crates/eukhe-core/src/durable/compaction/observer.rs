//! The `eukhe.compaction` post-commit observer: watches `pi.compaction`
//! task records settle and, per task (idempotent by task id, recorded in
//! the conversation's `eukhe.compaction.outcomes` document in the same
//! commit as the row):
//!
//! - a settled **threshold/overflow** compaction that failed, was aborted,
//!   or produced no summary appends the durable `compaction_outcome`
//!   disclosure row (the old engine's `_persistCompactionOutcome`; manual
//!   compactions stay excluded — the old `compact()` reports on the event
//!   only);
//! - a compaction that produced a summary gets the post-compaction
//!   `ipython_state` notice when a kernel survived it (the old engine's
//!   `_syncKernelStateAfterCompaction`), a model-context row that also
//!   keeps a back-to-back second `/compact` preparing in update mode
//!   instead of skipping as already compacted;
//! - and it arms the compact-trigger auto-refine (the old
//!   `_scheduleAutoRefineAfterCompaction`), serviced once the conversation
//!   is idle.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::harness::types::{SubmissionDraft, WriteSubmissionDraft};
use eukhe_durable::harness::Conversation;
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{
    CommitChange, CommitPublication, ConversationId, LatestFork, TaskOutcome, TaskRecord,
};
use eukhe_types::session::CustomMessage;
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::super::{custom_entry_draft, OpenedSession};
use super::{CompactionRuntime, HostDeps, COMPACTION_ENTRY_KIND};
use crate::session_engine::messages::{CompactionOutcomeKind, CompactionOutcomeReason};

static OUTCOMES_DOC: ConversationDoc<OutcomesState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.compaction.outcomes",
        version: 1,
        initial: OutcomesState::default,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.compaction.outcomes has a valid version"),
};

/// The task ids whose settle already produced its outcome row, `true`.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct OutcomesState {
    /// The task ids whose settle already produced its outcome row.
    pub recorded: HashMap<String, bool>,
}

/// One settled compaction the observer services.
struct Settled {
    conversation_id: ConversationId,
    /// The task's durable id (its idempotency key).
    task_id: String,
    reason: CompactionOutcomeReason,
    outcome: SettledOutcome,
}

/// How the task settled.
enum SettledOutcome {
    /// A summary was placed (entry or submission): the follow-ups run.
    Summarized,
    /// Completed without a summary.
    Skipped,
    /// Failed with `message`.
    Failed(String),
    /// Aborted by the user.
    Aborted,
}

/// Start the observer on the opened session; the stop unsubscribes and
/// ends the service task.
pub(crate) fn start(
    runtime: Arc<CompactionRuntime>,
    opened: OpenedSession,
) -> futures::future::BoxFuture<'static, SessionResult<Option<super::super::ServiceStop>>> {
    async move {
        let (events, mut event_rx) = tokio::sync::mpsc::unbounded_channel::<Settled>();
        let listener_seen: Arc<Mutex<Vec<String>>> = Arc::default();
        let listener_events = events;
        let listener_runtime = Arc::clone(&runtime);
        let commits = opened.harness.subscribe_commits(Arc::new(
            move |publication: &CommitPublication, _cx: &Context| {
                for change in &publication.changes {
                    match change {
                        CommitChange::Task(record) => {
                            if let Some(settled) = settle_of(record, &listener_seen) {
                                let _ = listener_events.send(settled);
                            }
                        }
                        // One settled assistant turn appended: the review
                        // prompt's trigger counter (the old engine's
                        // `message_end` increment).
                        CommitChange::Entry(entry) if entry.kind == "pi.assistant" => {
                            listener_runtime.autorefine.note_settled_turn();
                        }
                        _ => {}
                    }
                }
            },
        ))?;
        let close = Arc::new(tokio::sync::Notify::new());
        let close_signal = Arc::clone(&close);
        // `notify_one` stores a permit for the next waiter, so a close fired
        // before the service task first polls (nothing else parks between the
        // service start and the stop) still ends it, like a TS promise.
        let subscription = opened.harness.subscribe_close(Arc::new(move || {
            close_signal.notify_one();
        }))?;
        let service_runtime = Arc::clone(&runtime);
        let task_close = Arc::clone(&close);
        let task = tokio::spawn(async move {
            loop {
                tokio::select! {
                    event = event_rx.recv() => {
                        let Some(event) = event else { break };
                        if let Err(error) = handle(&service_runtime, event).await {
                            tracing::warn!(target: "eukhe.compaction", "compaction settle handling failed: {error:#}");
                        }
                    }
                    () = task_close.notified() => break,
                }
            }
        });
        let stop: super::super::ServiceStop = Box::new(move || {
            async move {
                drop(commits);
                drop(subscription);
                close.notify_one();
                let _ = task.await;
            }
            .boxed()
        });
        Ok(Some(stop))
    }
    .boxed()
}

/// The settle of one task record, when it is a terminal `pi.compaction`
/// whose id the observer has not serviced yet.
fn settle_of(record: &TaskRecord, seen: &Mutex<Vec<String>>) -> Option<Settled> {
    if record.kind != super::COMPACTION_ENTRY_KIND {
        return None;
    }
    let task_id = record.id.to_string();
    {
        let mut seen = seen.lock().unwrap_or_else(PoisonError::into_inner);
        if seen.contains(&task_id) {
            return None;
        }
        seen.push(task_id.clone());
    }
    let input: Value = serde_json::from_str(&record.input.to_string()).ok()?;
    let reason = match input.get("reason").and_then(Value::as_str) {
        Some("threshold") => CompactionOutcomeReason::Threshold,
        Some("overflow") => CompactionOutcomeReason::Overflow,
        // Manual compactions report on the event only (the old `compact()`).
        _ => return None,
    };
    let eukhe_durable::types::TaskState::Terminal { outcome } = &record.state else {
        return None;
    };
    let outcome = match outcome {
        TaskOutcome::Completed { result } => {
            let placed = serde_json::from_str::<Value>(&result.to_string())
                .ok()
                .and_then(|result| {
                    result.as_object().map(|fields| {
                        fields.contains_key("entryId") || fields.contains_key("submissionId")
                    })
                })
                .unwrap_or(false);
            if placed {
                SettledOutcome::Summarized
            } else {
                SettledOutcome::Skipped
            }
        }
        // A faulted task (an uncaught throw, e.g. a hook error) is a
        // failed compaction to the user.
        TaskOutcome::Failed { error, .. } | TaskOutcome::Faulted { error } => {
            SettledOutcome::Failed(error.message.clone())
        }
        TaskOutcome::Aborted { .. } => SettledOutcome::Aborted,
        // An orphaned compaction (its definition unavailable) never
        // settles through this observer.
        TaskOutcome::Orphaned { .. } => return None,
    };
    Some(Settled {
        conversation_id: record.conversation_id,
        task_id,
        reason,
        outcome,
    })
}

/// Service one settled compaction: the outcome row, the kernel notice,
/// and the auto-refine arming.
async fn handle(runtime: &Arc<CompactionRuntime>, event: Settled) -> anyhow::Result<()> {
    let deps = &runtime.deps;
    let harness = deps
        .harness
        .get()
        .ok_or_else(|| anyhow::anyhow!("the session is closed"))?;
    let cx = BACKGROUND_CONTEXT.clone();
    let Some(conversation) = harness.conversation(event.conversation_id, &cx).await? else {
        return Ok(());
    };
    match event.outcome {
        SettledOutcome::Summarized => {
            // The kernel survived the compaction: its persistence notice
            // (the old `_syncKernelStateAfterCompaction`) lands first.
            // The compact-trigger review arms (TS
            // `_scheduleAutoRefineAfterCompaction`); the spawned task
            // consumes it once the conversation is idle.
            notice_surviving_kernel(deps, &conversation, &cx).await;
            runtime.autorefine.arm();
            let arming = Arc::clone(runtime);
            let idle_conversation = conversation.clone();
            let idle_cx = cx.clone();
            tokio::spawn(async move {
                if idle_conversation.wait_for_idle(&idle_cx).await.is_ok() {
                    if let Err(error) =
                        super::autorefine::consume(&arming, &idle_conversation, &idle_cx).await
                    {
                        tracing::warn!(target: "eukhe.compaction", "compact auto-refine failed: {error:#}");
                    }
                }
            });
        }
        SettledOutcome::Skipped => {
            let message = skip_message(deps, &conversation, &cx).await;
            outcome_row(
                &conversation,
                &event.task_id,
                super::summary::outcome_message(
                    &format!("Auto-compaction skipped: {message}"),
                    event.reason,
                    CompactionOutcomeKind::Skipped,
                ),
                &cx,
            )
            .await?;
        }
        SettledOutcome::Failed(message) => {
            outcome_row(
                &conversation,
                &event.task_id,
                super::summary::outcome_message(
                    &format!("Auto-compaction failed: {message}"),
                    event.reason,
                    CompactionOutcomeKind::Failed,
                ),
                &cx,
            )
            .await?;
        }
        SettledOutcome::Aborted => {
            outcome_row(
                &conversation,
                &event.task_id,
                super::summary::outcome_message(
                    "Compaction cancelled",
                    event.reason,
                    CompactionOutcomeKind::Cancelled,
                ),
                &cx,
            )
            .await?;
        }
    }
    Ok(())
}

/// The skip message of a compaction that completed without a summary: the
/// chat-memory decline, the already-compacted head, or nothing to
/// summarize (the old engine's `CompactSkip::user_message` texts).
async fn skip_message(deps: &HostDeps, conversation: &Conversation, cx: &Context) -> String {
    if super::summary::chat_memory_root_of(deps, conversation.id(), cx)
        .await
        .unwrap_or(false)
    {
        return "Nothing to compact: the chat memory keeps this chat, and every turn starts fresh from its view".to_owned();
    }
    match conversation.context(cx).await {
        Ok(view) if matches!(view.entries.last(), Some(entry) if entry.kind == COMPACTION_ENTRY_KIND) => {
            "Already compacted".to_owned()
        }
        _ => "Session is too short to compact -- try again once it grows".to_owned(),
    }
}

/// Append the outcome row once per task id: the conversation's
/// `eukhe.compaction.outcomes` document records the task in the same
/// commit, so a crash between observe and append cannot double-write.
async fn outcome_row(
    conversation: &Conversation,
    task_id: &str,
    row: CustomMessage,
    cx: &Context,
) -> anyhow::Result<()> {
    let task_id = task_id.to_owned();
    let draft_entry = custom_entry_draft(
        row.custom_type.clone(),
        pi_user_content(&row.content)?,
        row.display,
        row.details.clone(),
        row.timestamp,
    )?;
    let conversation_id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                let draft = tx.doc(&OUTCOMES_DOC, conversation_id).await?;
                let mut state: OutcomesState = match draft.get("recorded")? {
                    Some(item) => eukhe_chord::json::from_json(&item.to_value()?)?,
                    None => OutcomesState::default(),
                };
                if state.recorded.remove(task_id.as_str()).is_some() {
                    // Already recorded: this settle is a replay.
                    return Ok(());
                }
                state.recorded.insert(task_id.clone(), true);
                draft.set(
                    "recorded",
                    eukhe_chord::json::to_json(&state)
                        .map_err(eukhe_durable::session::SessionError::other)?,
                )?;
                tx.append_entry(conversation_id, draft_entry).await?;
                Ok(())
            },
            cx,
        )
        .await?;
    Ok(())
}

/// Submit the post-compaction `ipython_state` notice when a kernel of the
/// conversation survived (a write submission: placed at once when idle,
/// otherwise at the next boundary — the old engine's row also landed
/// after the compaction commit).
async fn notice_surviving_kernel(deps: &HostDeps, conversation: &Conversation, cx: &Context) {
    let Some(pool) = deps.rlm_kernels.get().and_then(std::sync::Weak::upgrade) else {
        return;
    };
    let Some(kernel) = pool.existing(conversation.id()) else {
        return;
    };
    let Some(content) =
        crate::session_engine::ipython_state::capture_notice_content(&kernel.provisioner).await
    else {
        return;
    };
    let row = crate::session_engine::ipython_state::notice_message(content);
    let Some(content) = pi_user_content(&row.content).ok() else {
        return;
    };
    let Ok(draft) = custom_entry_draft(
        row.custom_type,
        content,
        row.display,
        row.details.clone(),
        row.timestamp,
    ) else {
        return;
    };
    if let Err(error) = conversation
        .submit(
            SubmissionDraft::Write(WriteSubmissionDraft {
                request_id: None,
                entry: draft,
            }),
            cx,
        )
        .await
    {
        tracing::warn!(target: "eukhe.compaction", "ipython_state notice not delivered: {error:#}");
    }
}

/// The pi wire shape of an old-engine user content (the two crates share
/// the camelCase wire form).
fn pi_user_content(
    content: &eukhe_types::ai::UserContent,
) -> anyhow::Result<eukhe_types::pi_ai::UserContent> {
    Ok(serde_json::from_value(serde_json::to_value(content)?)?)
}
