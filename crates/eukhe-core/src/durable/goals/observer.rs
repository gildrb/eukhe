//! The goal's run-end failure: an active goal whose conversation's run ends
//! on a terminal provider failure finishes as `error` right away (the old
//! engine's `finish_for_terminal_message` on the errored turn; TS fails the
//! goal on it too), so the goal watch announces the terminal state at once
//! instead of at the next generation's `before_request` settle.
//!
//! A post-commit observer watches for the commit that ends a run on a
//! failed model call: it appends the failed assistant entry and settles the
//! run's inputs `unanswered` with `model_error` (a retried attempt keeps the
//! run, an abort settles otherwise). The goal write is one commit through
//! [`failed`]/[`stamp`], a no-op unless the goal is still active — so a
//! replay, or the hooks' own lazy settle, never writes twice.

use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{CommitChange, CommitPublication, ConversationId};
use eukhe_types::pi_ai::Message;
use futures::FutureExt;

use super::docs::{open_doc, read_doc, write_doc, GOAL_DOC};
use super::state::{failed, stamp, terminal_provider_failure};
use crate::autonomous::now_millis;
use crate::durable::{HostDeps, OpenedSession, ServiceStop};
use crate::goals::GoalStatus;

/// The settle reason of a run that ended on a failed model call.
const MODEL_ERROR: &str = "model_error";

/// One run that ended on a terminal provider failure.
struct FailedRun {
    conversation_id: ConversationId,
    error: String,
}

/// Start the observer when the session opens.
pub(super) fn install(deps: &Arc<HostDeps>) {
    deps.add_service(Box::new(start));
}

fn start(
    opened: OpenedSession,
) -> futures::future::BoxFuture<'static, SessionResult<Option<ServiceStop>>> {
    async move {
        let (events, mut event_rx) = tokio::sync::mpsc::unbounded_channel::<FailedRun>();
        let commits = opened.harness.subscribe_commits(Arc::new(
            move |publication: &CommitPublication, _cx: &Context| {
                if let Some(run) = failed_run(publication) {
                    let _ = events.send(run);
                }
            },
        ))?;
        let close = Arc::new(tokio::sync::Notify::new());
        let close_signal = Arc::clone(&close);
        let subscription = opened.harness.subscribe_close(Arc::new(move || {
            close_signal.notify_one();
        }))?;
        let harness = opened.harness.clone();
        let task_close = Arc::clone(&close);
        let task = tokio::spawn(async move {
            loop {
                tokio::select! {
                    run = event_rx.recv() => {
                        let Some(run) = run else { break };
                        fail_goal(&harness, run).await;
                    }
                    () = task_close.notified() => {
                        while let Ok(run) = event_rx.try_recv() {
                            fail_goal(&harness, run).await;
                        }
                        break;
                    }
                }
            }
        });
        let stop: ServiceStop = Box::new(move || {
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

/// The run a commit ended on a terminal provider failure: a failed
/// assistant entry together with the run's `model_error` settle.
fn failed_run(publication: &CommitPublication) -> Option<FailedRun> {
    let settles_model_error = publication.changes.iter().any(|change| {
        matches!(change, CommitChange::Submission(record)
            if record.state.reason() == Some(MODEL_ERROR))
    });
    if !settles_model_error {
        return None;
    }
    publication.changes.iter().find_map(|change| {
        let CommitChange::Entry(entry) = change else {
            return None;
        };
        if entry.kind != ASSISTANT_ENTRY.kind() {
            return None;
        }
        let Some(Message::Assistant(message)) = entry.model.as_deref()?.first() else {
            return None;
        };
        terminal_provider_failure(message).map(|error| FailedRun {
            conversation_id: entry.conversation_id,
            error,
        })
    })
}

/// Fail the conversation's goal when it is still active; a failure is
/// logged (the lazy `before_request` settle still covers the goal).
async fn fail_goal(harness: &Harness, run: FailedRun) {
    let cx = BACKGROUND_CONTEXT.clone();
    let handled = async {
        let FailedRun {
            conversation_id,
            error,
        } = run;
        let active = read_doc(harness, &GOAL_DOC, conversation_id, &cx)
            .await?
            .is_some_and(|goal| goal.status == GoalStatus::Active);
        if !active {
            return Ok(());
        }
        let Some(conversation) = harness.conversation(conversation_id, &cx).await? else {
            return Ok(());
        };
        conversation
            .commit(
                move |tx| async move {
                    let (draft, goal) = open_doc(&tx, &GOAL_DOC, conversation_id).await?;
                    if let Some(next) = failed(&goal, Some(&error)) {
                        write_doc(&draft, &stamp(next, now_millis()))?;
                    }
                    Ok(())
                },
                &cx,
            )
            .await
    };
    let result: SessionResult<()> = handled.await;
    if let Err(error) = result {
        tracing::warn!(target: "eukhe.goals", "goal failure on the errored run failed: {error}");
    }
}
