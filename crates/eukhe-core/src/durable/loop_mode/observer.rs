//! The loop's run-end observer: a run that ends without a final answer
//! never reaches `on_yield`, so a post-commit observer tells the loop.
//!
//! - An aborted run (the user's interrupt, or any other abort of the
//!   session) is the loop's interrupt: the loop pauses. The abort a manual
//!   compaction makes is not one: the compaction holds the loop first
//!   ([`super::hold_loop_for_compaction`]) and sends the cut turn again;
//!   the cut turn's end, seen after the compaction already released the
//!   loop, is known by its request id and still no interrupt.
//! - A run that failed (a terminal provider failure, no model, a fault,
//!   the run limit) is a failed turn: the compiled core counts it and, under
//!   the cap of failed turns in a row, the loop goes on (the check, then
//!   the next iteration as a submission).
//!
//! At open the observer takes up a loop whose pending work nothing carries
//! any more (a worker that died between the state and the submission of an
//! iteration, or in the condition command of a failed turn).

use std::sync::Arc;

use eukhe_bend::rules::loop_mode::TurnOutcome;
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::{Harness, LIVE_DOC};
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{CommitChange, CommitPublication, ConversationId};
use eukhe_types::loop_mode::LoopPhase;
use futures::FutureExt;

use super::docs::{LoopDoc, LOOP_MODE_DOC};
use super::drive::{turn_request_id, Input, LoopHost, Mode};
use crate::durable::autonomous::read_doc;
use crate::durable::{HostDeps, OpenedSession, ServiceStop};

/// One run that ended without an answer.
struct EndedRun {
    conversation_id: ConversationId,
    aborted: bool,
    /// The request ids of the inputs it settled unanswered.
    request_ids: Vec<String>,
}

/// Whether an unanswered submission's reason is an abort (aborted, reset,
/// stale: the turn did not run to its end) and not a failed run.
fn aborted(reason: &str) -> bool {
    match reason {
        "model_error" | "no_model" | "faulted" | "run_limit" | "forced_tool" => false,
        // "aborted", "reset", "stale" and any reason added later.
        _ => true,
    }
}

/// The run a commit ended without an answer: its inputs settle unanswered
/// in the commit that removes the live run.
fn ended_run(publication: &CommitPublication) -> Option<EndedRun> {
    let mut unanswered = publication.changes.iter().filter_map(|change| {
        let CommitChange::Submission(record) = change else {
            return None;
        };
        let reason = record.state.reason()?;
        Some((record, reason))
    });
    let (first, reason) = unanswered.next()?;
    let request_ids = std::iter::once(first)
        .chain(unanswered.map(|(record, _)| record))
        .filter_map(|record| record.request_id.clone())
        .collect();
    Some(EndedRun {
        conversation_id: first.conversation_id,
        aborted: aborted(reason),
        request_ids,
    })
}

/// Start the observer when the session opens.
pub(super) fn install(deps: &Arc<HostDeps>, host: &LoopHost) {
    let host = host.clone();
    deps.add_service(Box::new(move |opened| start(opened, host)));
}

fn start(
    opened: OpenedSession,
    host: LoopHost,
) -> futures::future::BoxFuture<'static, SessionResult<Option<ServiceStop>>> {
    async move {
        let (events, mut event_rx) = tokio::sync::mpsc::unbounded_channel::<EndedRun>();
        let commits = opened.harness.subscribe_commits(Arc::new(
            move |publication: &CommitPublication, _cx: &Context| {
                if let Some(run) = ended_run(publication) {
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
        let main = opened.main.id();
        let task_close = Arc::clone(&close);
        let task = tokio::spawn(async move {
            take_up(&host, &harness, main).await;
            loop {
                tokio::select! {
                    run = event_rx.recv() => {
                        let Some(run) = run else { break };
                        run_ended(&host, &harness, run).await;
                    }
                    () = task_close.notified() => break,
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

/// The loop of `conversation_id` when it has pending work and nothing
/// runs.
async fn stranded(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Option<LoopDoc>> {
    let Some(doc) = read_doc(harness, &LOOP_MODE_DOC, conversation_id, cx).await? else {
        return Ok(None);
    };
    if !matches!(doc.state.phase, LoopPhase::Turn | LoopPhase::Judging) {
        return Ok(None);
    }
    let running = read_doc(harness, &LIVE_DOC, conversation_id, cx)
        .await?
        .is_some_and(|live| live.run.is_some());
    Ok((!running).then_some(doc))
}

/// Whether `run` was a send of `doc`'s current turn that a compaction cut:
/// the compaction sent the turn again under a later request id, so a run
/// with an earlier one ended before it (its end may reach the observer
/// after the compaction released the loop, the new send still queued).
fn cut_turn(doc: &LoopDoc, run: &EndedRun) -> bool {
    (0..doc.resends).any(|resends| {
        let cut = turn_request_id(doc, doc.state.iteration, resends);
        run.request_ids.contains(&cut)
    })
}

/// Tell the loop that a run ended without an answer; a failure is logged
/// (the loop stays as it is, visible in its status).
async fn run_ended(host: &LoopHost, harness: &Harness, run: EndedRun) {
    let cx = BACKGROUND_CONTEXT.clone();
    let handled = async {
        // A withdrawn queued input ends no run: the loop's turn still runs.
        let Some(doc) = stranded(harness, run.conversation_id, &cx).await? else {
            return Ok(());
        };
        let conversation = host.conversation(run.conversation_id, &cx).await?;
        let input = match (run.aborted, doc.held || cut_turn(&doc, &run)) {
            // The compaction that cut the turn sends it again.
            (true, true) => return Ok(()),
            (true, false) => Input::Abort,
            (false, _) => Input::TurnSettled(TurnOutcome::Errored),
        };
        host.drive(&conversation, input, Mode::Idle, None, &cx)
            .await?;
        Ok(())
    };
    let result: SessionResult<()> = handled.await;
    if let Err(error) = result {
        tracing::warn!(target: "eukhe.loop", "the loop's run-end step failed: {error}");
    }
}

/// At open: a loop with pending work that nothing carries takes it up (the
/// core's `Restart`): a check runs again; a turn whose prompt never was
/// sent is sent; a turn that is over pauses the loop.
async fn take_up(host: &LoopHost, harness: &Harness, conversation_id: ConversationId) {
    let cx = BACKGROUND_CONTEXT.clone();
    let handled = async {
        if stranded(harness, conversation_id, &cx).await?.is_none() {
            return Ok(());
        }
        let conversation = host.conversation(conversation_id, &cx).await?;
        host.drive(&conversation, Input::TakeUp, Mode::Idle, None, &cx)
            .await?;
        Ok(())
    };
    let result: SessionResult<()> = handled.await;
    if let Err(error) = result {
        tracing::warn!(target: "eukhe.loop", "taking the loop up at open failed: {error}");
    }
}

#[cfg(test)]
mod tests {
    use eukhe_durable::types::ROOT_CONVERSATION_ID;

    use super::{cut_turn, EndedRun, LoopDoc};

    fn ended(request_ids: &[&str]) -> EndedRun {
        EndedRun {
            conversation_id: ROOT_CONVERSATION_ID,
            aborted: true,
            request_ids: request_ids.iter().map(|id| (*id).to_owned()).collect(),
        }
    }

    /// After a compaction sent iteration 2 again (one resend), the end of
    /// its first send is the cut turn's; the end of the resend, of another
    /// iteration or of the user's own input is not.
    #[test]
    fn a_cut_turn_is_known_by_an_earlier_request_id() {
        let mut doc = LoopDoc {
            loop_id: Some("a1".to_owned()),
            resends: 1,
            ..LoopDoc::default()
        };
        doc.state.iteration = 2;
        assert!(cut_turn(&doc, &ended(&["loop:a1:2"])));
        assert!(cut_turn(&doc, &ended(&["user", "loop:a1:2"])));
        assert!(!cut_turn(&doc, &ended(&["loop:a1:2:1"])));
        assert!(!cut_turn(&doc, &ended(&["loop:a1:1"])));
        assert!(!cut_turn(&doc, &ended(&["loop:b2:2"])));
        assert!(!cut_turn(&doc, &ended(&[])));
        doc.resends = 0;
        assert!(!cut_turn(&doc, &ended(&["loop:a1:2"])));
    }
}
