//! Print mode's end of a prompt: the turn ending is not the run ending. A
//! session that still owns running jobs, subagents or workflow runs (or a
//! settle notice being admitted) wakes into another turn when they settle,
//! so print mode waits until the session is quiescent or the stated limit
//! (`--wait-limit-ms`) elapses; the compiled Bend core decides
//! (`headless_settle`, laws `laws/headless.bend`). The run watch also keeps
//! the inputs of the last run that ended, whose settlement is the exit code
//! fact of `headless_exit`.

use std::pin::pin;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_bend::rules::headless::{settle, RunEnd, Settle, SettleFacts, Unanswered};
use eukhe_chord::context::Context;
use eukhe_core::durable::pending::{pending_work, PendingWork};
use eukhe_durable::harness::{watch_events, AgentEvent, AgentEventStream, Conversation};
use eukhe_durable::session::SessionError;
use eukhe_durable::types::SubmissionId;
use futures::FutureExt;
use tokio::sync::Notify;

use crate::headless_session::HeadlessSession;

/// Why the wait or the run read failed.
#[derive(Debug, thiserror::Error)]
pub(crate) enum HeadlessWaitError {
    /// A session operation (the event watch, the idle wait, a submission
    /// read) failed.
    #[error("{0:#}")]
    Session(#[from] SessionError),
    /// The compiled core refused the facts (an inconsistent build).
    #[error("{0}")]
    Core(#[from] eukhe_bend::Error),
}

/// How the wait for quiescence ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Settled {
    /// Nothing runs that could wake the session.
    Quiescent,
    /// The limit elapsed while this still ran.
    GaveUp(PendingWork),
}

/// What the run watch saw.
#[derive(Default)]
struct Seen {
    /// Fired on every committed event batch of the main conversation.
    changed: Notify,
    /// The inputs of the last run that ended; `None` before any run ended.
    last_run: Mutex<Option<Vec<SubmissionId>>>,
}

/// The main conversation's events: a change signal for the wait, and the
/// inputs of the last run that ended.
pub(crate) struct RunWatch {
    stream: AgentEventStream,
    seen: Arc<Seen>,
}

impl RunWatch {
    /// Watch `conversation` from now on.
    ///
    /// # Errors
    ///
    /// The watch cannot start.
    pub(crate) async fn start(
        opened: &HeadlessSession,
        conversation: &Conversation,
        cx: &Context,
    ) -> Result<Self, HeadlessWaitError> {
        let stream = watch_events(opened.session.harness(), conversation.id(), cx).await?;
        let seen = Arc::new(Seen::default());
        let listener = Arc::clone(&seen);
        stream.start(Arc::new(move |batch, _cx| {
            let ended = batch.iter().rev().find_map(|event| {
                if let AgentEvent::RunEnd { inputs } = event {
                    Some(inputs.clone())
                } else {
                    None
                }
            });
            if let Some(inputs) = ended {
                *listener
                    .last_run
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner) = Some(inputs);
            }
            listener.changed.notify_waiters();
            futures::future::ready(Ok(())).boxed()
        }))?;
        Ok(Self { stream, seen })
    }

    /// Deliver every committed batch, then stop.
    pub(crate) async fn finish(self) {
        self.stream.delivered().await;
        self.stream.stop().await;
    }

    /// The last run's settlement: its last input's (every input of a run
    /// settles alike), with the unanswered detail; `NoRun` before any run
    /// ended or for a run without inputs.
    ///
    /// # Errors
    ///
    /// A submission read failure.
    pub(crate) async fn last_run(
        &self,
        opened: &HeadlessSession,
        cx: &Context,
    ) -> Result<(RunEnd, Option<String>), HeadlessWaitError> {
        self.stream.delivered().await;
        let last = self
            .seen
            .last_run
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .as_ref()
            .and_then(|inputs| inputs.last().copied());
        let Some(id) = last else {
            return Ok((RunEnd::NoRun, None));
        };
        let Some(handle) = opened.session.harness().submission(id, cx).await? else {
            return Ok((RunEnd::NoRun, None));
        };
        let state = handle.status(cx).await?.state;
        let detail = state
            .detail()
            .and_then(eukhe_chord::json::JsonValue::as_str)
            .filter(|detail| !detail.is_empty())
            .map(str::to_owned);
        Ok(match state.reason() {
            Some(reason) => (
                RunEnd::Unanswered(Unanswered::from_reason(reason)),
                detail.or_else(|| Some(reason.to_owned())),
            ),
            None if state.is_settled() => (RunEnd::Answered, None),
            // A run that ended with its input still unsettled ended
            // abnormally.
            None => (
                RunEnd::Unanswered(Unanswered::Other),
                Some(format!(
                    "the run ended with its input still {:?}",
                    state.status()
                )),
            ),
        })
    }
}

/// Wait until the session is quiescent: the main conversation idle with
/// no queued input, no running job, kernel command, subagent or workflow
/// run, and no settle notice being admitted; or until `limit` elapses.
/// Every woken turn runs inside the wait.
///
/// The facts are read in the order that never misses a wake: the pending
/// work, then the notices in flight, then the conversation's idleness (a
/// settle notice enters the in-flight count before its job reads ended,
/// and leaves it only once admitted).
///
/// # Errors
///
/// An idle wait failure (a closed session, a cancelled `cx`), or the
/// compiled core's refusal.
pub(crate) async fn wait_quiescent(
    opened: &HeadlessSession,
    watch: &RunWatch,
    limit: Duration,
    cx: &Context,
) -> Result<Settled, HeadlessWaitError> {
    let deadline = tokio::time::Instant::now() + limit;
    let conversation = opened.session.main();
    let deps = opened.session.deps();
    let harness = opened.session.harness();
    loop {
        let mut events = pin!(watch.seen.changed.notified());
        events.as_mut().enable();
        let mut wakes = pin!(opened.wakes.changed());
        wakes.as_mut().enable();
        conversation.wait_for_idle(cx).await?;
        let (work, unknown) = match pending_work(deps, harness, conversation.id(), cx).await {
            Ok(work) => (work, false),
            Err(error) => {
                // Unknown never reads idle: the wait goes on (to the limit
                // if the read keeps failing).
                tracing::warn!(%error, "print mode cannot read the session's pending work");
                (PendingWork::default(), true)
            }
        };
        let in_flight = opened.wakes.in_flight();
        let busy = match conversation.wait_for_idle(cx).now_or_never() {
            Some(idle) => {
                idle?;
                false
            }
            None => true,
        };
        let limit_hit = tokio::time::Instant::now() >= deadline;
        let count = |n: usize| u64::try_from(n).unwrap_or(u64::MAX);
        let decision = settle(&SettleFacts {
            busy,
            // A held result is a job whose end no notice took yet.
            jobs: count(work.jobs.len() + usize::from(work.held_results)),
            kernel_jobs: count(work.kernel_jobs),
            children: count(work.children),
            workflow_runs: count(work.workflow_runs),
            wakes: count(in_flight),
            unknown,
            limit_hit,
        })?;
        match decision {
            Settle::Done => return Ok(Settled::Quiescent),
            Settle::GiveUp => return Ok(Settled::GaveUp(work)),
            Settle::Wait if busy => {}
            Settle::Wait => {
                tokio::select! {
                    () = events => {}
                    () = wakes => {}
                    () = tokio::time::sleep_until(deadline) => {}
                }
            }
        }
    }
}

/// What a give-up still waited on, for the stderr line.
pub(crate) fn still_running(work: &PendingWork) -> String {
    let mut parts: Vec<String> = work
        .jobs
        .iter()
        .map(|job| format!("job {} ({})", job.id, job.label))
        .collect();
    let mut counted = |count: usize, one: &str, many: &str| {
        if count > 0 {
            parts.push(format!("{count} {}", if count == 1 { one } else { many }));
        }
    };
    counted(
        work.kernel_jobs,
        "kernel bash command",
        "kernel bash commands",
    );
    counted(work.children, "subagent", "subagents");
    counted(work.workflow_runs, "workflow run", "workflow runs");
    if parts.is_empty() {
        "work the session could not read".to_owned()
    } else {
        parts.join(", ")
    }
}
