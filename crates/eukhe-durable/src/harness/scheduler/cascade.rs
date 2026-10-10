//! Aborts and cascades: direct and conversation aborts, the reconcile commit
//! that derives abort marks (spec §5.4), `failFast` marks and withdrawn
//! inputs (spec §5.5), finalization of held outcomes, and scheduler-written
//! outcomes.

use std::future::Future;

use eukhe_chord::context::{await_with_context, Context};
use indexmap::IndexMap;

use crate::session::{SessionError, SessionResult, TransactionScope, Tx};
use crate::types::{
    AnyTaskRecord, ConversationId, TaskAbortReason, TaskId, TaskOutcome, TaskState,
};

use super::invocation::InvocationMode;
use super::mirror::{needs_request_mark, with_abort_mark, with_state, Queued};
use super::ownership::{failed_outcome, parent_of, Background, Overlay, Scope, Up};
use super::reservation::Resolution;
use super::{Inner, SchedulerOutcome, TaskScheduler};

/// What `abortTask()` found: the task was marked (or orphaned), or it was
/// already terminal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TaskAbortResult {
    /// `"marked"`.
    Marked,
    /// `"terminal"`.
    Terminal,
}

impl TaskAbortResult {
    /// The TS string: `"marked"` or `"terminal"`.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Marked => "marked",
            Self::Terminal => "terminal",
        }
    }
}

/// How far `Conversation.abort()` reaches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ConversationAbortReach {
    /// Ordinary traversal: background tasks are boundaries.
    Ordinary,
    /// `{ background: true }`: traversal crosses background boundaries, and
    /// the wait also covers every task it reached.
    Background,
}

impl TaskScheduler {
    /// Commit the abort mark, or settle a task that no registered definition
    /// can take as `orphaned` when nothing it owns is live, then join the run
    /// invocation seen on the line; the commit listener signalled it. The
    /// abort invocation starts once the task's ordinary owned work is gone. A
    /// `completing` task is only marked. A request replaces a `restart` mark,
    /// so a task abandoned after a restart that waits for its definition is
    /// orphaned. The commit is enqueued at the call, as the TS promise starts
    /// eagerly; the returned future only awaits it.
    ///
    /// # Errors
    ///
    /// `Task {id} does not exist`, a cancelled `cx`, or a Session failure.
    pub(crate) fn abort(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> impl Future<Output = SessionResult<TaskAbortResult>> + Send + 'static {
        self.abort_keeping(id, cx, KeepRestart::No)
    }

    /// [`Self::abort`]; with [`KeepRestart::Yes`], as for an owner's own
    /// cleanup, a task abandoned after a restart keeps its mark and waits on.
    pub(crate) fn abort_keeping(
        &self,
        id: TaskId,
        cx: &Context,
        keep_restart: KeepRestart,
    ) -> impl Future<Output = SessionResult<TaskAbortResult>> + Send + 'static {
        let inner = self.inner.arc();
        let committed = self.inner.session.commit_with(
            move |tx| async move {
                let Some(current) = tx.task(id).await? else {
                    return Err(SessionError::error(format!("Task {id} does not exist")));
                };
                if matches!(current.state, TaskState::Terminal { .. }) {
                    return Ok((TaskAbortResult::Terminal, None));
                }
                let invocation = inner.lock().invocations.get(&id).cloned();
                // A restart-marked task has no run invocation; it only waits for its abort.
                if keep_restart == KeepRestart::Yes
                    && current.abort_reason == Some(TaskAbortReason::Restart)
                {
                    return Ok((TaskAbortResult::Marked, None));
                }
                if invocation.is_none() && !matches!(current.state, TaskState::Completing { .. }) {
                    inner.load_scopes(Queued::Skip).await?;
                    if !inner.lock().owned_live(None).contains_key(&id) {
                        let snapshot = inner.registry.snapshot();
                        if let Resolution::Blocked(reason) = inner.resolve(&current, &snapshot) {
                            let reason = reason.as_str().to_owned();
                            inner
                                .terminate(&tx, &current, SchedulerOutcome::Orphaned { reason })
                                .await?;
                            return Ok((TaskAbortResult::Marked, None));
                        }
                    }
                }
                if needs_request_mark(&current) {
                    tx.set_task(with_abort_mark(&current, None))?;
                }
                let run = invocation.filter(|invocation| invocation.mode == InvocationMode::Run);
                Ok((TaskAbortResult::Marked, run))
            },
            cx,
            TransactionScope::default(),
        );
        let failed = self.inner.session.failed();
        let cx = cx.clone();
        async move {
            let (result, run) = committed.await?;
            // The commit listener signalled the run; join it. A run that
            // ignores its signal can outlive a failed Session, which ends the
            // wait instead.
            if let Some(run) = run {
                // `Promise.race([run.done, session.failed])`: the first listed
                // wins when both have settled.
                let joined = async move {
                    tokio::select! {
                        biased;
                        () = run.done() => Ok(()),
                        error = failed => Err(error),
                    }
                };
                await_with_context(joined, &cx)
                    .await
                    .map_err(SessionError::Aborted)??;
            }
            Ok(result)
        }
    }

    /// `Conversation.abort()`: in one commit, withdraw the queued inputs and
    /// mark every live non-background task that ordinary traversal from the
    /// conversation reaches; resolves once the scope is idle. With
    /// [`ConversationAbortReach::Background`], traversal crosses background
    /// boundaries, and the wait also covers every task it reached. The
    /// commit is enqueued at the call, as the TS promise starts eagerly.
    ///
    /// # Errors
    ///
    /// A cancelled `cx`, `Harness is closed`, or a Session failure.
    pub(crate) fn abort_conversation(
        &self,
        conversation_id: ConversationId,
        reach: ConversationAbortReach,
        cx: &Context,
    ) -> impl Future<Output = SessionResult<()>> + Send + 'static {
        let background = match reach {
            ConversationAbortReach::Ordinary => Background::Boundary,
            ConversationAbortReach::Background => Background::Cross,
        };
        let inner = self.inner.arc();
        let committed = self.inner.session.commit_with(
            move |tx| async move {
                let queued = inner.load_scopes(Queued::Load).await?;
                let scope = Scope::Conversation(conversation_id);
                let mut reached = Vec::new();
                {
                    let state = inner.lock();
                    for record in state.live.values() {
                        if record.background && background == Background::Boundary {
                            continue;
                        }
                        if state.in_scope(parent_of(record), scope, background) != Some(true) {
                            continue;
                        }
                        reached.push(record.id);
                        if needs_request_mark(record) {
                            tx.set_task(with_abort_mark(record, None))?;
                        }
                    }
                }
                for id in queued {
                    let in_scope = inner
                        .lock()
                        .in_scope(Up::Conversation(id), scope, background)
                        == Some(true);
                    if in_scope {
                        (inner.withdraw_inputs)(tx.clone(), id).await?;
                    }
                }
                Ok(reached)
            },
            cx,
            TransactionScope::default(),
        );
        let (scheduler, cx) = (self.clone(), cx.clone());
        async move {
            let reached = committed.await?;
            if reach == ConversationAbortReach::Background {
                for id in reached {
                    scheduler.wait_for_task(id, &cx).await?;
                }
            }
            scheduler.wait_for_idle(Some(conversation_id), &cx).await
        }
    }
}

impl Inner {
    pub(super) fn schedule_reconcile(&self) {
        {
            let mut state = self.lock();
            if state.reconcile_scheduled || state.closing {
                return;
            }
            state.reconcile_scheduled = true;
        }
        tokio::spawn(self.arc().reconcile());
    }

    /// One commit that applies what committed records imply: abort marks below
    /// live owners with cancellation intent (spec §5.4), `failFast` marks
    /// (spec §5.5), withdrawn queued inputs below cancelled owners, and the
    /// final terminal record of every `completing` task whose ordinary owned
    /// work is gone. The durable records are the intent, so this also repairs
    /// whatever a crash left unapplied. Resolves idle waiters that the loaded
    /// edges decide.
    async fn reconcile(self: std::sync::Arc<Self>) {
        let (cascade, checks) = {
            let mut state = self.lock();
            state.reconcile_scheduled = false;
            let cascade = std::mem::take(&mut state.cascade_pending);
            let checks: Vec<TaskId> = state.fail_fast_checks.drain(..).collect();
            (cascade, checks)
        };
        let inner = std::sync::Arc::clone(&self);
        let pass_checks = checks;
        let result = self
            .session
            .commit_with(
                move |tx| async move {
                    if inner.closing() {
                        return Ok(());
                    }
                    let queued = inner
                        .load_scopes(if cascade { Queued::Load } else { Queued::Skip })
                        .await?;
                    // A cascade from an abandoned owner passes its `restart` reason on; any other
                    // intent marks, or upgrades a `restart` mark, as a request. Collected first, so
                    // a request wins over a `restart` mark of the same pass.
                    let mut marks = Marks::default();
                    {
                        // Loading edges can reveal a cancelled owner, so marks
                        // are derived on every pass.
                        let state = inner.lock();
                        for record in state.live.values() {
                            if record.background {
                                continue;
                            }
                            let Some(owner) = state.cancelling_owner(parent_of(record)) else {
                                continue;
                            };
                            // Only an owner abandoned after a restart, and nothing else, passes its
                            // reason on.
                            let restart = owner.abort_reason == Some(TaskAbortReason::Restart)
                                && !failed_outcome(owner);
                            marks.mark(record, restart.then_some(TaskAbortReason::Restart));
                        }
                    }
                    for id in pass_checks {
                        let waiter = inner.lock().live.get(&id).cloned();
                        let Some(TaskState::Waiting { on, .. }) = waiter.map(|waiter| waiter.state)
                        else {
                            continue;
                        };
                        if !inner.any_failed(&on).await? {
                            continue;
                        }
                        // Every other live task: the failed one keeps its own outcome.
                        let state = inner.lock();
                        for member in &on {
                            if let Some(record) = state.live.get(member) {
                                if !failed_outcome(record) {
                                    marks.mark(record, None);
                                }
                            }
                        }
                    }
                    marks.apply(&tx)?;
                    for id in queued {
                        let below = inner.lock().below_cancelled(Up::Conversation(id));
                        if below {
                            (inner.withdraw_inputs)(tx.clone(), id).await?;
                        }
                    }
                    inner.finalize(&tx).await
                },
                &self.context,
                TransactionScope::default(),
            )
            .await;
        if let Err(error) = result {
            // No extension code runs in this commit: a failure is a storage
            // failure, a host callback, or a bug. None is fixed by running the
            // pass again, so it fails the Session, which reports it.
            self.fail_session(error);
        }
        self.settle_idle();
    }

    /// Whether any of `ids` holds or ended with an outcome other than `completed`.
    async fn any_failed(&self, ids: &[TaskId]) -> SessionResult<bool> {
        for id in ids {
            let live = self.lock().live.get(id).cloned();
            let record = match live {
                Some(record) => Some(record),
                None => self.storage.task(*id, &self.context).await?,
            };
            if record.as_ref().is_some_and(failed_outcome) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Write the terminal record of every `completing` task without live
    /// ordinary owned work. Finalizing one can free its owner, so this repeats
    /// over the commit's candidates until nothing changes. A held scheduler
    /// outcome gets its Harness cleanup here.
    async fn finalize(&self, tx: &Tx) -> SessionResult<()> {
        loop {
            let overlay = Overlay::of(tx);
            let done: Vec<AnyTaskRecord> = {
                let state = self.lock();
                let owned = state.owned_live(Some(&overlay));
                state
                    .live_records(Some(&overlay))
                    .filter(|record| {
                        matches!(record.state, TaskState::Completing { .. })
                            && !owned.contains_key(&record.id)
                    })
                    .cloned()
                    .collect()
            };
            if done.is_empty() {
                return Ok(());
            }
            for record in done {
                let TaskState::Completing { outcome } = &record.state else {
                    continue;
                };
                let outcome = outcome.clone();
                tx.set_task(with_state(
                    &record,
                    TaskState::Terminal {
                        outcome: outcome.clone(),
                    },
                ))?;
                // REMINDER: only the scheduler writes `faulted` and `orphaned` (spec §5.4);
                // their cleanup waits for this commit.
                if let Some(outcome) = scheduler_outcome(&outcome) {
                    (self.settle_outcome)(tx.clone(), record.clone(), outcome).await?;
                }
            }
        }
    }

    /// Write an outcome the scheduler decided. While the task's ordinary owned
    /// work is live it holds as `completing` and its Harness cleanup waits for
    /// the final commit (spec §5.5, rule 4); otherwise it is terminal with its
    /// cleanup.
    pub(super) async fn terminate(
        &self,
        tx: &Tx,
        record: &AnyTaskRecord,
        outcome: SchedulerOutcome,
    ) -> SessionResult<()> {
        self.load_scopes(Queued::Skip).await?;
        let overlay = Overlay::of(tx);
        let holds = self
            .lock()
            .owned_live(Some(&overlay))
            .contains_key(&record.id);
        if holds {
            tx.set_task(with_state(
                record,
                TaskState::Completing {
                    outcome: outcome.outcome(),
                },
            ))?;
            return Ok(());
        }
        tx.set_task(with_state(
            record,
            TaskState::Terminal {
                outcome: outcome.outcome(),
            },
        ))?;
        (self.settle_outcome)(tx.clone(), record.clone(), outcome).await
    }
}

/// Abort marks staged by one reconcile pass, each task at most once, in
/// staging order: a request wins over a `restart` mark of the same pass.
#[derive(Default)]
struct Marks(IndexMap<TaskId, (AnyTaskRecord, Option<TaskAbortReason>)>);

impl Marks {
    fn mark(&mut self, record: &AnyTaskRecord, reason: Option<TaskAbortReason>) {
        if self
            .0
            .get(&record.id)
            .is_some_and(|(_, staged)| staged.is_none())
        {
            return;
        }
        if record.abort_requested && (record.abort_reason.is_none() || reason.is_some()) {
            return;
        }
        self.0.insert(record.id, (record.clone(), reason));
    }

    fn apply(self, tx: &Tx) -> SessionResult<()> {
        for (record, reason) in self.0.into_values() {
            tx.set_task(with_abort_mark(&record, reason))?;
        }
        Ok(())
    }
}

/// Whether an abort keeps a `restart` mark (an owner's own cleanup through
/// `abort_owned`) instead of replacing it with a request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum KeepRestart {
    No,
    Yes,
}

/// The scheduler-written outcome a held outcome is, if any.
fn scheduler_outcome(outcome: &TaskOutcome) -> Option<SchedulerOutcome> {
    match outcome {
        TaskOutcome::Faulted { error } => Some(SchedulerOutcome::Faulted {
            error: error.clone(),
        }),
        TaskOutcome::Orphaned { reason } => Some(SchedulerOutcome::Orphaned {
            reason: reason.clone(),
        }),
        TaskOutcome::Completed { .. }
        | TaskOutcome::Failed { .. }
        | TaskOutcome::Aborted { .. } => None,
    }
}
