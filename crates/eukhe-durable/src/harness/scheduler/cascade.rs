//! Aborts and cascades: direct and conversation aborts, the reconcile commit
//! that derives abort marks (spec §5.4), `failFast` marks and withdrawn
//! inputs (spec §5.5), finalization of held outcomes, and scheduler-written
//! outcomes.

use std::collections::HashSet;
use std::future::Future;

use eukhe_bend::rules::task_life::{Mark, Member, Row};
use eukhe_chord::context::{await_with_context, Context};
use indexmap::{IndexMap, IndexSet};

use crate::session::{SessionError, SessionResult, TransactionScope, Tx};
use crate::types::{
    AnyTaskRecord, ConversationId, TaskAbortReason, TaskId, TaskOutcome, TaskState, TaskStatus,
};

use super::invocation::InvocationMode;
use super::life::{self, OwnedWork};
use super::mirror::{with_state, Queued};
use super::ownership::{failed_outcome, is_live, Background, Node, Overlay, Scope, TaskNode, Walk};
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
                    if !inner.lock().has_owned_live(id, Walk::default()) {
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
                if let Some(marked) = life::marked(&current, Mark::Request) {
                    tx.set_task(marked)?;
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
                    let walk = Walk {
                        background,
                        ..Walk::default()
                    };
                    for found in state.walk_down(Node::Conversation(conversation_id), walk) {
                        let Some(live) = found.live else {
                            continue;
                        };
                        if found.node.background && background == Background::Boundary {
                            continue;
                        }
                        reached.push(live.id);
                        if let Some(marked) = life::marked(live, Mark::Request) {
                            tx.set_task(marked)?;
                        }
                    }
                }
                for id in queued {
                    let in_scope = inner
                        .lock()
                        .in_scope(Node::Conversation(id), scope, background)
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
                    // The task-life rules decide every mark (`life::cascade`,
                    // `life::join`): a cascade from an abandoned owner passes
                    // its `restart` mark on; any other intent marks, or
                    // upgrades a `restart` mark, as a request. Collected
                    // first, so a request wins over a `restart` mark of the
                    // same pass.
                    let mut marks = Marks::default();
                    {
                        // Every task below a live owner with cancellation
                        // intent, which is its nearest one: a walk down from
                        // each owner with intent does not enter another, whose
                        // own walk covers what is below it. Derived again on
                        // every pass, as loading edges can reveal a cancelled
                        // owner.
                        let state = inner.lock();
                        let enter = |below: TaskId| !state.intent.contains(&below);
                        let walk = Walk {
                            enter: Some(&enter),
                            ..Walk::default()
                        };
                        for id in &state.intent {
                            let owner = &state.live[id];
                            let reached: Vec<_> = state.walk_down(Node::Task(*id), walk).collect();
                            let rows: Vec<Row> = reached
                                .iter()
                                .map(|found| Row {
                                    live: found.live.is_some(),
                                    background: found.node.background,
                                    mark: found
                                        .live
                                        .map_or(Mark::Clear, |live| marks.effective(live)),
                                })
                                .collect();
                            for (found, mark) in reached.iter().zip(life::cascade(owner, &rows)) {
                                if let Some(live) = found.live {
                                    marks.set(live, mark);
                                }
                            }
                        }
                    }
                    for id in pass_checks {
                        let waiter = inner.lock().live.get(&id).cloned();
                        let Some(TaskState::Waiting { on, policy, .. }) =
                            waiter.map(|waiter| waiter.state)
                        else {
                            continue;
                        };
                        let members = inner.members(&on).await?;
                        let joined = life::join(policy, &members);
                        let state = inner.lock();
                        for (member, abort) in on.iter().zip(joined.abort) {
                            if !abort {
                                continue;
                            }
                            if let Some(record) = state.live.get(member) {
                                marks.set(
                                    record,
                                    life::merge(marks.effective(record), Mark::Request),
                                );
                            }
                        }
                    }
                    marks.apply(&tx)?;
                    for id in queued {
                        let below = inner.lock().below_cancelled(Node::Conversation(id));
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

    /// Each of `ids` as a join reads it: live or not, and whether it holds or
    /// ended with an outcome other than `completed`.
    async fn members(&self, ids: &[TaskId]) -> SessionResult<Vec<Member>> {
        let mut members = Vec::with_capacity(ids.len());
        for id in ids {
            let live = self.lock().live.get(id).cloned();
            let record = match live {
                Some(record) => Some(record),
                None => self.storage.task(*id, &self.context).await?,
            };
            members.push(Member {
                live: record.as_ref().is_some_and(is_live),
                failed: record.as_ref().is_some_and(failed_outcome),
            });
        }
        Ok(members)
    }

    /// Write the terminal record of every `completing` task without live
    /// ordinary owned work, as the task-life rules decide
    /// (`life::finalize`). Finalizing one can free its owner, so this
    /// repeats over the commit's candidates until nothing changes. A held
    /// scheduler outcome gets its Harness cleanup here.
    async fn finalize(&self, tx: &Tx) -> SessionResult<()> {
        // A worklist: the tasks that started holding, and the holders of work
        // that ended. Finalizing one can free the nearest live task above it,
        // which goes on the list. Tasks finalized here have no live work below
        // them, so walks down skip them. In rounds: the holders the tasks of
        // one round free are checked once, in the next, so a holder of many
        // tasks that end together is walked once, not once per task.
        let mut round: Vec<TaskId> = self.lock().finalize_checks.drain(..).collect();
        let mut done: HashSet<TaskId> = HashSet::new();
        let mut overlay = Overlay::of(tx);
        while !round.is_empty() {
            let mut next: IndexSet<TaskId> = IndexSet::new();
            for id in round {
                if done.contains(&id) {
                    continue;
                }
                let held = {
                    let state = self.lock();
                    let record = overlay.tasks.get(&id).or_else(|| state.live.get(&id));
                    // Only a held outcome finalizes; skip the walk for the rest.
                    let holding =
                        record.filter(|record| record.state.status() == TaskStatus::Completing);
                    let enter = |below: TaskId| !done.contains(&below);
                    let walk = Walk {
                        overlay: Some(&overlay),
                        enter: Some(&enter),
                        ..Walk::default()
                    };
                    holding.map(|record| {
                        let owned = if state.has_owned_live(id, walk) {
                            OwnedWork::Live
                        } else {
                            OwnedWork::Gone
                        };
                        (record.clone(), owned)
                    })
                };
                let Some((record, owned)) = held else {
                    continue;
                };
                let finalized = life::finalize(&record, owned)?;
                let TaskState::Terminal { outcome } = &finalized else {
                    continue;
                };
                // REMINDER: only the scheduler writes `faulted` and `orphaned` (spec §5.4);
                // their cleanup waits for this commit.
                let settled = scheduler_outcome(outcome);
                let terminal = with_state(&record, finalized);
                tx.set_task(terminal.clone())?;
                overlay.tasks.insert(id, terminal);
                done.insert(id);
                if let Some(outcome) = settled {
                    (self.settle_outcome)(tx.clone(), record.clone(), outcome).await?;
                }
                let above = self
                    .lock()
                    .nearest_live_above(TaskNode::of(&record), Some(&overlay))
                    .filter(|above| matches!(above.state, TaskState::Completing { .. }))
                    .map(|above| above.id);
                if let Some(above) = above {
                    next.insert(above);
                }
            }
            round = next.into_iter().collect();
        }
        Ok(())
    }

    /// Write an outcome the scheduler decided, as the task-life rules decide
    /// (`life::settle`). While the task's ordinary owned work is live it
    /// holds as `completing` and its Harness cleanup waits for the final
    /// commit (spec §5.5, rule 4); otherwise it is terminal with its cleanup.
    pub(super) async fn terminate(
        &self,
        tx: &Tx,
        record: &AnyTaskRecord,
        outcome: SchedulerOutcome,
    ) -> SessionResult<()> {
        self.load_scopes(Queued::Skip).await?;
        let overlay = Overlay::of(tx);
        let holds = self.lock().has_owned_live(
            record.id,
            Walk {
                overlay: Some(&overlay),
                ..Walk::default()
            },
        );
        let owned = if holds {
            OwnedWork::Live
        } else {
            OwnedWork::Gone
        };
        let state = life::settle(record, &outcome.outcome(), owned)?;
        let terminal = state.status() == TaskStatus::Terminal;
        tx.set_task(with_state(record, state))?;
        if !terminal {
            return Ok(());
        }
        (self.settle_outcome)(tx.clone(), record.clone(), outcome).await
    }
}

/// Abort marks staged by one reconcile pass, each task at most once, in
/// staging order, with the mark it takes: a request wins over a `restart`
/// mark of the same pass (`life::merge`).
#[derive(Default)]
struct Marks(IndexMap<TaskId, (AnyTaskRecord, Mark)>);

impl Marks {
    /// The mark of `record` so far in this pass.
    fn effective(&self, record: &AnyTaskRecord) -> Mark {
        self.0
            .get(&record.id)
            .map_or_else(|| life::mark_of(record), |(_, mark)| *mark)
    }

    /// Stage `mark` for `record` when it is not the record's own.
    fn set(&mut self, record: &AnyTaskRecord, mark: Mark) {
        if mark != life::mark_of(record) {
            self.0.insert(record.id, (record.clone(), mark));
        }
    }

    fn apply(self, tx: &Tx) -> SessionResult<()> {
        for (record, mark) in self.0.into_values() {
            tx.set_task(life::with_mark(&record, mark))?;
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
