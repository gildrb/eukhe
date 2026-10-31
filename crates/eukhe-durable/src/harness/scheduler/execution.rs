//! Running invocations off the line: phase handlers each preceded by a step
//! on the line that applies the precedence rules (spec §5.1), the abort
//! handler, handover to a replacement definition (spec §5.4), and the state a
//! runtime commit writes.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};
use std::time::Duration;

use eukhe_chord::json::JsonValue;
use futures::future::{BoxFuture, Shared};

use crate::harness::types::{Agent, RegistrySnapshot};
use crate::session::{SessionError, SessionResult, TransactionScope, Tx};
use crate::tasks::{AnyTask, NextTaskState, RunningTask, TaskRuntimeBackend};
use crate::types::{AnyTaskRecord, JoinPolicy, TaskId, TaskOutcomeError, TaskState, TaskStatus};

use super::invocation::{Invocation, InvocationMode};
use super::life::{self, OwnedWork};
use super::mirror::{checkpoint_of, with_state, Queued};
use super::ownership::{is_live, parent_of, Node, Overlay, Walk};
use super::reservation::{can_reserve, Reservation};
use super::runtime::InvocationRuntime;
use super::state::State;
use super::{Inner, SchedulerOutcome};

/// The agent resolution of one phase, shared by every caller in it.
pub(super) type AgentResolution = Shared<BoxFuture<'static, SessionResult<Arc<Agent>>>>;

/// How long a phase handler may run on after its invocation's signal (an
/// abort mark, close, or the invocation's end) before the driver drops it
/// (LAWS.bend H4.6). A handler that honours its signal returns within
/// it and cleans up; one stuck in a wait that ignores the signal (a hook, a
/// lock, a peer that never answers) is dropped, so every abort ends.
const ABORT_GRACE: Duration = Duration::from_secs(3);

/// What a runtime reads for the phase handler it serves: the phase's snapshot
/// and task, and its lazily resolved agent.
pub(super) struct Phase {
    state: Mutex<PhaseState>,
}

struct PhaseState {
    snapshot: RegistrySnapshot,
    task: AnyTask,
    /// Replacement definition already reported as unable to take over.
    reported: Option<ReportedTask>,
    agent: Option<AgentResolution>,
}

/// The replacement a phase reported, `None` for a missing definition (TS
/// `ReportedTask`).
struct ReportedTask {
    task: Option<AnyTask>,
}

impl Phase {
    pub(super) fn new(snapshot: RegistrySnapshot, task: AnyTask) -> Self {
        Self {
            state: Mutex::new(PhaseState {
                snapshot,
                task,
                reported: None,
                agent: None,
            }),
        }
    }

    fn lock(&self) -> MutexGuard<'_, PhaseState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    pub(super) fn snapshot(&self) -> RegistrySnapshot {
        self.lock().snapshot.clone()
    }

    pub(super) fn task(&self) -> AnyTask {
        self.lock().task.clone()
    }

    /// The phase's agent resolution, started by `start` at first use.
    pub(super) fn agent(
        &self,
        start: impl FnOnce(&RegistrySnapshot) -> AgentResolution,
    ) -> AgentResolution {
        let mut state = self.lock();
        if let Some(agent) = &state.agent {
            return agent.clone();
        }
        let agent = start(&state.snapshot);
        state.agent = Some(agent.clone());
        agent
    }

    /// Each phase handler resolves its agent afresh, at first use.
    fn reset_agent(&self) {
        self.lock().agent = None;
    }
}

/// Outcome of the phase that just returned, judged by the next step.
struct PhaseResult {
    checkpoint: JsonValue,
    failure: Option<SessionError>,
}

/// Step decision: continue with the next phase, end the invocation, or end it
/// by writing `faulted`.
pub(super) enum Decision {
    Continue,
    End,
    Fault(SessionError),
}

/// Failure reported when a running task keeps its old definition because the
/// registry's replacement is missing or cannot take it. `cause` is
/// `missing_task` or `incompatible_task` (TS `Error.cause`).
#[derive(Clone, Debug, thiserror::Error)]
#[error("{message}")]
pub struct DefinitionKept {
    message: String,
    cause: &'static str,
}

impl DefinitionKept {
    /// `missing_task` or `incompatible_task`.
    #[must_use]
    pub fn cause(&self) -> &'static str {
        self.cause
    }
}

/// Ends an invocation however its task future finishes, unwinding included.
struct Finish {
    inner: Arc<Inner>,
    invocation: Arc<Invocation>,
}

impl Drop for Finish {
    fn drop(&mut self) {
        self.inner.end(&self.invocation);
        self.invocation.finish();
        self.inner.kick();
    }
}

impl Inner {
    pub(super) fn start(&self, reservation: Reservation) {
        let inner = self.arc();
        tokio::spawn(async move {
            let _finish = Finish {
                inner: Arc::clone(&inner),
                invocation: Arc::clone(&reservation.invocation),
            };
            match reservation.invocation.mode {
                InvocationMode::Run => inner.run(reservation).await,
                InvocationMode::Abort => inner.run_abort(reservation).await,
            }
        });
    }

    /// Run phase handlers, each preceded by a step that decides on the line
    /// whether the invocation continues.
    async fn run(self: &Arc<Self>, reservation: Reservation) {
        let Reservation {
            invocation,
            task,
            snapshot,
        } = reservation;
        let phase = Arc::new(Phase::new(snapshot, task));
        let runtime: Arc<dyn TaskRuntimeBackend> = Arc::new(InvocationRuntime::new(
            Arc::clone(self),
            Arc::clone(&invocation),
            Arc::clone(&phase),
        ));
        let mut previous: Option<PhaseResult> = None;
        loop {
            let decide = {
                let inner = Arc::clone(self);
                let phase = Arc::clone(&phase);
                let previous = previous.take();
                move |tx: &Tx, current: &AnyTaskRecord| {
                    inner.decide(tx, current, previous.as_ref(), &phase)
                }
            };
            let current = self.step(&invocation, decide).await;
            // Close may seal between the decision and dispatch.
            let Some(current) = current else {
                return;
            };
            if self.closing() {
                return;
            }
            let checkpoint = checkpoint_of(&current);
            phase.reset_agent();
            let Some(running) = RunningTask::from_record(current) else {
                return;
            };
            let handled = phase.task().definition().run_phase(
                running,
                Arc::clone(&runtime),
                invocation.context.clone(),
            );
            tokio::pin!(handled);
            // The one place a phase meets its signal (H4.6): every hook and
            // every wait inside it ends with the invocation.
            let signal = invocation.signal();
            let handled = tokio::select! {
                biased;
                handled = &mut handled => handled,
                reason = signal.cancelled() => {
                    match tokio::time::timeout(ABORT_GRACE, &mut handled).await {
                        Ok(handled) => handled,
                        Err(_elapsed) => Err(SessionError::Aborted(reason)),
                    }
                }
            };
            previous = Some(PhaseResult {
                checkpoint,
                failure: handled.err(),
            });
        }
    }

    /// Precedence rules for a run invocation, on the line. Rules 1 (terminal,
    /// `completing`, or `waiting`) and 2 (closing) are applied by `step`.
    /// Returns whether the invocation continues with the next phase.
    fn decide(
        &self,
        tx: &Tx,
        current: &AnyTaskRecord,
        previous: Option<&PhaseResult>,
        phase: &Phase,
    ) -> SessionResult<Decision> {
        // 3. abort mark: end; a fresh abort invocation starts once the task's
        // ordinary owned work is gone.
        if current.abort_requested {
            return Ok(Decision::End);
        }
        // An owner's cancellation intent ends it too, before its cascade marks
        // it; reservation then holds it back.
        if !current.background && self.lock().below_cancelled(parent_of(current)) {
            self.lock().cascade_pending = true;
            self.schedule_reconcile();
            return Ok(Decision::End);
        }
        let Some(previous) = previous else {
            return Ok(Decision::Continue);
        };
        // 4. uncaught error.
        if let Some(error) = &previous.failure {
            return Ok(Decision::Fault(error.clone()));
        }
        // 6. no durable progress.
        if current.state.checkpoint() == Some(&previous.checkpoint) {
            let phase_name = template_string(previous.checkpoint.get("phase"));
            let message = format!(
                "Task {} phase {phase_name} returned without durable progress",
                current.kind
            );
            return Ok(Decision::Fault(SessionError::error(message)));
        }
        // 5. progress: refresh the snapshot; hand over to a replacement
        // definition that can take the task.
        let snapshot = self.registry.snapshot();
        let next = snapshot.task(&current.kind).cloned();
        let task = {
            let mut state = phase.lock();
            state.snapshot = snapshot;
            state.task.clone()
        };
        let replaced = next
            .as_ref()
            .is_none_or(|next| !AnyTask::ptr_eq(next, &task));
        if replaced {
            if let Some(next) = &next {
                if can_reserve(next, current) {
                    tx.set_task(with_state(current, life::requeue(current)?))?;
                    return Ok(Decision::End);
                }
            }
            let fresh = {
                let mut state = phase.lock();
                let fresh = match &state.reported {
                    None => true,
                    Some(reported) => !same_task(reported.task.as_ref(), next.as_ref()),
                };
                if fresh {
                    state.reported = Some(ReportedTask { task: next.clone() });
                }
                fresh
            };
            if fresh {
                let cause = if next.is_none() {
                    "missing_task"
                } else {
                    "incompatible_task"
                };
                self.report(SessionError::other(DefinitionKept {
                    message: format!(
                        "Task {} keeps running under its old {} definition",
                        current.id, current.kind
                    ),
                    cause,
                }));
            }
        }
        Ok(Decision::Continue)
    }

    /// Run the abort handler once; rules 1, 2, and 4 apply, and returning
    /// without an outcome faults.
    async fn run_abort(self: &Arc<Self>, reservation: Reservation) {
        let Reservation {
            invocation,
            task,
            snapshot,
        } = reservation;
        let current = {
            let state = self.lock();
            if state.closing {
                return;
            }
            state.live.get(&invocation.task_id).cloned()
        };
        // The reservation committed `running`; nothing else changes the state
        // before the abort handler commits.
        let Some(current) = current.and_then(RunningTask::from_record) else {
            return;
        };
        let phase = Arc::new(Phase::new(snapshot, task.clone()));
        let runtime: Arc<dyn TaskRuntimeBackend> = Arc::new(InvocationRuntime::new(
            Arc::clone(self),
            Arc::clone(&invocation),
            phase,
        ));
        let failure = task
            .definition()
            .run_abort(current, runtime, invocation.context.clone())
            .await
            .err();
        let message = format!(
            "Abort handler of task {} returned without a terminal outcome",
            invocation.task_id
        );
        self.step(&invocation, move |_, _| {
            Ok(Decision::Fault(
                failure.unwrap_or_else(|| SessionError::error(message)),
            ))
        })
        .await;
    }

    /// One synchronous decision on the Session line. A task that is no longer
    /// running (rule 1: terminal, `completing`, or `waiting`) or a closing
    /// Harness (rule 2) ends the invocation without a write; otherwise
    /// `decide` may stage a write and returns whether the invocation
    /// continues. Ending happens inside the callback, before a fault's Harness
    /// cleanup. A rejected step, such as admission after close, also ends the
    /// invocation.
    async fn step<D>(
        self: &Arc<Self>,
        invocation: &Arc<Invocation>,
        decide: D,
    ) -> Option<AnyTaskRecord>
    where
        D: FnOnce(&Tx, &AnyTaskRecord) -> SessionResult<Decision> + Send + 'static,
    {
        let inner = Arc::clone(self);
        let ending = Arc::clone(invocation);
        let result = self
            .session
            .commit_with(
                move |tx| async move {
                    let (current, closing) = {
                        let state = inner.lock();
                        let current = state
                            .live
                            .get(&ending.task_id)
                            .filter(|found| found.state.status() == TaskStatus::Running)
                            .cloned();
                        (current, state.closing)
                    };
                    let decision = match &current {
                        Some(current) if !closing => decide(&tx, current)?,
                        Some(_) | None => Decision::End,
                    };
                    let fault = match decision {
                        Decision::Continue => return Ok(current),
                        Decision::End => None,
                        Decision::Fault(error) => Some(error),
                    };
                    inner.end(&ending);
                    if let (Some(error), Some(current)) = (fault, current) {
                        let error = TaskOutcomeError {
                            message: error.to_string(),
                            detail: None,
                        };
                        inner
                            .terminate(&tx, &current, SchedulerOutcome::Faulted { error })
                            .await?;
                    }
                    Ok(None)
                },
                &self.context,
                TransactionScope::default(),
            )
            .await;
        match result {
            Ok(current) => current,
            Err(error) => {
                self.end(invocation);
                // The step writes the scheduler's own decision, a fault or a
                // terminal record; a failure there would otherwise leave the
                // task running, to be reserved and run again.
                self.fail_session(error);
                None
            }
        }
    }

    /// End an invocation: its runtime operations reject from now on, its
    /// signal aborts, its watches stop, and its task is free.
    pub(super) fn end(&self, invocation: &Arc<Invocation>) {
        if !invocation.mark_ended() {
            return;
        }
        {
            let mut state = self.lock();
            if state
                .invocations
                .get(&invocation.task_id)
                .is_some_and(|registered| Arc::ptr_eq(registered, invocation))
            {
                state.invocations.remove(&invocation.task_id);
                if state.live.contains_key(&invocation.task_id) {
                    state.runnable.insert(invocation.task_id);
                }
            }
        }
        invocation.stop_watches();
        // Pending waits bound to the invocation, such as a tool's
        // waitForTask(), reject with it.
        invocation
            .controller
            .abort(Some(Arc::new(invocation.ended_error())));
    }

    /// Replace a running task's state with what it committed, as the
    /// task-life rules decide (`life::commit`): a terminal state holds as
    /// `completing` while ordinary owned work is live, judged on the
    /// commit's candidates, so work the same commit creates below the task
    /// counts. A wait is validated first.
    pub(super) async fn commit_state(
        &self,
        tx: &Tx,
        invocation: &Invocation,
        current: &AnyTaskRecord,
        next: NextTaskState,
    ) -> SessionResult<()> {
        let next = next.into_state();
        if let TaskState::Waiting { on, policy, .. } = &next {
            self.validate_wait(tx, invocation, current, on, *policy)
                .await?;
        }
        // Owned work matters only to an outcome; finding it walks the tree.
        let owned = match &next {
            TaskState::Terminal { .. } => {
                let overlay = Overlay::of(tx);
                self.load_scopes(Queued::Skip).await?;
                for record in overlay.tasks.values() {
                    self.load_chain(parent_of(record), Some(&overlay)).await?;
                }
                let holds = self.lock().has_owned_live(
                    current.id,
                    Walk {
                        overlay: Some(&overlay),
                        ..Walk::default()
                    },
                );
                if holds {
                    OwnedWork::Live
                } else {
                    OwnedWork::Gone
                }
            }
            TaskState::Pending { .. }
            | TaskState::Running { .. }
            | TaskState::Waiting { .. }
            | TaskState::Completing { .. } => OwnedWork::Gone,
        };
        tx.set_task(with_state(current, life::commit(current, &next, owned)?))
    }

    /// A wait names existing tasks, and `failFast` only tasks the waiter
    /// owns. It may not close a cycle in the wait-for graph, whose edges run
    /// from each task to what it waits on and to its live ordinary owned work
    /// (spec §5.5); waiting on itself or on an owner holding it are the
    /// shortest such cycles. An abort handler cannot wait.
    ///
    /// Invariant: the wait-for graph is acyclic. Only a wait adds an edge
    /// between existing tasks, as a new task has only incoming edges, so
    /// checking each wait maintains it.
    async fn validate_wait(
        &self,
        tx: &Tx,
        invocation: &Invocation,
        current: &AnyTaskRecord,
        on: &[TaskId],
        policy: JoinPolicy,
    ) -> SessionResult<()> {
        if invocation.mode == InvocationMode::Abort {
            return Err(SessionError::error(format!(
                "Abort handler of task {} cannot wait",
                current.id
            )));
        }
        let overlay = Overlay::of(tx);
        let mut targets = Vec::new();
        for id in on {
            let staged = {
                let state = self.lock();
                overlay
                    .tasks
                    .get(id)
                    .or_else(|| state.live.get(id))
                    .map(|member| (member.owner, is_live(member)))
            };
            let member = match staged {
                Some(member) => Some(member),
                None => self
                    .storage
                    .task(*id, &self.context)
                    .await?
                    .map(|member| (member.owner, is_live(&member))),
            };
            let Some((owner, live)) = member else {
                return Err(SessionError::error(format!("Task {id} does not exist")));
            };
            let child = owner == Some(current.id);
            if policy == JoinPolicy::FailFast && !child {
                return Err(SessionError::error(format!(
                    "Task {} can wait failFast only on tasks it owns; {id} is not one",
                    current.id
                )));
            }
            // A live child already holds the waiter (task-owned tasks are
            // never background): waiting on it adds no edge. A terminal task
            // has no edges.
            if live && !child {
                targets.push(*id);
            }
        }
        if targets.is_empty() {
            return Ok(());
        }
        // Owned work is found by walks down, which need the chains of every
        // live task loaded.
        self.load_scopes(Queued::Skip).await?;
        let cycle = self.lock().wait_cycle(current.id, &targets, &overlay);
        let Some(cycle) = cycle else {
            return Ok(());
        };
        let path = std::iter::once(current.id)
            .chain(cycle.iter().copied())
            .map(|id| id.to_string())
            .collect::<Vec<_>>()
            .join(" -> ");
        Err(SessionError::error(format!(
            "Task {} cannot wait on {}: {path} is a wait cycle",
            current.id, cycle[0]
        )))
    }
}

impl State {
    /// The path from a member of `on` back to `task` in the wait-for graph,
    /// if the wait would close a cycle (spec §5.1). An edge X -> Y means X
    /// cannot settle before Y: Y is in the `on` of waiting X that is not
    /// abort-marked, or Y is live ordinary owned work of X, which holds X as
    /// `completing`. Each task is visited once and each subtree walked once,
    /// so a check is bounded by the live work it reaches. Owner chains must
    /// be loaded.
    fn wait_cycle(&self, task: TaskId, on: &[TaskId], overlay: &Overlay) -> Option<Vec<TaskId>> {
        // Each reached task, by the task it was reached from; `None` for a
        // member of `on`.
        let mut from: HashMap<TaskId, Option<TaskId>> = HashMap::new();
        let mut walked: HashSet<TaskId> = HashSet::new();
        let mut pending: Vec<TaskId> = Vec::new();
        let reach = |from: &mut HashMap<TaskId, Option<TaskId>>,
                     pending: &mut Vec<TaskId>,
                     id: TaskId,
                     via: Option<TaskId>| {
            if let Entry::Vacant(vacant) = from.entry(id) {
                vacant.insert(via);
                pending.push(id);
            }
        };
        for id in on {
            reach(&mut from, &mut pending, *id, None);
        }
        while let Some(id) = pending.pop() {
            if id == task {
                // The steps from a member of `on` to here, following `from`
                // back.
                let mut steps = vec![id];
                let mut at = id;
                while let Some(Some(previous)) = from.get(&at) {
                    steps.push(*previous);
                    at = *previous;
                }
                steps.reverse();
                return Some(steps);
            }
            let Some(record) = overlay
                .tasks
                .get(&id)
                .or_else(|| self.live.get(&id))
                .filter(|record| is_live(record))
            else {
                continue;
            };
            // An abort-marked task waits only for its owned work, as abort
            // runs bottom-up (`waiting_on`).
            if let TaskState::Waiting { on, .. } = &record.state {
                if !record.abort_requested {
                    for member in on {
                        reach(&mut from, &mut pending, *member, Some(id));
                    }
                }
            }
            if !walked.insert(id) {
                continue;
            }
            // Below a walked task the walk does not go again: its own walk
            // covered what lies below.
            let mut found = Vec::new();
            {
                let enter = |below: TaskId| !walked.contains(&below);
                let walk = Walk {
                    overlay: Some(overlay),
                    enter: Some(&enter),
                    ..Walk::default()
                };
                for reached in self.walk_down(Node::Task(id), walk) {
                    if reached.live.is_none() || reached.node.background {
                        continue;
                    }
                    found.push(reached.id);
                    reach(&mut from, &mut pending, reached.id, Some(id));
                }
            }
            walked.extend(found);
        }
        None
    }
}

/// Identity of two optional definitions; two absent ones are the same.
fn same_task(left: Option<&AnyTask>, right: Option<&AnyTask>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => AnyTask::ptr_eq(left, right),
        (None, Some(_)) | (Some(_), None) => false,
    }
}

/// A JSON value interpolated into a JS template literal (`${value}`);
/// `undefined` when absent.
fn template_string(value: Option<&JsonValue>) -> String {
    match value {
        None => "undefined".to_owned(),
        Some(JsonValue::String(text)) => text.to_string(),
        Some(JsonValue::Object(_)) => "[object Object]".to_owned(),
        Some(JsonValue::Array(items)) => items
            .iter()
            .map(|item| match item {
                JsonValue::Null => String::new(),
                other => template_string(Some(other)),
            })
            .collect::<Vec<_>>()
            .join(","),
        Some(other @ (JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_))) => {
            other.to_string()
        }
    }
}
