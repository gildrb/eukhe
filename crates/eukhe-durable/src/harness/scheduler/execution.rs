//! Running invocations off the line: phase handlers each preceded by a step
//! on the line that applies the precedence rules (spec §5.1), the abort
//! handler, handover to a replacement definition (spec §5.4), and the state a
//! runtime commit writes.

use std::collections::HashSet;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::json::JsonValue;
use futures::future::{BoxFuture, Shared};

use crate::harness::types::{Agent, RegistrySnapshot};
use crate::session::{SessionError, SessionResult, TransactionScope, Tx};
use crate::tasks::{AnyTask, NextTaskState, RunningTask, TaskRuntimeBackend};
use crate::types::{AnyTaskRecord, JoinPolicy, TaskId, TaskOutcomeError, TaskState, TaskStatus};

use super::invocation::{Invocation, InvocationMode};
use super::mirror::{checkpoint_of, with_state, Queued};
use super::ownership::{parent_of, Overlay, Step};
use super::reservation::{can_reserve, Reservation};
use super::runtime::InvocationRuntime;
use super::{Inner, SchedulerOutcome};

/// The agent resolution of one phase, shared by every caller in it.
pub(super) type AgentResolution = Shared<BoxFuture<'static, SessionResult<Arc<Agent>>>>;

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
            let handled = phase
                .task()
                .definition()
                .run_phase(running, Arc::clone(&runtime), invocation.context.clone())
                .await;
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
                    tx.set_task(with_state(
                        current,
                        TaskState::Pending {
                            checkpoint: checkpoint_of(current),
                        },
                    ))?;
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
            }
        }
        invocation.stop_watches();
        // Pending waits bound to the invocation, such as a tool's
        // waitForTask(), reject with it.
        invocation
            .controller
            .abort(Some(Arc::new(invocation.ended_error())));
    }

    /// Replace a running task's state with what it committed. A terminal state
    /// holds as `completing` while ordinary owned work is live, judged on the
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
        if let TaskState::Terminal { outcome } = &next {
            let overlay = Overlay::of(tx);
            self.load_scopes(Queued::Skip).await?;
            for record in overlay.tasks.values() {
                self.load_chain(parent_of(record), Some(&overlay)).await?;
            }
            let holds = self
                .lock()
                .owned_live(Some(&overlay))
                .contains_key(&current.id);
            if holds {
                return tx.set_task(with_state(
                    current,
                    TaskState::Completing {
                        outcome: outcome.clone(),
                    },
                ));
            }
        }
        tx.set_task(with_state(current, next))
    }

    /// A wait names existing tasks other than the waiter and its owners, which
    /// could never finish first; `failFast` only tasks the waiter owns. An
    /// abort handler cannot wait.
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
        self.load_chain(parent_of(current), None).await?;
        let owners: HashSet<TaskId> = self
            .lock()
            .above(parent_of(current), None)
            .filter_map(|step| match step {
                Step::Task { id, .. } => Some(id),
                Step::Conversation(_) | Step::Unknown => None,
            })
            .collect();
        for id in on {
            if *id == current.id || owners.contains(id) {
                return Err(SessionError::error(format!(
                    "Task {} cannot wait on itself or its owner {id}",
                    current.id
                )));
            }
            let staged = overlay
                .tasks
                .get(id)
                .cloned()
                .or_else(|| self.lock().live.get(id).cloned());
            let member = match staged {
                Some(member) => Some(member),
                None => self.storage.task(*id, &self.context).await?,
            };
            let Some(member) = member else {
                return Err(SessionError::error(format!("Task {id} does not exist")));
            };
            if policy == JoinPolicy::FailFast && member.owner != Some(current.id) {
                return Err(SessionError::error(format!(
                    "Task {} can wait failFast only on tasks it owns; {id} is not one",
                    current.id
                )));
            }
        }
        Ok(())
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
