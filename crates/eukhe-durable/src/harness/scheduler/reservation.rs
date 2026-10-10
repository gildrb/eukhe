//! Serial reservation on the Session line: the drain loop, definition
//! resolution with migration (spec §5.4), blocked tasks, and inspection.

use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::copy_json;
use indexmap::IndexMap;

use crate::harness::types::{
    RegistrySnapshot, SchedulingState, TaskBlockedReason, TaskInspection, TaskInspectionState,
};
use crate::session::{SessionError, SessionResult, TransactionScope};
use crate::tasks::{AnyTask, Migrated};
use crate::types::{AnyTaskRecord, TaskAbortReason, TaskId, TaskState, TaskStatus};

use super::invocation::{Invocation, InvocationMode};
use super::mirror::{with_abort_mark, with_state, Queued};
use super::ownership::parent_of;
use super::state::{FailedMigration, State};
use super::{Inner, SchedulerOutcome, TaskScheduler};

/// A definition that can take the task, with the record it runs, or why no
/// definition can.
pub(super) enum Resolution {
    Ready {
        task: AnyTask,
        /// The record, migrated when the definition is newer; boxed, as a
        /// record is far larger than a blocked reason.
        record: Box<AnyTaskRecord>,
        migrated: bool,
    },
    Blocked(TaskBlockedReason),
}

/// A definition that can take a record, or why none can; deciding it runs no
/// task code.
enum Fit {
    Task {
        task: AnyTask,
        migrates: bool,
    },
    Blocked {
        reason: TaskBlockedReason,
        error: Option<SessionError>,
    },
}

/// One reserved invocation and the definition and snapshot it starts with.
pub(super) struct Reservation {
    pub(super) invocation: Arc<Invocation>,
    pub(super) task: AnyTask,
    pub(super) snapshot: RegistrySnapshot,
}

/// Scheduling state and every live task with its derived state.
#[derive(Clone, Debug)]
pub(crate) struct SchedulerInspection {
    pub(crate) scheduling: SchedulingState,
    pub(crate) tasks: Vec<TaskInspection>,
}

impl TaskScheduler {
    /// Scheduling state and every live task with its derived state; call it on
    /// the Session line. Runs no task code: a pending migration shows as
    /// `ready` with `migrates`, and only a migration the scheduler already
    /// tried, or one that cannot exist, shows as failed.
    ///
    /// # Errors
    ///
    /// Loading owner chains from Storage failed.
    pub(crate) async fn inspect(
        &self,
        snapshot: &RegistrySnapshot,
    ) -> SessionResult<SchedulerInspection> {
        self.inner.load_scopes(Queued::Skip).await?;
        let state = self.inner.lock();
        let owned = state.owned_live(None);
        let tasks = state
            .live
            .values()
            .map(|record| TaskInspection {
                record: record.clone(),
                state: inspect_task(&state, record, snapshot, &owned),
            })
            .collect();
        let scheduling = if state.closing {
            SchedulingState::Closing
        } else if state.enabled {
            SchedulingState::Running
        } else {
            SchedulingState::Paused
        };
        Ok(SchedulerInspection { scheduling, tasks })
    }
}

fn inspect_task(
    state: &State,
    record: &AnyTaskRecord,
    snapshot: &RegistrySnapshot,
    owned: &IndexMap<TaskId, Vec<TaskId>>,
) -> TaskInspectionState {
    if state.invocations.contains_key(&record.id) {
        return TaskInspectionState::Running;
    }
    if record.state.status() == TaskStatus::Completing {
        return TaskInspectionState::Completing;
    }
    let on = state.waiting_on(record, owned);
    if !on.is_empty() {
        return TaskInspectionState::Waiting { on };
    }
    match fit(state, record, snapshot.task(&record.kind)) {
        Fit::Blocked { reason, error } => TaskInspectionState::Blocked { reason, error },
        Fit::Task { task, migrates } => {
            if migrates && !task.definition().has_migrate() {
                return TaskInspectionState::Blocked {
                    reason: TaskBlockedReason::MigrationFailed,
                    error: Some(missing_migration(record, &task)),
                };
            }
            TaskInspectionState::Ready { migrates }
        }
    }
}

impl State {
    /// Live tasks a task waits for before its next invocation: its live
    /// ordinary owned work when abort-marked, since abort runs bottom-up,
    /// otherwise the live part of the `on` of a wait.
    pub(super) fn waiting_on(
        &self,
        record: &AnyTaskRecord,
        owned: &IndexMap<TaskId, Vec<TaskId>>,
    ) -> Vec<TaskId> {
        if record.abort_requested {
            return owned.get(&record.id).cloned().unwrap_or_default();
        }
        match &record.state {
            TaskState::Waiting { on, .. } => on
                .iter()
                .copied()
                .filter(|id| self.live.contains_key(id))
                .collect(),
            TaskState::Pending { .. }
            | TaskState::Running { .. }
            | TaskState::Completing { .. }
            | TaskState::Terminal { .. } => Vec::new(),
        }
    }
}

fn fit(state: &State, record: &AnyTaskRecord, task: Option<&AnyTask>) -> Fit {
    let Some(task) = task else {
        return Fit::Blocked {
            reason: TaskBlockedReason::MissingTask,
            error: None,
        };
    };
    let version = task.version();
    if version == record.version {
        return Fit::Task {
            task: task.clone(),
            migrates: false,
        };
    }
    if version < record.version {
        return Fit::Blocked {
            reason: TaskBlockedReason::TaskTooOld,
            error: None,
        };
    }
    if let Some(failed) = state.failed_migrations.get(&record.id) {
        if AnyTask::ptr_eq(&failed.task, task) {
            return Fit::Blocked {
                reason: TaskBlockedReason::MigrationFailed,
                error: Some(failed.error.clone()),
            };
        }
    }
    Fit::Task {
        task: task.clone(),
        migrates: true,
    }
}

/// `Task {kind} version {version} has no migration from {stored}`.
pub(super) fn missing_migration(record: &AnyTaskRecord, task: &AnyTask) -> SessionError {
    SessionError::error(format!(
        "Task {} version {} has no migration from {}",
        record.kind,
        task.version(),
        record.version
    ))
}

/// Whether a definition can take the task at reservation: same version, or
/// newer with a migration.
pub(super) fn can_reserve(task: &AnyTask, record: &AnyTaskRecord) -> bool {
    task.version() == record.version
        || (task.version() > record.version && task.definition().has_migrate())
}

impl Inner {
    pub(super) fn kick(&self) {
        {
            let mut state = self.lock();
            state.dirty = true;
            if state.draining || !state.enabled || state.closing {
                return;
            }
            state.draining = true;
            // The drain loop's first pass.
            state.dirty = false;
        }
        // TS defers the drain by one microtask so it never commits from inside
        // a commit or registry listener, and its reservation commit then
        // enqueues at once. Enqueueing that commit here (it runs after the
        // listener's commit) keeps its place on the Session line ahead of the
        // work the listener's commit woke, as in TS.
        let first = self.reserve();
        tokio::spawn(self.arc().drain(first));
    }

    async fn drain<F>(self: Arc<Self>, first: F)
    where
        F: Future<Output = SessionResult<Vec<Reservation>>> + Send,
    {
        let result: SessionResult<()> = async {
            for reservation in first.await? {
                self.start(reservation);
            }
            loop {
                {
                    let mut state = self.lock();
                    if !(state.dirty && state.enabled && !state.closing) {
                        return Ok(());
                    }
                    state.dirty = false;
                }
                for reservation in self.reserve().await? {
                    self.start(reservation);
                }
            }
        }
        .await;
        if let Err(error) = result {
            // As in `reconcile()`: the reservation commit runs no extension code.
            self.fail_session(error);
        }
        let dirty = {
            let mut state = self.lock();
            state.draining = false;
            state.dirty
        };
        // A wakeup that arrived during a failed pass still needs its pass.
        if dirty {
            self.kick();
        }
    }

    /// Reserve every eligible task in one commit; orphan abort-marked tasks no
    /// definition can take, unless abandoned after a restart. The first pass
    /// after open only abort-marks the abandoned tasks, so later passes see
    /// the marks. The commit is enqueued now.
    #[expect(
        clippy::too_many_lines,
        reason = "one TS method: the reservation commit and its bookkeeping share state"
    )]
    fn reserve(&self) -> impl Future<Output = SessionResult<Vec<Reservation>>> + Send + 'static {
        let reservations: Arc<Mutex<Vec<Reservation>>> = Arc::default();
        let abandoned: Arc<Mutex<Vec<TaskId>>> = Arc::default();
        let inner = self.arc();
        let staged = Arc::clone(&reservations);
        let staged_abandoned = Arc::clone(&abandoned);
        let committed = self.session.commit_with(
            move |tx| async move {
                {
                    let state = inner.lock();
                    if !state.enabled || state.closing {
                        return Ok(());
                    }
                    if !state.abandoned.is_empty() {
                        for id in &state.abandoned {
                            if let Some(record) = state.live.get(id) {
                                if !record.abort_requested {
                                    tx.set_task(with_abort_mark(
                                        record,
                                        Some(TaskAbortReason::Restart),
                                    ))?;
                                }
                            }
                        }
                        *staged_abandoned
                            .lock()
                            .unwrap_or_else(PoisonError::into_inner) =
                            state.abandoned.iter().copied().collect();
                        return Ok(());
                    }
                }
                inner.load_scopes(Queued::Skip).await?;
                let (owned, records) = {
                    let state = inner.lock();
                    let records: Vec<AnyTaskRecord> = state.live.values().cloned().collect();
                    (state.owned_live(None), records)
                };
                // Taken once per pass, and only when some task is a candidate.
                let mut snapshot: Option<RegistrySnapshot> = None;
                for record in records {
                    {
                        let state = inner.lock();
                        if state.invocations.contains_key(&record.id)
                            || !state.waiting_on(&record, &owned).is_empty()
                        {
                            continue;
                        }
                    }
                    if record.state.status() == TaskStatus::Completing {
                        continue;
                    }
                    let mode = if record.abort_requested {
                        InvocationMode::Abort
                    } else {
                        InvocationMode::Run
                    };
                    // Work below an owner with cancellation intent waits for its cascade mark
                    // instead of running a phase; schedule the cascade, which may not have run yet.
                    if mode == InvocationMode::Run
                        && !record.background
                        && inner.lock().below_cancelled(parent_of(&record))
                    {
                        inner.lock().cascade_pending = true;
                        inner.schedule_reconcile();
                        continue;
                    }
                    let snapshot = snapshot
                        .get_or_insert_with(|| inner.registry.snapshot())
                        .clone();
                    match inner.resolve(&record, &snapshot) {
                        Resolution::Blocked(reason) => {
                            // An abandoned task waits for its definition, so its abort handler can
                            // clean up.
                            if mode == InvocationMode::Abort && record.abort_reason.is_none() {
                                let reason = reason.as_str().to_owned();
                                inner
                                    .terminate(&tx, &record, SchedulerOutcome::Orphaned { reason })
                                    .await?;
                            }
                        }
                        Resolution::Ready {
                            task,
                            record: resolved,
                            migrated,
                        } => {
                            if migrated || record.state.status() != TaskStatus::Running {
                                let checkpoint =
                                    resolved.state.checkpoint().cloned().unwrap_or_default();
                                tx.set_task(with_state(
                                    &resolved,
                                    TaskState::Running { checkpoint },
                                ))?;
                            }
                            // Registered on the line, so marks and later
                            // reservations see it and close joins it.
                            let invocation = inner.create_invocation(&record, mode);
                            staged.lock().unwrap_or_else(PoisonError::into_inner).push(
                                Reservation {
                                    invocation,
                                    task,
                                    snapshot,
                                },
                            );
                        }
                    }
                }
                Ok(())
            },
            &self.context,
            TransactionScope::default(),
        );
        let inner = self.arc();
        async move {
            let result = committed.await;
            let reservations =
                std::mem::take(&mut *reservations.lock().unwrap_or_else(PoisonError::into_inner));
            if let Err(error) = result {
                for reservation in &reservations {
                    let invocation = &reservation.invocation;
                    {
                        let mut state = inner.lock();
                        if state
                            .invocations
                            .get(&invocation.task_id)
                            .is_some_and(|registered| Arc::ptr_eq(registered, invocation))
                        {
                            state.invocations.remove(&invocation.task_id);
                        }
                    }
                    invocation.finish();
                }
                return Err(error);
            }
            // Marked, or already marked or gone: done with them. Reserve again, now seeing the
            // marks.
            let abandoned =
                std::mem::take(&mut *abandoned.lock().unwrap_or_else(PoisonError::into_inner));
            if !abandoned.is_empty() {
                let mut state = inner.lock();
                for id in &abandoned {
                    state.abandoned.shift_remove(id);
                }
                state.dirty = true;
            }
            Ok(reservations)
        }
    }

    /// Resolve the record's definition by kind, migrating an older stored
    /// version. A failed migration is remembered and reported.
    pub(super) fn resolve(
        &self,
        record: &AnyTaskRecord,
        snapshot: &RegistrySnapshot,
    ) -> Resolution {
        let fitted = {
            let state = self.lock();
            fit(&state, record, snapshot.task(&record.kind))
        };
        let task = match fitted {
            Fit::Blocked { reason, .. } => return Resolution::Blocked(reason),
            Fit::Task {
                task,
                migrates: false,
            } => {
                return Resolution::Ready {
                    task,
                    record: Box::new(record.clone()),
                    migrated: false,
                }
            }
            Fit::Task {
                task,
                migrates: true,
            } => task,
        };
        let checkpoint = record.state.checkpoint().cloned().unwrap_or_default();
        let migrated = task
            .definition()
            .migrate(&record.input, &checkpoint, record.version)
            .unwrap_or_else(|| Err(missing_migration(record, &task)));
        match migrated {
            Ok(Migrated { input, checkpoint }) => {
                let state = match &record.state {
                    TaskState::Pending { .. } => TaskState::Pending {
                        checkpoint: copy_json(&checkpoint),
                    },
                    TaskState::Running { .. } => TaskState::Running {
                        checkpoint: copy_json(&checkpoint),
                    },
                    TaskState::Waiting { on, policy, .. } => TaskState::Waiting {
                        checkpoint: copy_json(&checkpoint),
                        on: on.clone(),
                        policy: *policy,
                    },
                    TaskState::Completing { .. } | TaskState::Terminal { .. } => {
                        record.state.clone()
                    }
                };
                let migrated = AnyTaskRecord {
                    version: task.version(),
                    input: copy_json(&input),
                    state,
                    ..record.clone()
                };
                Resolution::Ready {
                    task,
                    record: Box::new(migrated),
                    migrated: true,
                }
            }
            Err(error) => {
                self.lock().failed_migrations.insert(
                    record.id,
                    FailedMigration {
                        task,
                        error: error.clone(),
                    },
                );
                self.report(error);
                Resolution::Blocked(TaskBlockedReason::MigrationFailed)
            }
        }
    }

    fn create_invocation(&self, record: &AnyTaskRecord, mode: InvocationMode) -> Arc<Invocation> {
        let invocation = Arc::new(Invocation::new(
            record.id,
            record.conversation_id,
            mode,
            &self.context,
        ));
        self.lock()
            .invocations
            .insert(record.id, Arc::clone(&invocation));
        invocation
    }
}
