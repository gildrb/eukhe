//! The lifecycle rules of a task (spec §5.1-§5.5) over scheduler records.
//! Every transition the scheduler writes, the resume of a stored state, the
//! failFast join of a wait and every abort mark run as the compiled core
//! (`eukhe_bend::rules::task_life`; `bend/task_life.bend`,
//! `laws/task_life.bend`; `docs/state.md` section S2).
//!
//! The core never reads a payload: a state goes out with handle
//! [`CURRENT`] for the record's own checkpoint or outcome, a transition
//! with [`GIVEN`] for the one it brings, and the reply's handles pick the
//! payloads back. A waiting state's awaited tasks travel with its
//! checkpoint.

use eukhe_bend::rules::task_life::{
    self as life, Event, Mark, Member, Next, Outcome, Refusal, Row,
};
use eukhe_bend::{expect_core, Entry};
use eukhe_chord::json::JsonValue;

use super::runtime::status_name;
use crate::session::{SessionError, SessionResult};
use crate::types::{
    AnyTaskRecord, JoinPolicy, TaskAbortReason, TaskOutcome, TaskOutcomeStatus, TaskState,
};

/// The handle of the record's own checkpoint or outcome.
const CURRENT: u64 = 0;
/// The handle of the checkpoint or outcome a transition brings.
const GIVEN: u64 = 1;

/// Whether ordinary owned work below a task is live, so a decided outcome
/// holds as `completing`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum OwnedWork {
    Live,
    Gone,
}

/// A stored state after a restart.
#[derive(Debug, PartialEq)]
pub(super) struct Resumed {
    /// The state the new Harness schedules.
    pub(super) state: TaskState,
    /// A failFast wait: check its awaited tasks again.
    pub(super) check_fail_fast: bool,
}

/// What a transition brings besides the record: nothing, the state a
/// running task commits, or an outcome the scheduler decided.
enum Given<'a> {
    Nothing,
    Next(&'a TaskState),
    Outcome(&'a TaskOutcome),
}

/// Where a handle of the reply points.
enum Source<'a> {
    State(&'a TaskState),
    Outcome(&'a TaskOutcome),
}

fn policy(policy: JoinPolicy) -> life::Policy {
    match policy {
        JoinPolicy::FailFast => life::Policy::FailFast,
        JoinPolicy::AllSettled => life::Policy::AllSettled,
    }
}

fn outcome(outcome: &TaskOutcome, payload: u64) -> Outcome {
    let status = match outcome.status() {
        TaskOutcomeStatus::Completed => life::Status::Completed,
        TaskOutcomeStatus::Failed => life::Status::Failed,
        TaskOutcomeStatus::Aborted => life::Status::Aborted,
        TaskOutcomeStatus::Orphaned => life::Status::Orphaned,
        TaskOutcomeStatus::Faulted => life::Status::Faulted,
    };
    Outcome { status, payload }
}

/// A state as the core reads it, its payload named by `handle`.
fn model(state: &TaskState, handle: u64) -> life::State {
    match state {
        TaskState::Pending { .. } => life::State::Pending { checkpoint: handle },
        TaskState::Running { .. } => life::State::Running { checkpoint: handle },
        TaskState::Waiting { policy: p, .. } => life::State::Waiting {
            checkpoint: handle,
            policy: policy(*p),
        },
        TaskState::Completing { outcome: o } => life::State::Completing {
            outcome: outcome(o, handle),
        },
        TaskState::Terminal { outcome: o } => life::State::Terminal {
            outcome: outcome(o, handle),
        },
    }
}

fn unknown(handle: u64) -> SessionError {
    SessionError::error(format!(
        "task_life: the core answered a payload handle {handle} it was not given"
    ))
}

fn source<'a>(handle: u64, current: &'a TaskState, given: &Given<'a>) -> SessionResult<Source<'a>> {
    match (handle, given) {
        (CURRENT, _) => Ok(Source::State(current)),
        (GIVEN, Given::Next(next)) => Ok(Source::State(next)),
        (GIVEN, Given::Outcome(outcome)) => Ok(Source::Outcome(outcome)),
        (_, Given::Nothing | Given::Next(_) | Given::Outcome(_)) => Err(unknown(handle)),
    }
}

fn checkpoint(handle: u64, current: &TaskState, given: &Given<'_>) -> SessionResult<JsonValue> {
    match source(handle, current, given)? {
        Source::State(state) => state.checkpoint().cloned().ok_or_else(|| unknown(handle)),
        Source::Outcome(_) => Err(unknown(handle)),
    }
}

fn held(handle: u64, current: &TaskState, given: &Given<'_>) -> SessionResult<TaskOutcome> {
    match source(handle, current, given)? {
        Source::State(state) => state.outcome().cloned().ok_or_else(|| unknown(handle)),
        Source::Outcome(outcome) => Ok(outcome.clone()),
    }
}

/// The record state the core's answer names, its payloads picked by handle.
fn realize(state: life::State, current: &TaskState, given: &Given<'_>) -> SessionResult<TaskState> {
    Ok(match state {
        life::State::Pending { checkpoint: c } => TaskState::Pending {
            checkpoint: checkpoint(c, current, given)?,
        },
        life::State::Running { checkpoint: c } => TaskState::Running {
            checkpoint: checkpoint(c, current, given)?,
        },
        life::State::Waiting {
            checkpoint: c,
            policy: p,
        } => match source(c, current, given)? {
            Source::State(TaskState::Waiting { checkpoint, on, .. }) => TaskState::Waiting {
                checkpoint: checkpoint.clone(),
                on: on.clone(),
                policy: match p {
                    life::Policy::FailFast => JoinPolicy::FailFast,
                    life::Policy::AllSettled => JoinPolicy::AllSettled,
                },
            },
            Source::State(
                TaskState::Pending { .. }
                | TaskState::Running { .. }
                | TaskState::Completing { .. }
                | TaskState::Terminal { .. },
            )
            | Source::Outcome(_) => return Err(unknown(c)),
        },
        life::State::Completing { outcome: o } => TaskState::Completing {
            outcome: held(o.payload, current, given)?,
        },
        life::State::Terminal { outcome: o } => TaskState::Terminal {
            outcome: held(o.payload, current, given)?,
        },
    })
}

fn step(record: &AnyTaskRecord, event: Event, given: &Given<'_>) -> SessionResult<TaskState> {
    let stepped = expect_core(
        Entry::TaskLife,
        life::step(model(&record.state, CURRENT), event),
    );
    let id = record.id;
    match stepped {
        Ok(state) => realize(state, &record.state, given),
        Err(refusal) => Err(SessionError::error(match refusal {
            Refusal::Ended => format!("Task {id} is terminal"),
            Refusal::Held => format!("Task {id} is completing"),
            Refusal::NotRunning => format!("Task {id} is not running"),
            Refusal::NotHeld => format!("Task {id} holds no outcome"),
        })),
    }
}

fn owned_live(owned: OwnedWork) -> bool {
    match owned {
        OwnedWork::Live => true,
        OwnedWork::Gone => false,
    }
}

/// The state a reservation writes: a pending, running or waiting task runs
/// at its checkpoint.
///
/// # Errors
///
/// A held or terminal task.
pub(super) fn reserve(record: &AnyTaskRecord) -> SessionResult<TaskState> {
    step(record, Event::Reserve, &Given::Nothing)
}

/// A running task handed back to pending at its checkpoint, for a
/// replacement definition.
///
/// # Errors
///
/// A task that is not running.
pub(super) fn requeue(record: &AnyTaskRecord) -> SessionResult<TaskState> {
    step(record, Event::Requeue, &Given::Nothing)
}

/// The state a running task's commit of `next` writes: a decided outcome
/// holds as `completing` while owned work is live.
///
/// # Errors
///
/// A task that is not running, or a `next` a runtime never commits
/// (pending, completing).
pub(super) fn commit(
    record: &AnyTaskRecord,
    next: &TaskState,
    owned: OwnedWork,
) -> SessionResult<TaskState> {
    let committed = match next {
        TaskState::Running { .. } => Next::Running { checkpoint: GIVEN },
        TaskState::Waiting { policy: p, .. } => Next::Waiting {
            checkpoint: GIVEN,
            policy: policy(*p),
        },
        TaskState::Terminal { outcome: o } => Next::Ended {
            outcome: outcome(o, GIVEN),
        },
        TaskState::Pending { .. } | TaskState::Completing { .. } => {
            return Err(SessionError::error(format!(
                "Task {} cannot commit a {} state",
                record.id,
                status_name(next.status())
            )));
        }
    };
    step(
        record,
        Event::Commit {
            next: committed,
            owned_live: owned_live(owned),
        },
        &Given::Next(next),
    )
}

/// The state an outcome the scheduler decided writes for a live task that
/// is not held: `completing` while owned work is live, else terminal.
///
/// # Errors
///
/// A held or terminal task.
pub(super) fn settle(
    record: &AnyTaskRecord,
    decided: &TaskOutcome,
    owned: OwnedWork,
) -> SessionResult<TaskState> {
    step(
        record,
        Event::Settle {
            outcome: outcome(decided, GIVEN),
            owned_live: owned_live(owned),
        },
        &Given::Outcome(decided),
    )
}

/// A held outcome once its owned work is checked: still `completing` while
/// it is live, else terminal with the same outcome.
///
/// # Errors
///
/// A task that holds no outcome.
pub(super) fn finalize(record: &AnyTaskRecord, owned: OwnedWork) -> SessionResult<TaskState> {
    step(
        record,
        Event::Finalize {
            owned_live: owned_live(owned),
        },
        &Given::Nothing,
    )
}

/// A stored state when a new Harness opens: a running task is pending at
/// its checkpoint, a failFast wait is checked again, nothing else changes.
///
/// # Errors
///
/// Only an answer that names a payload it was not given (an inconsistent
/// build).
pub(super) fn resume(record: &AnyTaskRecord) -> SessionResult<Resumed> {
    let resumed = expect_core(Entry::TaskLife, life::resume(model(&record.state, CURRENT)));
    Ok(Resumed {
        state: realize(resumed.state, &record.state, &Given::Nothing)?,
        check_fail_fast: resumed.check_fail_fast,
    })
}

/// The join of a `policy` wait over its awaited tasks, in order.
pub(super) fn join(policy_of: JoinPolicy, members: &[Member]) -> life::Join {
    expect_core(Entry::TaskLife, life::join(policy(policy_of), members))
}

/// The abort mark of a record.
pub(super) fn mark_of(record: &AnyTaskRecord) -> Mark {
    match (record.abort_requested, record.abort_reason) {
        (false, None | Some(TaskAbortReason::Restart)) => Mark::Clear,
        (true, Some(TaskAbortReason::Restart)) => Mark::Restart,
        (true, None) => Mark::Request,
    }
}

/// The record with `mark`: `Restart` for an abandonment, `Request` for an
/// abort request, which replaces `Restart`.
pub(super) fn with_mark(record: &AnyTaskRecord, mark: Mark) -> AnyTaskRecord {
    let (abort_requested, abort_reason) = match mark {
        Mark::Clear => (false, None),
        Mark::Restart => (true, Some(TaskAbortReason::Restart)),
        Mark::Request => (true, None),
    };
    AnyTaskRecord {
        abort_requested,
        abort_reason,
        ..record.clone()
    }
}

/// The stronger of `mark` and `by`.
pub(super) fn merge(mark: Mark, by: Mark) -> Mark {
    expect_core(Entry::TaskLife, life::merge(mark, by))
}

/// The record marked with `by` merged into its mark, or `None` when its mark
/// already holds.
pub(super) fn marked(record: &AnyTaskRecord, by: Mark) -> Option<AnyTaskRecord> {
    let mark = mark_of(record);
    let next = merge(mark, by);
    (next != mark).then(|| with_mark(record, next))
}

/// The mark of each task an owner's walk reached, in order (`rows`): a
/// live foreground task below an owner with cancellation intent takes the
/// owner's reason; every other task keeps its mark.
pub(super) fn cascade(owner: &AnyTaskRecord, rows: &[Row]) -> Vec<Mark> {
    expect_core(
        Entry::TaskLife,
        life::cascade(model(&owner.state, CURRENT), mark_of(owner), rows),
    )
}

#[cfg(test)]
mod tests {
    use eukhe_bend::rules::task_life::{Join, Mark, Member, Row};
    use eukhe_chord::json::JsonValue;
    use serde_json::json;

    use super::{
        cascade, commit, finalize, join, marked, requeue, reserve, resume, settle, with_mark,
        OwnedWork, Resumed,
    };
    use crate::types::{
        AnyTaskRecord, ConversationId, JoinPolicy, TaskId, TaskOutcome, TaskOutcomeError, TaskState,
    };

    fn phase(name: &str) -> JsonValue {
        JsonValue::from(json!({ "phase": name }))
    }

    fn record(state: TaskState) -> AnyTaskRecord {
        AnyTaskRecord {
            id: TaskId::from_number(7),
            conversation_id: ConversationId::from_number(1),
            kind: "k".to_owned(),
            version: 1,
            input: JsonValue::Null,
            owner: None,
            background: false,
            abort_requested: false,
            abort_reason: None,
            abandon_on_restart: false,
            state,
            memos: None,
            started_at: None,
            ended_at: None,
        }
    }

    fn done() -> TaskOutcome {
        TaskOutcome::Completed {
            result: JsonValue::from(json!(42)),
        }
    }

    fn faulted() -> TaskOutcome {
        TaskOutcome::Faulted {
            error: TaskOutcomeError {
                message: "boom".to_owned(),
                detail: None,
            },
        }
    }

    fn waiting(policy: JoinPolicy) -> TaskState {
        TaskState::Waiting {
            checkpoint: phase("wait"),
            on: vec![TaskId::from_number(8)],
            policy,
        }
    }

    fn running(name: &str) -> TaskState {
        TaskState::Running {
            checkpoint: phase(name),
        }
    }

    #[test]
    fn a_reservation_runs_a_waiting_task_at_its_checkpoint_and_refuses_a_held_one() {
        assert_eq!(
            reserve(&record(waiting(JoinPolicy::AllSettled))).unwrap(),
            running("wait")
        );
        assert_eq!(
            reserve(&record(TaskState::Completing { outcome: done() }))
                .unwrap_err()
                .to_string(),
            "Task 7 is completing"
        );
    }

    #[test]
    fn a_handover_puts_a_running_task_back_at_its_own_checkpoint() {
        assert_eq!(
            requeue(&record(running("a"))).unwrap(),
            TaskState::Pending {
                checkpoint: phase("a")
            }
        );
        assert_eq!(
            requeue(&record(waiting(JoinPolicy::FailFast)))
                .unwrap_err()
                .to_string(),
            "Task 7 is not running"
        );
    }

    #[test]
    fn a_commit_holds_an_outcome_while_owned_work_lives_and_keeps_a_wait() {
        let current = record(running("a"));
        let ended = TaskState::Terminal { outcome: done() };
        assert_eq!(
            [
                commit(&current, &ended, OwnedWork::Live).unwrap(),
                commit(&current, &ended, OwnedWork::Gone).unwrap(),
                commit(&current, &waiting(JoinPolicy::FailFast), OwnedWork::Gone).unwrap(),
            ],
            [
                TaskState::Completing { outcome: done() },
                ended.clone(),
                waiting(JoinPolicy::FailFast),
            ]
        );
        assert_eq!(
            commit(
                &record(waiting(JoinPolicy::AllSettled)),
                &ended,
                OwnedWork::Gone
            )
            .unwrap_err()
            .to_string(),
            "Task 7 is not running"
        );
    }

    #[test]
    fn a_scheduler_outcome_settles_a_live_task_and_never_a_terminal_one() {
        assert_eq!(
            [
                settle(
                    &record(waiting(JoinPolicy::FailFast)),
                    &faulted(),
                    OwnedWork::Gone
                )
                .unwrap(),
                settle(&record(running("a")), &faulted(), OwnedWork::Live).unwrap(),
            ],
            [
                TaskState::Terminal { outcome: faulted() },
                TaskState::Completing { outcome: faulted() },
            ]
        );
        assert_eq!(
            settle(
                &record(TaskState::Terminal { outcome: done() }),
                &faulted(),
                OwnedWork::Gone
            )
            .unwrap_err()
            .to_string(),
            "Task 7 is terminal"
        );
    }

    #[test]
    fn finalization_keeps_the_held_outcome() {
        let held = record(TaskState::Completing { outcome: faulted() });
        assert_eq!(
            [
                finalize(&held, OwnedWork::Live).unwrap(),
                finalize(&held, OwnedWork::Gone).unwrap(),
            ],
            [
                TaskState::Completing { outcome: faulted() },
                TaskState::Terminal { outcome: faulted() },
            ]
        );
    }

    #[test]
    fn resume_requeues_a_running_task_and_checks_a_fail_fast_wait() {
        assert_eq!(
            [
                resume(&record(running("a"))).unwrap(),
                resume(&record(waiting(JoinPolicy::FailFast))).unwrap(),
                resume(&record(waiting(JoinPolicy::AllSettled))).unwrap(),
            ],
            [
                Resumed {
                    state: TaskState::Pending {
                        checkpoint: phase("a")
                    },
                    check_fail_fast: false,
                },
                Resumed {
                    state: waiting(JoinPolicy::FailFast),
                    check_fail_fast: true,
                },
                Resumed {
                    state: waiting(JoinPolicy::AllSettled),
                    check_fail_fast: false,
                },
            ]
        );
    }

    #[test]
    fn a_fail_fast_join_aborts_the_live_tasks_that_did_not_fail() {
        let members = [
            Member {
                live: true,
                failed: false,
            },
            Member {
                live: false,
                failed: true,
            },
            Member {
                live: true,
                failed: true,
            },
        ];
        assert_eq!(
            [
                join(JoinPolicy::FailFast, &members),
                join(JoinPolicy::AllSettled, &members),
            ],
            [
                Join {
                    ready: false,
                    abort: vec![true, false, false],
                },
                Join {
                    ready: false,
                    abort: vec![false, false, false],
                },
            ]
        );
    }

    #[test]
    fn a_request_replaces_a_restart_mark_and_never_the_reverse() {
        let restart = with_mark(&record(running("a")), Mark::Restart);
        let request = with_mark(&record(running("a")), Mark::Request);
        assert_eq!(
            [
                marked(&restart, Mark::Request),
                marked(&request, Mark::Restart),
                marked(&record(running("a")), Mark::Restart),
            ],
            [Some(request), None, Some(restart)]
        );
    }

    #[test]
    fn a_cascade_marks_only_the_live_foreground_tasks_below_an_owner_with_intent() {
        let abandoned = with_mark(&record(running("a")), Mark::Restart);
        let row = |live, background, mark| Row {
            live,
            background,
            mark,
        };
        let rows = [
            row(true, false, Mark::Clear),
            row(true, true, Mark::Clear),
            row(false, false, Mark::Clear),
            row(true, false, Mark::Request),
        ];
        assert_eq!(
            [
                cascade(&abandoned, &rows),
                cascade(&record(running("a")), &rows),
            ],
            [
                vec![Mark::Restart, Mark::Clear, Mark::Clear, Mark::Request],
                vec![Mark::Clear, Mark::Clear, Mark::Clear, Mark::Request],
            ]
        );
    }
}
