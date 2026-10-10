//! Port of `test/harness-inspect.test.ts`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::JsonValue;
use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;

use super::chat_support::{chat_setup, open_chat, unanswered, wait_for, OpenChat};
use super::support::context;
use super::task_support::{
    completed, deferred, eventually, open_tasks, Deferred, OpenTasksOptions,
};
use crate::harness::types::{
    ConversationCreateOptions, SchedulingState, TaskInspection, TaskInspectionState,
    WriteSubmissionDraft,
};
use crate::harness::RootOptions;
use crate::session::{SessionError, SessionResult};
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, Migrated, NextTaskState, Task, TaskDefinition};
use crate::types::{
    ConversationOwnership, EntryDraft, JoinPolicy, TaskId, TaskOptions, TaskOwnership,
};

type JsonTask = Task<JsonValue, JsonValue, JsonValue, ()>;

type Migrate = Arc<dyn Fn() -> SessionResult<()> + Send + Sync>;

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn run_checkpoint() -> JsonValue {
    json(r#"{"phase":"run"}"#)
}

/// A one-phase task that completes once `gate` resolves; `migrate` runs when an older stored version migrates.
fn task(name: &str, version: u64, gate: Option<Deferred>, migrate: Option<Migrate>) -> JsonTask {
    let definition = TaskDefinition::new(
        name,
        version,
        |_: &JsonValue| Ok(run_checkpoint()),
        |_, _, _| async { Ok(()) },
    )
    .phase("run", move |_, runtime, cx| {
        let gate = gate.clone();
        async move {
            if let Some(gate) = gate {
                gate.wait().await;
            }
            runtime
                .commit(|_, _| async { Ok(Some(completed(JsonValue::Null))) }, &cx)
                .await
        }
    });
    let definition = match migrate {
        None => definition,
        Some(migrate) => definition.migrate(move |_, _, _| {
            migrate()?;
            Ok(Migrated {
                input: JsonValue::Null,
                checkpoint: run_checkpoint(),
            })
        }),
    };
    define_task(definition)
}

/// The inspected state of task `id`, rendered for whole-value comparison
/// (`TaskInspectionState` holds errors and has no `PartialEq`).
fn state_of(tasks: &[TaskInspection], id: TaskId) -> Option<String> {
    tasks
        .iter()
        .find(|entry| entry.record.id == id)
        .map(|entry| describe(&entry.state))
}

fn describe(state: &TaskInspectionState) -> String {
    match state {
        TaskInspectionState::Running => "running".to_owned(),
        TaskInspectionState::Ready { migrates } => format!("ready migrates={migrates}"),
        TaskInspectionState::Waiting { on } => format!("waiting on={on:?}"),
        TaskInspectionState::Completing => "completing".to_owned(),
        TaskInspectionState::Blocked { reason, error } => format!(
            "blocked reason={} error={:?}",
            reason.as_str(),
            error.as_ref().map(ToString::to_string)
        ),
    }
}

fn kind_of(state: &TaskInspectionState) -> &'static str {
    match state {
        TaskInspectionState::Running => "running",
        TaskInspectionState::Ready { .. } => "ready",
        TaskInspectionState::Waiting { .. } => "waiting",
        TaskInspectionState::Completing => "completing",
        TaskInspectionState::Blocked { .. } => "blocked",
    }
}

fn conversation_owned() -> TaskOptions {
    TaskOptions {
        ownership: TaskOwnership::Conversation,
        conversation_id: None,
        background: None,
        abandon_on_restart: None,
    }
}

#[derive(Debug, Clone, Copy)]
struct Ids {
    gate: TaskId,
    dependent: TaskId,
    migrating: TaskId,
    no_migration: TaskId,
    failing: TaskId,
    too_old: TaskId,
    missing: TaskId,
}

// Harness.inspect()

#[tokio::test(flavor = "multi_thread")]
#[allow(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn derives_every_live_tasks_state_without_running_task_code() {
    let gate: Deferred = deferred();
    let gate_task = task("test.gate", 1, Some(gate.clone()), None);
    let gate_id: Arc<Mutex<Option<TaskId>>> = Arc::default();
    let awaited = Arc::clone(&gate_id);
    let dependent: JsonTask = define_task(
        TaskDefinition::new(
            "test.dependent",
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"wait"}"#)),
            |_, _, _| async { Ok(()) },
        )
        .phase("wait", move |_, runtime, cx| {
            let gate_id = awaited
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .expect("the gate was created");
            async move {
                let checkpoint = json(r#"{"phase":"done"}"#);
                runtime
                    .commit(
                        move |_, _| async move {
                            Ok(Some(NextTaskState::Waiting {
                                checkpoint,
                                on: vec![gate_id],
                                policy: JoinPolicy::AllSettled,
                            }))
                        },
                        &cx,
                    )
                    .await
            }
        })
        .phase("done", |_, runtime, cx| async move {
            runtime
                .commit(|_, _| async { Ok(Some(completed(JsonValue::Null))) }, &cx)
                .await
        }),
    );
    let migrations = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&migrations);
    let registered = [
        gate_task.erase(),
        dependent.erase(),
        task(
            "test.migrating",
            2,
            None,
            Some(Arc::new(move || {
                counted.fetch_add(1, Ordering::SeqCst);
                Ok(())
            })),
        )
        .erase(),
        task("test.no-migration", 2, None, None).erase(),
        task(
            "test.failing",
            2,
            None,
            Some(Arc::new(|| Err(SessionError::error("cannot migrate")))),
        )
        .erase(),
        task("test.too-old", 1, None, None).erase(),
    ];
    let opened = open_tasks(
        Arc::new(MemoryStorage::new()),
        &registered,
        OpenTasksOptions::default(),
    )
    .await;
    let harness = opened.harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let (gate_definition, dependent_definition) = (
        gate_task.erase().as_definition_ref(),
        dependent.erase().as_definition_ref(),
    );
    let sink = Arc::clone(&gate_id);
    let ids = root
        .commit(
            move |tx| async move {
                let gate = tx
                    .create_task(gate_definition, JsonValue::Null, conversation_owned())
                    .await?;
                *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(gate);
                let stored = |name: &str, version| {
                    tx.create_task(
                        task(name, version, None, None).erase().as_definition_ref(),
                        JsonValue::Null,
                        conversation_owned(),
                    )
                };
                Ok(Ids {
                    gate,
                    dependent: tx
                        .create_task(dependent_definition, JsonValue::Null, conversation_owned())
                        .await?,
                    // Stored by definitions other than the registered ones.
                    migrating: stored("test.migrating", 1).await?,
                    no_migration: stored("test.no-migration", 1).await?,
                    failing: stored("test.failing", 1).await?,
                    too_old: stored("test.too-old", 2).await?,
                    missing: stored("test.missing", 1).await?,
                })
            },
            context(),
        )
        .await
        .unwrap();

    let paused = harness.inspect(context()).await.unwrap();
    assert_eq!(paused.scheduling, SchedulingState::Paused);
    let listed: Vec<_> = paused.tasks.iter().map(|entry| entry.record.id).collect();
    assert_eq!(
        listed,
        [
            ids.gate,
            ids.dependent,
            ids.migrating,
            ids.no_migration,
            ids.failing,
            ids.too_old,
            ids.missing,
        ]
    );
    let ready = |migrates: bool| Some(describe(&TaskInspectionState::Ready { migrates }));
    assert_eq!(state_of(&paused.tasks, ids.gate), ready(false));
    assert_eq!(state_of(&paused.tasks, ids.dependent), ready(false));
    assert_eq!(state_of(&paused.tasks, ids.migrating), ready(true));
    // A migration that was never tried is not run to find out.
    assert_eq!(state_of(&paused.tasks, ids.failing), ready(true));
    assert_eq!(
        state_of(&paused.tasks, ids.no_migration).as_deref(),
        Some(
            r#"blocked reason=migration_failed error=Some("Task test.no-migration version 2 has no migration from 1")"#
        )
    );
    assert_eq!(
        state_of(&paused.tasks, ids.too_old).as_deref(),
        Some("blocked reason=task_too_old error=None")
    );
    assert_eq!(
        state_of(&paused.tasks, ids.missing).as_deref(),
        Some("blocked reason=missing_task error=None")
    );
    assert_eq!(migrations.load(Ordering::SeqCst), 0);
    assert_eq!(
        harness.inspect(context()).await.unwrap().scheduling,
        SchedulingState::Paused
    );

    harness.resume().unwrap();
    eventually(|| {
        let migrations = Arc::clone(&migrations);
        async move { migrations.load(Ordering::SeqCst) == 1 }
    })
    .await;
    harness
        .wait_for_task(ids.migrating, context())
        .await
        .unwrap();
    let running = Arc::new(Mutex::new(harness.inspect(context()).await.unwrap()));
    wait_for(
        || {
            let (harness, running) = (harness.clone(), Arc::clone(&running));
            async move {
                let inspection = harness.inspect(context()).await.unwrap();
                let reached = state_of(&inspection.tasks, ids.gate).as_deref() == Some("running")
                    && inspection
                        .tasks
                        .iter()
                        .find(|entry| entry.record.id == ids.dependent)
                        .is_some_and(|entry| kind_of(&entry.state) == "waiting");
                *running.lock().unwrap_or_else(PoisonError::into_inner) = inspection;
                reached
            }
        },
        5000,
    )
    .await;
    let running = running
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(
        state_of(&running.tasks, ids.dependent),
        Some(describe(&TaskInspectionState::Waiting {
            on: vec![ids.gate]
        }))
    );
    assert_eq!(running.scheduling, SchedulingState::Running);
    assert_eq!(
        state_of(&running.tasks, ids.gate).as_deref(),
        Some("running")
    );
    assert_eq!(state_of(&running.tasks, ids.migrating), None);
    assert_eq!(
        state_of(&running.tasks, ids.failing).as_deref(),
        Some(r#"blocked reason=migration_failed error=Some("cannot migrate")"#)
    );

    gate.resolve(());
    harness
        .wait_for_task(ids.dependent, context())
        .await
        .unwrap();
    let settled = harness.inspect(context()).await.unwrap();
    let listed: Vec<_> = settled.tasks.iter().map(|entry| entry.record.id).collect();
    assert_eq!(
        listed,
        [ids.no_migration, ids.failing, ids.too_old, ids.missing]
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lists_unsettled_submissions() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let busy = unanswered();
    setup.faux.set_responses(vec![busy.step.clone()]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let other = harness
        .create_conversation(
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            context(),
        )
        .await
        .unwrap();
    other
        .submit(
            WriteSubmissionDraft {
                request_id: None,
                entry: EntryDraft::new("note"),
            },
            context(),
        )
        .await
        .unwrap();
    let input = root
        .submit(
            crate::harness::types::InputSubmissionDraft::new("hi"),
            context(),
        )
        .await
        .unwrap();
    busy.reached().await;

    let inspection = harness.inspect(context()).await.unwrap();
    assert_eq!(
        inspection.submissions,
        [input.status(context()).await.unwrap()]
    );
    let tasks: Vec<_> = inspection
        .tasks
        .iter()
        .map(|entry| (entry.record.kind.as_str(), kind_of(&entry.state)))
        .collect();
    assert_eq!(tasks, [("pi.generation", "running")]);
    harness.close(context()).await.unwrap();
}
