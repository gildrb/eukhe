//! TS `describe("blocked tasks")`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{from_json, JsonValue};

use super::{create_in, sqlite, sqlite_path, until, versioned, Step};
use crate::documents::{DocDefinition, TaskDoc};
use crate::harness::tests::support::{
    add_task, add_tool, context, create_registry, tool_described,
};
use crate::harness::tests::task_support::{aborted, deferred, flush, open_tasks, OpenTasksOptions};
use crate::harness::{RootOptions, TaskAbortResult};
use crate::session::tests::support::json;
use crate::session::SessionError;
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, Migrated, TaskDefinition};
use crate::types::{TaskOptions, TaskOutcome, TaskOwnership, TaskState, TaskStatus};

const ORPHAN_SCRATCH: TaskDoc<JsonValue> = match TaskDoc::define(DocDefinition {
    kind: "test.orphan-scratch",
    version: 1,
    initial: || json(r#"{"n":0}"#),
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

fn memory() -> Arc<dyn crate::types::Storage> {
    Arc::new(MemoryStorage::new())
}

fn completed_with(result: &str) -> TaskOutcome {
    TaskOutcome::Completed {
        result: JsonValue::from(result),
    }
}

fn missing_task() -> TaskState {
    TaskState::Terminal {
        outcome: TaskOutcome::Orphaned {
            reason: "missing_task".to_owned(),
        },
    }
}

#[tokio::test]
async fn keeps_a_task_with_a_missing_definition_pending_and_live_for_idle_waits_until_registration()
{
    let v1 = versioned(1, "v1", None);
    let opened = open_tasks(memory(), &[], OpenTasksOptions::default()).await;
    let harness = opened.harness;
    let id = create_in(&harness, &v1).await;
    harness.resume().unwrap();
    flush().await;
    assert_eq!(
        harness
            .get_task(id, context())
            .await
            .unwrap()
            .map(|record| record.state.status()),
        Some(TaskStatus::Pending)
    );
    let idle = tokio::spawn(harness.wait_for_idle(context()));
    flush().await;
    add_task(&opened.registry, v1, None).unwrap();
    idle.await.unwrap().unwrap();
    assert_eq!(
        harness
            .get_task(id, context())
            .await
            .unwrap()
            .map(|record| record.state),
        Some(TaskState::Terminal {
            outcome: completed_with("v1"),
        })
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_a_task_stored_by_a_newer_version_pending_until_a_fitting_definition_is_registered() {
    let registry = create_registry();
    add_task(&registry, versioned(1, "old", None), None).unwrap();
    let harness = open_tasks(
        memory(),
        &[],
        OpenTasksOptions {
            registry: Some(registry.clone()),
            ..OpenTasksOptions::default()
        },
    )
    .await
    .harness;
    let id = create_in(&harness, &versioned(2, "new", None)).await;
    harness.resume().unwrap();
    flush().await;
    assert_eq!(
        harness
            .get_task(id, context())
            .await
            .unwrap()
            .map(|record| record.state.status()),
        Some(TaskStatus::Pending)
    );
    // The same extension name replaces the old one in place.
    add_task(&registry, versioned(2, "new", None), None).unwrap();
    assert_eq!(
        harness.wait_for_task(id, context()).await.unwrap().outcome,
        completed_with("new")
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn migrates_at_reservation_leaves_the_record_unchanged_when_migration_fails_and_retries_only_for_a_new_definition(
) {
    let (_directory, path) = sqlite_path();
    let opened = open_tasks(sqlite(&path).await, &[], OpenTasksOptions::default()).await;
    let id = create_in(&opened.harness, &versioned(1, "v1", None)).await;
    opened.harness.close(context()).await.unwrap();

    let registry = create_registry();
    let failures = Arc::new(AtomicUsize::new(0));
    let failing = Arc::clone(&failures);
    add_task(
        &registry,
        versioned(
            2,
            "v2",
            Some(Box::new(move |_, _, _| {
                failing.fetch_add(1, Ordering::SeqCst);
                Err(SessionError::error("cannot migrate"))
            })),
        ),
        None,
    )
    .unwrap();
    let opened = open_tasks(
        sqlite(&path).await,
        &[],
        OpenTasksOptions {
            registry: Some(registry.clone()),
            ..OpenTasksOptions::default()
        },
    )
    .await;
    opened.harness.resume().unwrap();
    until(|| opened.reports.len() == 1).await;
    // An unrelated registry change wakes the scheduler without retrying the same failed definition.
    add_tool(&registry, tool_described("unrelated", "unrelated"), None).unwrap();
    flush().await;
    assert_eq!(failures.load(Ordering::SeqCst), 1);
    let reports = opened.reports.all();
    assert_eq!(reports.len(), 1);
    assert!(reports[0].to_string().contains("cannot migrate"));
    let record = opened
        .harness
        .get_task(id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(record.version, 1);
    assert_eq!(
        record.state,
        TaskState::Pending {
            checkpoint: json(r#"{"phase":"run"}"#),
        }
    );

    let migrations = Arc::new(Mutex::new(Vec::new()));
    let recorded = Arc::clone(&migrations);
    // The same extension name replaces the old one in place.
    add_task(
        &registry,
        versioned(
            2,
            "v2",
            Some(Box::new(move |_input, checkpoint, from_version| {
                recorded
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(from_version);
                Ok(Migrated {
                    input: (),
                    checkpoint: from_json::<Step>(checkpoint)?,
                })
            })),
        ),
        None,
    )
    .unwrap();
    let receipt = opened.harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(receipt.version, 2);
    assert_eq!(receipt.outcome, completed_with("v2"));
    assert_eq!(
        *migrations.lock().unwrap_or_else(PoisonError::into_inner),
        [1]
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn blocks_an_older_record_whose_newer_definition_has_no_migration() {
    let (_directory, path) = sqlite_path();
    let opened = open_tasks(sqlite(&path).await, &[], OpenTasksOptions::default()).await;
    let id = create_in(&opened.harness, &versioned(1, "v1", None)).await;
    opened.harness.close(context()).await.unwrap();
    let opened = open_tasks(
        sqlite(&path).await,
        &[versioned(2, "v2", None)],
        OpenTasksOptions::default(),
    )
    .await;
    opened.harness.resume().unwrap();
    until(|| opened.reports.len() == 1).await;
    assert!(opened.reports.all()[0]
        .to_string()
        .contains("has no migration from 1"));
    let record = opened
        .harness
        .get_task(id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(record.version, 1);
    assert_eq!(record.state.status(), TaskStatus::Pending);
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn settles_an_aborted_blocked_task_as_orphaned_and_retires_its_documents() {
    let harness = open_tasks(memory(), &[], OpenTasksOptions::default())
        .await
        .harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let definition = versioned(1, "x", None).as_definition_ref();
    let id = root
        .commit(
            move |tx| async move {
                let created = tx
                    .create_task(
                        definition,
                        JsonValue::Null,
                        TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: None,
                            background: None,
                            abandon_on_restart: None,
                        },
                    )
                    .await?;
                tx.doc(&ORPHAN_SCRATCH, created)
                    .await?
                    .set("n", json("1"))?;
                Ok(created)
            },
            context(),
        )
        .await
        .unwrap();
    // Before resume: the marking commit settles the blocked task directly.
    assert_eq!(
        harness.abort_task(id, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_eq!(
        harness
            .get_task(id, context())
            .await
            .unwrap()
            .map(|record| record.state),
        Some(missing_task())
    );
    assert!(harness
        .snapshot(&ORPHAN_SCRATCH, id, context())
        .await
        .unwrap()
        .is_none());
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn orphans_a_marked_task_whose_definition_disappeared_while_its_run_was_active() {
    let reached = deferred::<()>();
    let running = {
        let reached = reached.clone();
        define_task(
            TaskDefinition::<(), Step, (), ()>::new(
                "test.vanishing",
                1,
                |()| Ok(Step::Run),
                |_task, _runtime, _cx| async { Err(SessionError::error("must not run")) },
            )
            .phase("run", move |_task, runtime, _cx| {
                let reached = reached.clone();
                async move {
                    reached.resolve(());
                    Err(aborted(&runtime.signal()).await)
                }
            }),
        )
        .erase()
    };
    let registry = create_registry();
    let registration = add_task(&registry, running.clone(), None).unwrap();
    let harness = open_tasks(
        memory(),
        &[],
        OpenTasksOptions {
            registry: Some(registry),
            ..OpenTasksOptions::default()
        },
    )
    .await
    .harness;
    let id = create_in(&harness, &running).await;
    harness.resume().unwrap();
    reached.wait().await;
    registration.dispose();
    // An active run means the mark does not orphan directly; the scheduler orphans once the run has ended.
    assert_eq!(
        harness.abort_task(id, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    assert_eq!(
        harness.wait_for_task(id, context()).await.unwrap().outcome,
        TaskOutcome::Orphaned {
            reason: "missing_task".to_owned(),
        }
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn orphans_a_reopened_abort_marked_task_without_a_definition_once_scheduling_resumes() {
    let (_directory, path) = sqlite_path();
    let opened = open_tasks(
        sqlite(&path).await,
        &[versioned(1, "x", None)],
        OpenTasksOptions::default(),
    )
    .await;
    let id = create_in(&opened.harness, &versioned(1, "x", None)).await;
    assert_eq!(
        opened.harness.abort_task(id, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    opened.harness.close(context()).await.unwrap();

    let opened = open_tasks(sqlite(&path).await, &[], OpenTasksOptions::default()).await;
    let record = opened
        .harness
        .get_task(id, context())
        .await
        .unwrap()
        .unwrap();
    assert!(record.abort_requested);
    assert_eq!(record.state.status(), TaskStatus::Pending);
    let idle = opened.harness.wait_for_idle(context());
    opened.harness.resume().unwrap();
    idle.await.unwrap();
    assert_eq!(
        opened
            .harness
            .get_task(id, context())
            .await
            .unwrap()
            .map(|record| record.state),
        Some(missing_task())
    );
    opened.harness.close(context()).await.unwrap();
}
