//! Port of `test/harness-tasks-recovery.test.ts`: recovery across close and
//! reopen, crash recovery, blocked tasks, definition handover, and Harness
//! open failure. Shared helpers of the TS file live here; each TS `describe`
//! is one submodule.

mod blocked;
mod close_reopen;
mod crash;
mod handover;
mod open;

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::JsonValue;
use serde::{Deserialize, Serialize};

use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{aborted_with, completed, eventually};
use crate::harness::{Harness, RootOptions};
use crate::session::SessionResult;
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::tasks::{define_task, AnyTask, Migrated, TaskDefinition};
use crate::types::{Storage, TaskId, TaskOptions, TaskOwnership};

/// TS `sqlitePath()`: a fresh directory (removed when dropped, the TS
/// `afterEach`) and the database path inside it.
fn sqlite_path() -> (tempfile::TempDir, PathBuf) {
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-tasks-")
        .tempdir()
        .expect("create a temp dir");
    let path = directory.path().join("session.sqlite");
    (directory, path)
}

/// TS `openNodeSqliteStorage(path)`.
async fn sqlite(path: &Path) -> Arc<dyn Storage> {
    Arc::new(
        open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
            .await
            .expect("open the SQLite storage"),
    )
}

/// TS `createIn(harness, task)`: create `task` with `null` input in the root
/// conversation.
async fn create_in(harness: &Harness, task: &AnyTask) -> TaskId {
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .expect("root conversation");
    let definition = task.as_definition_ref();
    root.commit(
        move |tx| async move {
            tx.create_task(
                definition,
                JsonValue::Null,
                TaskOptions {
                    ownership: TaskOwnership::Conversation,
                    conversation_id: None,
                    background: None,
                    abandon_on_restart: None,
                },
            )
            .await
        },
        context(),
    )
    .await
    .expect("create the task")
}

/// Flush pending work until `check` holds (TS `eventually` over a
/// synchronous condition).
async fn until(mut check: impl FnMut() -> bool) {
    eventually(|| std::future::ready(check())).await;
}

/// TS `string[]` log shared with task handlers.
#[derive(Clone, Default)]
struct Log(Arc<Mutex<Vec<String>>>);

impl Log {
    fn push(&self, line: impl Into<String>) {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(line.into());
    }

    fn all(&self) -> Vec<String> {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    fn len(&self) -> usize {
        self.0.lock().unwrap_or_else(PoisonError::into_inner).len()
    }

    fn contains(&self, line: &str) -> bool {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .iter()
            .any(|entry| entry == line)
    }
}

/// TS `{ phase: "run" }`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "lowercase")]
enum Step {
    Run,
}

/// TS `versioned` migrate callback.
type VersionedMigrate =
    Box<dyn Fn(&JsonValue, &JsonValue, u64) -> SessionResult<Migrated<(), Step>> + Send + Sync>;

/// A versioned one-phase task that completes with `result`, optionally
/// migrating older records.
fn versioned(version: u64, result: &str, migrate: Option<VersionedMigrate>) -> AnyTask {
    let run_result = result.to_owned();
    let abort_result = result.to_owned();
    let mut definition = TaskDefinition::<(), Step, String, ()>::new(
        "test.versioned",
        version,
        |()| Ok(Step::Run),
        move |_task, runtime, cx| {
            let reason = abort_result.clone();
            async move {
                runtime
                    .commit(
                        move |_tx, _current| async move { Ok(Some(aborted_with(&reason))) },
                        &cx,
                    )
                    .await
            }
        },
    )
    .phase("run", move |_task, runtime, cx| {
        let result = run_result.clone();
        async move {
            runtime
                .commit(
                    move |_tx, _current| async move { Ok(Some(completed(result))) },
                    &cx,
                )
                .await
        }
    });
    if let Some(migrate) = migrate {
        definition = definition.migrate(migrate);
    }
    define_task(definition).erase()
}
