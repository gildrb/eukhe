//! Close, reopen, and continue where a task stopped.
//! Run from the workspace:
//!   cargo run -p eukhe-durable --example 13-recovery
use std::io::Write;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{to_json, JsonValue};
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{Extension, HarnessOptions};
use eukhe_durable::harness::{Harness, RootOptions};
use eukhe_durable::session::SessionResult;
use eukhe_durable::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use eukhe_durable::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use eukhe_durable::types::{TaskOptions, TaskOutcome, TaskOwnership};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use serde::{Deserialize, Serialize};
use tokio::sync::oneshot;

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TickerInput {
    to: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "lowercase")]
enum TickerState {
    Tick { n: u64 },
}

/// Lines the task prints. The task runs on the Harness's tokio tasks, so it
/// collects its lines here and `run` writes them to `out` in order.
type Printed = Arc<Mutex<Vec<String>>>;

/// TS `reachedTick`: armed during the first run, fired at tick 2.
type TickTwo = Arc<Mutex<Option<oneshot::Sender<()>>>>;

fn ticker_task(
    printed: &Printed,
    tick_two: &TickTwo,
) -> Task<TickerInput, TickerState, String, ()> {
    let printed = Arc::clone(printed);
    let tick_two = Arc::clone(tick_two);
    define_task(
        TaskDefinition::new(
            "example.ticker",
            1,
            |_: &TickerInput| Ok(TickerState::Tick { n: 1 }),
            |_task, runtime, task_context| async move {
                runtime
                    .commit(
                        |_tx, _current| async move {
                            Ok(Some(NextTaskState::Terminal {
                                outcome: TaskOutcome::Aborted {
                                    reason: None,
                                    result: None,
                                },
                            }))
                        },
                        &task_context,
                    )
                    .await
            },
        )
        .phase("tick", move |task, runtime, task_context| {
            let printed = Arc::clone(&printed);
            let tick_two = Arc::clone(&tick_two);
            async move {
                let TickerState::Tick { n } = task.checkpoint;
                // Save the intent before the effect. A memo keeps the first
                // value written under its name, so if the process dies after
                // printing but before the next checkpoint is saved, the rerun
                // sees the memo and does not print the same tick twice.
                let name = format!("printed-{n}");
                if runtime.memo::<bool>(&name, &task_context).await?.is_none() {
                    runtime.memo_or(&name, &true, &task_context).await?;
                    printed
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(format!("tick {n}"));
                }
                if n == 2 {
                    let armed = tick_two
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .take();
                    if let Some(reached) = armed {
                        // The receiver is alive until `run` closes the
                        // first Harness.
                        let _ = reached.send(());
                        // TS closes the Harness in the same turn of the event
                        // loop, before this phase's next commit runs. Tokio
                        // runs this phase in parallel with `run`, so wait for
                        // the close to signal the invocation; the commit
                        // below then rejects as TS's does.
                        runtime.signal().cancellation_token().cancelled().await;
                    }
                }
                // Save the outcome: the next tick, or the final result.
                let to = task.input.to;
                runtime
                    .commit(
                        move |_tx, _current| async move {
                            Ok(Some(if n == to {
                                NextTaskState::Terminal {
                                    outcome: TaskOutcome::Completed {
                                        result: format!("counted to {n}"),
                                    },
                                }
                            } else {
                                NextTaskState::Running {
                                    checkpoint: TickerState::Tick { n: n + 1 },
                                }
                            }))
                        },
                        &task_context,
                    )
                    .await?;
                // Wait a little between ticks. Closing the Harness cancels
                // this wait; the checkpoint saved above is where the next
                // Harness continues.
                runtime.sleep(runtime.now()? + 50.0, &task_context).await
            }
        }),
    )
}

async fn open(database_path: &Path, registry: &Registry) -> SessionResult<Harness> {
    let storage =
        open_native_sqlite_storage(database_path, NativeSqliteStorageOptions::default()).await?;
    Harness::open(
        Arc::new(storage),
        HarnessOptions::new(
            create_models(CreateModelsOptions::default()),
            Arc::new(registry.clone()),
        ),
        &BACKGROUND_CONTEXT,
    )
    .await
}

fn flush(out: &mut (dyn Write + Send), printed: &Printed) -> std::io::Result<()> {
    let lines = std::mem::take(&mut *printed.lock().unwrap_or_else(PoisonError::into_inner));
    for line in lines {
        writeln!(out, "{line}")?;
    }
    Ok(())
}

/// Runs the example, writing what the TS example prints to `out`.
///
/// # Errors
///
/// The first step that fails.
pub async fn run(
    out: &mut (dyn Write + Send),
    _args: &[String],
    _openai_api_key: Option<&str>,
) -> Result<(), BoxError> {
    let context = &*BACKGROUND_CONTEXT;

    // Everything a task needs to continue is in storage, so a new Harness
    // over the same storage picks up where the last one stopped. This
    // example keeps its storage in a SQLite file so it survives closing.
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-example-")
        .tempdir()?;
    let database_path = directory.path().join("session.sqlite");

    let printed = Printed::default();
    let tick_two = TickTwo::default();
    let ticker = ticker_task(&printed, &tick_two);
    let registry = create_registry();
    registry.install(define_extension(Extension {
        tasks: vec![ticker.erase()],
        ..Extension::named("ticker")
    }))?;

    // First run: start counting to 5, and close the Harness right after tick
    // 2 is printed, before its next checkpoint is saved. That is the same
    // situation as a crash between the effect and saving its outcome.
    let first_run = open(&database_path, &registry).await?;
    let definition = ticker.as_definition_ref();
    let input = to_json(&TickerInput { to: 5 })?;
    let ticker_id = first_run
        .root(RootOptions::default(), context)
        .await?
        .commit(
            move |tx| async move {
                tx.create_task(
                    definition,
                    input,
                    TaskOptions {
                        ownership: TaskOwnership::Conversation,
                        conversation_id: None,
                        background: None,
                        abandon_on_restart: None,
                    },
                )
                .await
            },
            context,
        )
        .await?;
    let (reached, reached_two) = oneshot::channel();
    *tick_two.lock().unwrap_or_else(PoisonError::into_inner) = Some(reached);
    first_run.resume()?;
    reached_two.await?;
    first_run.close(context).await?;
    flush(out, &printed)?;

    // Read the saved record through a Harness that never resumes, so nothing
    // runs.
    let reader = open(&database_path, &registry).await?;
    let saved = reader
        .get_task(ticker_id, context)
        .await?
        .ok_or("the ticker task is saved")?;
    reader.close(context).await?;
    let memos = saved
        .memos
        .clone()
        .map_or(JsonValue::Null, JsonValue::Object);
    writeln!(
        out,
        "closed; saved checkpoint: {} memos: {memos}",
        to_json(&saved.state)?
    )?;

    // Second run: nothing to restart by hand. Waiting for the unfinished task
    // enables scheduling and continues it. Tick 2 runs again because its
    // outcome was never saved, but its memo says it was already printed.
    let second_run = open(&database_path, &registry).await?;
    let counted = second_run.wait_for_task(ticker_id, context).await?;
    flush(out, &printed)?;
    writeln!(out, "after reopen: {}", to_json(&counted.outcome)?)?;
    second_run.close(context).await?;
    directory.close()?;
    Ok(())
}
