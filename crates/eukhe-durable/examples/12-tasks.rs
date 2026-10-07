//! Run a durable task.
//! Run from the workspace:
//!   cargo run -p eukhe-durable --example 12-tasks
use std::collections::HashMap;
use std::io::Write;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::to_json;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{Extension, HarnessOptions};
use eukhe_durable::harness::{Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use eukhe_durable::types::{TaskOptions, TaskOutcome, TaskOwnership};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use serde::{Deserialize, Serialize};

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaymentInput {
    amount: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "lowercase")]
enum PaymentState {
    Prepare,
    Charge { key: String },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Receipt {
    receipt: u64,
}

/// The fake payment service: charges keyed by idempotency key.
type Payments = Arc<Mutex<HashMap<String, u64>>>;

// A task is a small state machine. Its state, the checkpoint, is saved after
// every step, so after a crash the next open continues from the last saved
// step. The usual pattern: save what you are about to do, do it, then save
// the result. A crash between doing and saving reruns that step, so the step
// must be safe to repeat; here the fake payment service ignores a repeated
// key.
fn payment_task(payments: &Payments) -> Task<PaymentInput, PaymentState, Receipt, ()> {
    let payments = Arc::clone(payments);
    define_task(
        TaskDefinition::new(
            "example.payment",
            1,
            |_: &PaymentInput| Ok(PaymentState::Prepare),
            // Runs instead of the phases after harness.abort_task(); it
            // decides the outcome.
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
        // One handler per phase. Each must save progress through
        // runtime.commit(): its callback returns the next checkpoint or the
        // final outcome, and that state is saved in the same commit as
        // everything else the callback wrote.
        .phase("prepare", |task, runtime, task_context| async move {
            let key = format!("payment-{}", task.id);
            runtime
                .commit(
                    move |_tx, _current| async move {
                        Ok(Some(NextTaskState::Running {
                            checkpoint: PaymentState::Charge { key },
                        }))
                    },
                    &task_context,
                )
                .await
        })
        .phase("charge", move |task, runtime, task_context| {
            let payments = Arc::clone(&payments);
            async move {
                let PaymentState::Charge { key } = &task.checkpoint else {
                    unreachable!("the charge phase runs charge checkpoints");
                };
                let receipt = *payments
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .entry(key.clone())
                    .or_insert(task.input.amount * 100);
                runtime
                    .commit(
                        move |_tx, _current| async move {
                            Ok(Some(NextTaskState::Terminal {
                                outcome: TaskOutcome::Completed {
                                    result: Receipt { receipt },
                                },
                            }))
                        },
                        &task_context,
                    )
                    .await
            }
        }),
    )
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
    let payments = Payments::default();
    let payment = payment_task(&payments);

    // Extensions bring task code; the Harness finds it by name in the
    // registry. Nothing runs until resume() or a call that waits for
    // progress, such as wait_for_task().
    let registry = create_registry();
    registry.install(define_extension(Extension {
        tasks: vec![payment.erase()],
        ..Extension::named("payments")
    }))?;
    let harness = Harness::open(
        Arc::new(MemoryStorage::new()),
        HarnessOptions::new(
            create_models(CreateModelsOptions::default()),
            Arc::new(registry),
        ),
        context,
    )
    .await?;
    let root = harness.root(RootOptions::default(), context).await?;
    // Every task names its owner. This one belongs to the conversation; a
    // task can also own child tasks and wait for them (24-child-tasks.rs).
    let definition = payment.as_definition_ref();
    let input = to_json(&PaymentInput { amount: 5 })?;
    let payment_id = root
        .commit(
            move |tx| async move {
                tx.create_task(
                    definition,
                    input,
                    TaskOptions {
                        ownership: TaskOwnership::Conversation,
                        conversation_id: None,
                        background: None,
                    },
                )
                .await
            },
            context,
        )
        .await?;
    // The finished task record is the durable receipt.
    let paid = harness.wait_for_task(payment_id, context).await?;
    writeln!(out, "payment outcome: {}", to_json(&paid.outcome)?)?;

    harness.close(context).await?;
    Ok(())
}
