//! A task that owns child tasks: a checkout charges four payments at once and waits for them.
//! The task graph view prints the checkout's tree while its payments run.
//! Run:
//!   cargo run -p eukhe-durable --example 24-child-tasks
use std::collections::HashSet;
use std::io::Write;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{to_json, JsonValue};
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{Extension, HarnessOptions};
use eukhe_durable::harness::{Conversation, Harness, RootOptions, TaskGraphNode, TaskGraphState};
use eukhe_durable::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use eukhe_durable::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use eukhe_durable::types::{
    JoinPolicy, TaskId, TaskOptions, TaskOutcome, TaskOutcomeError, TaskOutcomeStatus,
    TaskOwnership,
};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use serde::{Deserialize, Serialize};

type BoxError = Box<dyn std::error::Error + Send + Sync>;

#[tokio::main]
async fn main() -> Result<(), BoxError> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let key = std::env::var("OPENAI_API_KEY").ok();
    run(&mut std::io::stdout(), &args, key.as_deref()).await
}

/// Lines printed by the task handlers and the example, in print order. Task
/// handlers run on the Harness's own tasks, so they cannot borrow `out`.
#[derive(Clone, Default)]
struct Console(Arc<Mutex<Vec<String>>>);

impl Console {
    fn log(&self, line: impl Into<String>) {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(line.into());
    }

    /// Move the printed lines to `out`.
    fn flush(&self, out: &mut (dyn Write + Send)) -> std::io::Result<()> {
        let lines = std::mem::take(&mut *self.0.lock().unwrap_or_else(PoisonError::into_inner));
        for line in lines {
            writeln!(out, "{line}")?;
        }
        Ok(())
    }
}

#[expect(
    clippy::cast_precision_loss,
    reason = "`Date.now()` is a whole number of milliseconds, far below 2^53"
)]
fn date_now() -> f64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0.0, |elapsed| elapsed.as_millis() as f64)
}

/// The `status` string of an outcome, as TS prints it.
fn status_name(status: TaskOutcomeStatus) -> &'static str {
    match status {
        TaskOutcomeStatus::Completed => "completed",
        TaskOutcomeStatus::Failed => "failed",
        TaskOutcomeStatus::Aborted => "aborted",
        TaskOutcomeStatus::Orphaned => "orphaned",
        TaskOutcomeStatus::Faulted => "faulted",
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaymentInput {
    card: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum PaymentState {
    Charge { at: f64 },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaymentResult {
    card: String,
}

type Payment = Task<PaymentInput, PaymentState, PaymentResult, ()>;

fn terminal<S, R>(outcome: TaskOutcome<R>) -> NextTaskState<S, R> {
    NextTaskState::Terminal { outcome }
}

fn aborted<R>() -> TaskOutcome<R> {
    TaskOutcome::Aborted {
        reason: None,
        result: None,
    }
}

// A fake bank: it declines an expired card at once, and confirms other charges after a moment.
fn payment_task(charged: Arc<Mutex<HashSet<String>>>, console: Console) -> Payment {
    let charge_set = Arc::clone(&charged);
    define_task(
        TaskDefinition::new(
            "example.payment",
            1,
            |_: &PaymentInput| {
                Ok(PaymentState::Charge {
                    at: date_now() + 100.0,
                })
            },
            // Each payment undoes its own effect when aborted.
            move |task, runtime, cx: Context| {
                let refunded = charged
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .remove(&task.input.card);
                let suffix = if refunded { ", refunded" } else { "" };
                console.log(format!("  payment {} aborted{suffix}", task.input.card));
                async move {
                    runtime
                        .commit(|_, _| async { Ok(Some(terminal(aborted()))) }, &cx)
                        .await
                }
            },
        )
        .phase("charge", move |task, runtime, cx| {
            let charged = Arc::clone(&charge_set);
            async move {
                let card = task.input.card;
                if card.starts_with("expired") {
                    let error = TaskOutcomeError {
                        message: format!("{card} declined"),
                        detail: None,
                    };
                    return runtime
                        .commit(
                            |_, _| async {
                                Ok(Some(terminal(TaskOutcome::Failed {
                                    error,
                                    result: None,
                                })))
                            },
                            &cx,
                        )
                        .await;
                }
                charged
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .insert(card.clone());
                let PaymentState::Charge { at } = task.checkpoint;
                runtime.sleep(at, &cx).await?;
                runtime
                    .commit(
                        |_, _| async {
                            Ok(Some(terminal(TaskOutcome::Completed {
                                result: PaymentResult { card },
                            })))
                        },
                        &cx,
                    )
                    .await
            }
        }),
    )
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct CheckoutInput {
    cards: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
enum CheckoutState {
    Pay,
    Decide { payments: Vec<TaskId> },
}

type Checkout = Task<CheckoutInput, CheckoutState, String, ()>;

// The checkout creates its payments as child tasks and waits for all of them.
// With `FailFast`, the first payment that fails aborts the others; the checkout
// itself is not aborted and decides its outcome once every payment is done.
fn checkout_task(payment: &Payment, console: Console) -> Checkout {
    let payment = payment.as_definition_ref();
    let decide_console = console.clone();
    define_task(
        TaskDefinition::new(
            "example.checkout",
            1,
            |_: &CheckoutInput| Ok(CheckoutState::Pay),
            // Runs only after every payment is done, so the refunds have already happened.
            move |_task, runtime, cx: Context| {
                console.log("  checkout aborted");
                async move {
                    runtime
                        .commit(|_, _| async { Ok(Some(terminal(aborted()))) }, &cx)
                        .await
                }
            },
        )
        .phase("pay", move |task, runtime, cx| {
            let payment = Arc::clone(&payment);
            async move {
                runtime
                    .commit(
                        move |tx, task| async move {
                            let mut payments = Vec::new();
                            for card in task.input.cards {
                                let options = TaskOptions {
                                    ownership: TaskOwnership::Task {
                                        task_id: task.id.erase(),
                                    },
                                    conversation_id: None,
                                    background: None,
                                    abandon_on_restart: None,
                                };
                                let input = to_json(&PaymentInput { card })?;
                                payments.push(
                                    tx.create_task(Arc::clone(&payment), input, options).await?,
                                );
                            }
                            Ok(Some(NextTaskState::Waiting {
                                checkpoint: CheckoutState::Decide {
                                    payments: payments.clone(),
                                },
                                on: payments,
                                policy: JoinPolicy::FailFast,
                            }))
                        },
                        &cx,
                    )
                    .await?;
                drop(task);
                Ok(())
            }
        })
        .phase("decide", move |task, runtime, cx| {
            let console = decide_console.clone();
            async move {
                let CheckoutState::Decide { payments } = task.checkpoint else {
                    return Ok(());
                };
                let outcomes = runtime.outcomes::<JsonValue>(&payments, &cx).await?;
                let statuses: Vec<&str> = outcomes
                    .iter()
                    .map(|outcome| status_name(outcome.status()))
                    .collect();
                console.log(format!("  payments: {}", statuses.join(", ")));
                let paid = outcomes
                    .iter()
                    .all(|outcome| outcome.status() == TaskOutcomeStatus::Completed);
                runtime
                    .commit(
                        move |_, _| async move {
                            Ok(Some(terminal(if paid {
                                TaskOutcome::Completed {
                                    result: "order placed".to_owned(),
                                }
                            } else {
                                TaskOutcome::Failed {
                                    error: TaskOutcomeError {
                                        message: "payment failed".to_owned(),
                                        detail: None,
                                    },
                                    result: None,
                                }
                            })))
                        },
                        &cx,
                    )
                    .await
            }
        }),
    )
}

async fn open(
    path: &std::path::Path,
    registry: &Registry,
    cx: &Context,
) -> Result<Harness, BoxError> {
    let storage = open_native_sqlite_storage(path, NativeSqliteStorageOptions::default()).await?;
    let options = HarnessOptions::new(
        create_models(CreateModelsOptions::default()),
        Arc::new(registry.clone()),
    );
    Ok(Harness::open(Arc::new(storage), options, cx).await?)
}

/// Print `node` and, indented below it, the tasks it owns.
fn print_node(console: &Console, nodes: &[TaskGraphNode], node: &TaskGraphNode, depth: usize) {
    let status = match &node.state {
        TaskGraphState::Waiting { on, .. } => {
            let on: Vec<String> = on.iter().map(ToString::to_string).collect();
            format!("waiting on {}", on.join(", "))
        }
        state => state.status().to_owned(),
    };
    console.log(format!(
        "  {}{} {}: {status}",
        "  ".repeat(depth),
        node.kind,
        node.id
    ));
    for child in nodes.iter().filter(|child| child.owner == Some(node.id)) {
        print_node(console, nodes, child, depth + 1);
    }
}

/// Print the live tasks as a tree along their owner edges.
fn print_graph(console: &Console, graph: &JsonValue) -> Result<(), BoxError> {
    let mut nodes: Vec<TaskGraphNode> = Vec::new();
    if let JsonValue::Object(tasks) = &graph["tasks"] {
        for node in tasks.values() {
            nodes.push(eukhe_chord::json::from_json(node)?);
        }
    }
    // JS objects list integer keys in ascending order.
    nodes.sort_by_key(|node| node.id);
    for node in nodes.iter().filter(|node| node.owner.is_none()) {
        print_node(console, &nodes, node, 0);
    }
    Ok(())
}

/// Whether the graph holds `count` running payments.
fn payments_running(graph: &JsonValue, count: usize) -> Result<bool, BoxError> {
    let mut running = 0;
    if let JsonValue::Object(tasks) = &graph["tasks"] {
        for node in tasks.values() {
            let node: TaskGraphNode = eukhe_chord::json::from_json(node)?;
            if node.kind == "example.payment"
                && matches!(node.state, TaskGraphState::Running { .. })
            {
                running += 1;
            }
        }
    }
    Ok(running == count)
}

async fn checkout(
    root: &Conversation,
    task: &Checkout,
    cards: &[&str],
    cx: &Context,
) -> Result<TaskId, BoxError> {
    let definition = task.as_definition_ref();
    let input = to_json(&CheckoutInput {
        cards: cards.iter().map(|card| (*card).to_owned()).collect(),
    })?;
    let options = TaskOptions {
        ownership: TaskOwnership::Conversation,
        conversation_id: None,
        background: None,
        abandon_on_restart: None,
    };
    Ok(root
        .commit(
            move |tx| async move { tx.create_task(definition, input, options).await },
            cx,
        )
        .await?)
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
    let cx: &Context = &BACKGROUND_CONTEXT;
    let console = Console::default();
    let charged = Arc::new(Mutex::new(HashSet::new()));
    let payment = payment_task(charged, console.clone());
    let checkout_definition = checkout_task(&payment, console.clone());

    let registry = create_registry();
    registry.install(define_extension(Extension {
        tasks: vec![payment.erase(), checkout_definition.erase()],
        ..Extension::named("checkout")
    }))?;
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-example-")
        .tempdir()?;
    let database_path = directory.path().join("session.sqlite");

    let mut harness = open(&database_path, &registry, cx).await?;
    let mut root = harness.root(RootOptions::default(), cx).await?;

    console.log("One card is declined:");
    let id = checkout(
        &root,
        &checkout_definition,
        &["visa-1", "expired-2", "visa-3", "visa-4"],
        cx,
    )
    .await?;
    let settled = harness.wait_for_task(id, cx).await?;
    console.log(format!(
        "  checkout: {}",
        status_name(settled.outcome.status())
    ));
    console.flush(out)?;

    console.log("The customer cancels:");
    let id = checkout(
        &root,
        &checkout_definition,
        &["visa-5", "visa-6", "visa-7", "visa-8"],
        cx,
    )
    .await?;
    harness.resume()?;
    // TS waits 20 ms here; waiting until every payment runs shows the same tree on a busy machine too.
    loop {
        let graph = harness.task_graph(cx).await?;
        let value = graph.value();
        graph.dispose()?;
        if payments_running(&value, 4)? {
            print_graph(&console, &value)?;
            break;
        }
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    harness.abort_task(id, cx).await?;
    let settled = harness.wait_for_task(id, cx).await?;
    console.log(format!(
        "  checkout: {}",
        status_name(settled.outcome.status())
    ));
    console.flush(out)?;

    console.log("The process stops while the payments run, and a new one continues:");
    let id = checkout(
        &root,
        &checkout_definition,
        &["visa-9", "visa-10", "visa-11", "visa-12"],
        cx,
    )
    .await?;
    tokio::time::sleep(Duration::from_millis(20)).await;
    harness.close(cx).await?;
    harness = open(&database_path, &registry, cx).await?;
    root = harness.root(RootOptions::default(), cx).await?;
    let settled = harness.wait_for_task(id, cx).await?;
    console.log(format!(
        "  checkout: {}",
        status_name(settled.outcome.status())
    ));
    console.flush(out)?;
    drop(root);

    harness.close(cx).await?;
    directory.close()?;
    Ok(())
}
