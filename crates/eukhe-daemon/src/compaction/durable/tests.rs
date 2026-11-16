use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::models::{create_models, CreateModelsOptions};
use eukhe_chord::json::to_json;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{Extension, HarnessOptions};
use eukhe_durable::harness::RootOptions;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::tasks::{define_task, AnyTask, NextTaskState, Task, TaskDefinition};
use eukhe_durable::types::{TaskOptions, TaskOwnership};
use futures::FutureExt as _;
use serde::{Deserialize, Serialize};
use serde_json::json;
use tokio::sync::watch;

use super::*;
use crate::durable_test_support::{answer, ask, cx, kinds, Fixture, SESSION_ID};

fn small_keep_window(fixture: &Fixture) {
    fixture.settings(&json!({ "compaction": { "keepRecentTokens": 1 } }));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn manual_compaction_answers_the_ts_result_and_places_the_summary() {
    let fixture = Fixture::new();
    small_keep_window(&fixture);
    let session = fixture.open(SESSION_ID).await;
    let root = session.root().clone();
    ask(&fixture, &root, "first question", "first answer").await;
    ask(&fixture, &root, "second question", "second answer").await;

    fixture
        .faux
        .append_responses(vec![answer("The user asked two questions.")]);
    let result = run_manual_compaction(
        session.harness(),
        session.deps(),
        &root,
        Some("Be terse.".to_owned()),
        cx(),
    )
    .await
    .expect("compacted");
    assert_eq!(result.summary, "The user asked two questions.");
    assert!(result.tokens_before > 0);
    let first_kept = result.first_kept_entry_id.expect("a kept entry");
    assert!(!first_kept.is_empty());
    assert_eq!(
        kinds(&root).await.last().map(String::as_str),
        Some("pi.compaction")
    );

    // The context now starts at the summary: a second run skips.
    let skipped = run_manual_compaction(session.harness(), session.deps(), &root, None, cx()).await;
    assert_eq!(
        skipped,
        Err(ManualCompactionError::Skipped(ALREADY_COMPACTED))
    );
    session.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_short_session_skips_with_the_ts_message() {
    let fixture = Fixture::new();
    // The keep window counts the system prompt's entries too: with the
    // tool declarations the prompt counts about 19k tokens. This window
    // keeps the one exchange whatever the prompt weighs, with any
    // default.
    fixture.settings(&json!({ "compaction": { "keepRecentTokens": 200_000 } }));
    let session = fixture.open(SESSION_ID).await;
    let root = session.root().clone();
    ask(&fixture, &root, "hi", "hello").await;
    let skipped = run_manual_compaction(session.harness(), session.deps(), &root, None, cx()).await;
    assert_eq!(
        skipped,
        Err(ManualCompactionError::Skipped(TOO_SHORT_TO_COMPACT))
    );
    assert_eq!(
        skipped.unwrap_err().to_string(),
        "Session is too short to compact -- try again once it grows"
    );
    assert!(!kinds(&root)
        .await
        .iter()
        .any(|kind| kind == "pi.compaction"));
    session.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn abort_with_no_live_compaction_is_a_no_op() {
    let fixture = Fixture::new();
    let session = fixture.open(SESSION_ID).await;
    let root = session.root().clone();
    let aborted = abort_compactions(session.harness(), &root, cx())
        .await
        .unwrap();
    assert!(aborted.is_empty());
    session.close(cx()).await.unwrap();
}

/// The kind of [`turn_task`].
const TURN: &str = "test.turn";

/// A turn of [`turn_task`]: the first, or the follow-up its abort starts.
#[derive(Clone, Serialize, Deserialize)]
struct Turn {
    followup: bool,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "lowercase")]
enum TurnPhase {
    Run,
}

/// The gates of [`turn_task`]: the first turn runs, the follow-up runs, the
/// follow-up may end.
struct TurnGates {
    running: watch::Sender<bool>,
    followup_running: watch::Sender<bool>,
    release: watch::Sender<bool>,
}

async fn opened(gate: &watch::Sender<bool>) {
    gate.subscribe()
        .wait_for(|open| *open)
        .await
        .expect("the gates live as long as the test");
}

/// The first turn runs until it is stopped; its abort starts the follow-up
/// turn in the conversation (as an aborted child hands its withdrawn report
/// on and the report starts the parent's next run) and ends once the
/// follow-up runs; the follow-up ends at `release`.
fn turn_task(gates: &Arc<TurnGates>) -> Task<Turn, TurnPhase, (), ()> {
    let (abort_gates, run_gates) = (Arc::clone(gates), Arc::clone(gates));
    let aborted = || NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: None,
            result: None,
        },
    };
    define_task(
        TaskDefinition::new(
            TURN,
            1,
            |_: &Turn| Ok(TurnPhase::Run),
            move |task, runtime, task_cx| {
                let gates = Arc::clone(&abort_gates);
                async move {
                    if !task.input.followup {
                        let definition = runtime
                            .registry()
                            .task(TURN)
                            .map(AnyTask::as_definition_ref)
                            .ok_or_else(|| SessionError::error("test.turn is not defined"))?;
                        let input = to_json(&Turn { followup: true })?;
                        let options = TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: None,
                            background: None,
                            abandon_on_restart: None,
                        };
                        runtime
                            .commit(
                                move |tx, _| async move {
                                    tx.create_task(definition, input, options).await?;
                                    Ok(None)
                                },
                                &task_cx,
                            )
                            .await?;
                        opened(&gates.followup_running).await;
                    }
                    runtime
                        .commit(move |_, _| async move { Ok(Some(aborted())) }, &task_cx)
                        .await
                }
            },
        )
        .phase("run", move |task, runtime, task_cx| {
            let gates = Arc::clone(&run_gates);
            async move {
                if !task.input.followup {
                    gates.running.send_replace(true);
                    return Err(SessionError::Aborted(runtime.signal().cancelled().await));
                }
                gates.followup_running.send_replace(true);
                opened(&gates.release).await;
                runtime
                    .commit(
                        |_, _| async {
                            Ok(Some(NextTaskState::Terminal {
                                outcome: TaskOutcome::Completed { result: () },
                            }))
                        },
                        &task_cx,
                    )
                    .await
            }
        }),
    )
}

/// A manual compaction summarizes a settled transcript: its interrupt
/// returns once the conversation is idle, also after a run the abort itself
/// started, which the abort does not wait for. Paused clock: the sleep ends
/// only once every task parked, so an interrupt that returned with the
/// follow-up still running fails here.
#[tokio::test(start_paused = true)]
async fn the_interrupt_returns_once_the_run_its_abort_started_ended() {
    let gates = Arc::new(TurnGates {
        running: watch::Sender::new(false),
        followup_running: watch::Sender::new(false),
        release: watch::Sender::new(false),
    });
    let turn = turn_task(&gates);
    let registry = create_registry();
    registry
        .install(define_extension(Extension {
            tasks: vec![turn.erase()],
            ..Extension::named("test.turns")
        }))
        .expect("install the turns");
    let harness = Harness::open(
        Arc::new(MemoryStorage::new()),
        HarnessOptions::new(
            create_models(CreateModelsOptions::default()),
            Arc::new(registry),
        ),
        cx(),
    )
    .await
    .expect("open");
    let root = harness
        .root(RootOptions::default(), cx())
        .await
        .expect("root");
    harness.resume().expect("resume");
    let (definition, input) = (
        turn.as_definition_ref(),
        to_json(&Turn { followup: false }).unwrap(),
    );
    root.commit(
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
        cx(),
    )
    .await
    .expect("start the turn");
    opened(&gates.running).await;

    let interrupted = interrupt_turn(&harness, &root, cx());
    tokio::pin!(interrupted);
    tokio::select! {
        biased;
        _ = &mut interrupted => panic!("the interrupt returned while the follow-up ran"),
        () = tokio::time::sleep(Duration::from_secs(3600)) => {}
    }
    assert!(*gates.followup_running.borrow());
    gates.release.send_replace(true);
    assert!(interrupted.await.expect("interrupted").is_empty());
    assert!(matches!(
        root.wait_for_idle(cx()).now_or_never(),
        Some(Ok(()))
    ));
    harness.close(cx()).await.unwrap();
}
