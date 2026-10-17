//! The bridge between one real tool call and the journal of its Bend model
//! (`bend/job.bend`, whose laws `PROOF.bend` proves): both run the same
//! scenarios and must print the same transcript, byte for byte.
//!
//! A scenario is a call scenario of `bend/bridge_stream.bend` (the file
//! documents the format): a model-issued call streams result bytes, warns,
//! and records usage, then returns or is cancelled. The driver records
//! every `pi.live` commit from the call's start on and prints, in order,
//! each one that writes inside the call's slot: `start` for the one that
//! marks it running, `settle H B W U` for the one that marks it done (H, B,
//! W and U read from the result entry it appended), and `progress` for any
//! other. The model journals only the start and the settle, so a progress
//! commit fails the bridge.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{StopReason, Usage, UserContentBlock};
use futures::future::BoxFuture;
use futures::FutureExt;
use tokio::sync::{mpsc, oneshot};

use super::support::results;
use crate::harness::define::define_tool;
use crate::harness::live::LIVE_DOC;
use crate::harness::tests::chat_support::{all_entries, chat_setup, open_chat, OpenChat};
use crate::harness::tests::support::{add_tool, context, empty_object_schema};
use crate::harness::types::{
    InputSubmissionDraft, ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionApi,
    ToolExecutionResult, ToolOutputChunk, ToolRegistration,
};
use crate::session::tests::support::document_changes;
use crate::session::SessionError;
use crate::storage::MemoryStorage;
use crate::testing::bridge::{compare, Rng, Scenario};
use crate::types::TaskId;

/// One step inside the tool: false returns the tool's result.
type Action = Box<dyn FnOnce(&dyn ToolExecutionApi) -> bool + Send>;
type Steps = mpsc::UnboundedSender<(Action, oneshot::Sender<()>)>;
type Commits = Arc<Mutex<Vec<Vec<serde_json::Value>>>>;

fn lock<T>(value: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    value.lock().unwrap_or_else(PoisonError::into_inner)
}

/// What a scenario's call does.
#[derive(Clone, Copy)]
enum Event {
    Delta(u64),
    Warn,
    Use(u64),
    Final,
    Cancel,
}

/// The `scripted` tool: runs each step it receives, until one returns.
fn scripted(steps: mpsc::UnboundedReceiver<(Action, oneshot::Sender<()>)>) -> ToolRegistration {
    let steps = Arc::new(tokio::sync::Mutex::new(steps));
    ToolRegistration::new(
        "scripted",
        "Driven by the bridge",
        empty_object_schema(),
        move |_, api, cx| {
            let steps = Arc::clone(&steps);
            async move {
                let signal = cx.abort_signal().expect("a call signal");
                let mut steps = steps.lock().await;
                loop {
                    let (action, done) = tokio::select! {
                        step = steps.recv() => step.expect("the driver holds the sender"),
                        reason = signal.cancelled() => return Err(SessionError::Aborted(reason)),
                    };
                    let going = action(&*api);
                    let _ = done.send(());
                    if !going {
                        return Ok(ToolExecutionResult::default());
                    }
                }
            }
        },
    )
}

async fn step(steps: &Steps, action: Action) {
    let (done, ran) = oneshot::channel();
    steps.send((action, done)).unwrap();
    ran.await.unwrap();
}

/// Run one call through `events` and print its journal.
#[expect(
    clippy::too_many_lines,
    reason = "one scenario, step by step: setup, the call, the journal"
)]
async fn run(events: &[Event]) -> String {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let (steps, received) = mpsc::unbounded_channel();
    add_tool(&setup.registry, define_tool(scripted(received)), None).unwrap();
    setup.faux.set_responses(vec![
        faux_assistant_message(
            vec![faux_tool_call(
                "scripted",
                serde_json::Map::new(),
                Some("c1".to_owned()),
            )],
            FauxAssistantMessageOptions {
                stop_reason: Some(StopReason::ToolUse),
                ..FauxAssistantMessageOptions::default()
            },
        )
        .into(),
        faux_assistant_message(
            vec![faux_text("done")],
            FauxAssistantMessageOptions::default(),
        )
        .into(),
    ]);
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let commits: Commits = Arc::default();
    let sink = Arc::clone(&commits);
    drop(
        harness
            .subscribe_commits(Arc::new(move |publication, _| {
                for change in document_changes(publication) {
                    if change.record.kind == "pi.live" && !change.ops.is_empty() {
                        lock(&sink).push(
                            change
                                .ops
                                .iter()
                                .map(|op| serde_json::Value::from(&op.to_json()))
                                .collect(),
                        );
                    }
                }
            }))
            .unwrap(),
    );
    let submission = root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    let conversation = root.id();
    let task = loop {
        let live = harness
            .snapshot(&LIVE_DOC, conversation, context())
            .await
            .unwrap()
            .map(|value| serde_json::Value::from(&eukhe_chord::json::JsonValue::Object(value)));
        let slot = live.as_ref().map(|live| &live["tools"][0]);
        if let Some(slot) = slot.filter(|slot| slot["status"] == "running") {
            break TaskId::from_number(slot["taskId"].as_u64().unwrap());
        }
        tokio::time::sleep(Duration::from_millis(1)).await;
    };
    for event in events {
        match *event {
            Event::Delta(bytes) => {
                let text = "x".repeat(usize::try_from(bytes).unwrap());
                step(
                    &steps,
                    Box::new(move |api| {
                        api.output(ToolOutputChunk::Text(&text), None).unwrap();
                        true
                    }),
                )
                .await;
            }
            Event::Warn => {
                step(
                    &steps,
                    Box::new(|api| {
                        api.diagnostic(ToolDiagnostic {
                            omitted: None,
                            artifact: None,
                            lines: None,
                            severity: ToolDiagnosticSeverity::Warn,
                            code: None,
                            message: "careful".to_owned(),
                        })
                        .unwrap();
                        true
                    }),
                )
                .await;
            }
            Event::Use(tokens) => {
                step(
                    &steps,
                    Box::new(move |api| {
                        api.usage(Usage {
                            input: tokens,
                            ..Usage::default()
                        })
                        .unwrap();
                        true
                    }),
                )
                .await;
            }
            Event::Final => {
                step(&steps, Box::new(|_| false)).await;
                break;
            }
            Event::Cancel => {
                harness.abort_task(task, context()).await.unwrap();
                break;
            }
        }
    }
    submission.wait(context()).await.unwrap();
    let entries = all_entries(&root, context()).await.unwrap();
    let result = results(&entries).remove(0);
    let warns = result
        .content
        .iter()
        .filter_map(|block| match block {
            UserContentBlock::Text(text) if text.text.starts_with("<harness>") => {
                Some(text.text.matches("[warn] ").count())
            }
            _ => None,
        })
        .sum::<usize>();
    let bytes: usize = result
        .content
        .iter()
        .filter_map(|block| match block {
            UserContentBlock::Text(text) if !text.text.starts_with("<harness>") => {
                Some(text.text.len())
            }
            _ => None,
        })
        .sum();
    let how = if result.is_error { "c" } else { "f" };
    let usage = result.usage.map_or(0, |usage| usage.input);
    harness.close(context()).await.unwrap();

    let in_slot = |op: &serde_json::Value| {
        op[1]
            .as_array()
            .is_some_and(|path| path.len() > 2 && path[0] == "tools" && path[1] == 0)
    };
    let sets = |ops: &[serde_json::Value], status: &str| {
        ops.iter().any(|op| {
            op[0] == "s" && op[1] == serde_json::json!(["tools", 0, "status"]) && op[2] == status
        })
    };
    let mut journal = String::new();
    for ops in lock(&commits).iter().filter(|ops| ops.iter().any(in_slot)) {
        if sets(ops, "running") {
            journal.push_str("start\n");
        } else if sets(ops, "done") {
            let _infallible = writeln!(journal, "settle {how} {bytes} {warns} {usage}");
        } else {
            journal.push_str("progress\n");
        }
    }
    journal
}

/// One scenario of 0 to 12 events before the call returns or is cancelled.
fn scenario(rng: &mut Rng) -> (Vec<Event>, String) {
    let mut events: Vec<Event> = (0..rng.range(0, 12))
        .map(|_| match rng.below(3) {
            0 => Event::Delta(rng.range(0, 40)),
            1 => Event::Warn,
            _ => Event::Use(rng.range(0, 9)),
        })
        .collect();
    events.push(if rng.chance(50) {
        Event::Final
    } else {
        Event::Cancel
    });
    let mut text = String::from("s\n");
    for event in &events {
        let _infallible = match *event {
            Event::Delta(bytes) => writeln!(text, "d {bytes}"),
            Event::Warn => writeln!(text, "w"),
            Event::Use(tokens) => writeln!(text, "u {tokens}"),
            Event::Final => writeln!(text, "f"),
            Event::Cancel => writeln!(text, "x"),
        };
    }
    (events, text)
}

fn block_on(future: BoxFuture<'_, String>) -> String {
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}

#[test]
fn a_real_tool_calls_journal_equals_the_bend_model() {
    let mut rng = Rng(0x5851_f42d_4c95_7f2d);
    let scenarios: Vec<Scenario> = (0..40)
        .map(|at| {
            let (events, text) = scenario(&mut rng);
            let transcript = block_on(run(&events).boxed());
            Scenario {
                name: format!("call {at}"),
                events: text,
                transcript,
            }
        })
        .collect();
    compare("bend/bridge_stream.bend", scenarios);
}
