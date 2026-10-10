//! Nested calls a caller leaves running, aborts, cancels, or reattaches to.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use eukhe_chord::context::{with_abort_signal, AbortController};
use eukhe_chord::json::JsonValue;
use serde_json::json;

use super::super::nested_support::{
    call_with, echo_tool, end_result, exec, exec_key, hang, input_of, is_nested, listen, lock,
    nested_text, open_sqlite, plain, results, run_once, settle, sqlite_path, submit_go, taken,
    text_result, tool_tasks, Slot,
};
use super::super::support::{done, result_text, submit_and_wait, tool, tool_with};
use super::setup;
use crate::harness::events::AgentEvent;
use crate::harness::tests::chat_support::{all_entries, open_chat};
use crate::harness::tests::support::{add_tool, context};
use crate::harness::tests::task_support::deferred;
use crate::harness::tool::ToolTaskInput;
use crate::harness::types::{
    ConversationAbortOptions, InputSubmissionDraft, NestedToolExecutionResult, ToolExecutionResult,
    ToolOutputChunk, ToolReplay,
};
use crate::session::SessionError;
use crate::storage::MemoryStorage;
use crate::types::{AnyTaskRecord, SubmissionStatus};

fn json_value(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

/// The terminal outcome status of `record`, as TS `state.outcome.status`.
fn outcome_status(record: &AnyTaskRecord) -> serde_json::Value {
    let state = plain(&record.state);
    assert_eq!(state["status"], "terminal", "{state}");
    state["outcome"]["status"].clone()
}

#[tokio::test]
async fn aborts_the_nested_calls_a_caller_left_running_when_it_returns_keeping_their_details() {
    let setup = setup();
    let running = deferred::<()>();
    {
        let running = running.clone();
        add_tool(
            &setup.registry,
            tool("hang", move |_, api, cx| {
                let running = running.clone();
                async move {
                    api.output(ToolOutputChunk::Text("partial\n"), None)?;
                    api.details(json_value(r#"{"step":1}"#), &cx).await?;
                    running.resolve(());
                    Err(hang(&cx).await)
                }
            }),
            None,
        )
        .unwrap();
    }
    {
        let running = running.clone();
        add_tool(
            &setup.registry,
            tool("batch", move |_, api, cx| {
                let running = running.clone();
                async move {
                    drop(tokio::spawn(exec(&api, "hang", json!({}), &cx)));
                    running.wait().await;
                    Ok(text_result("returned early"))
                }
            }),
            None,
        )
        .unwrap();
    }
    setup.faux.set_responses(vec![
        call_with("batch", json!({}), "c1").into(),
        done().into(),
    ]);
    let chat = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let (stream, events) = listen(&chat.harness, chat.root.id()).await;
    assert_eq!(
        submit_and_wait(&chat.root, "go").await,
        SubmissionStatus::Done
    );
    chat.harness.wait_for_idle(context()).await.unwrap();
    stream.stop().await;
    let entries = all_entries(&chat.root, context()).await.unwrap();
    assert_eq!(result_text(&results(&entries)[0]), "returned early");
    let child = tool_tasks(&chat.harness).await[1].clone();
    assert_eq!(outcome_status(&child), "aborted");
    assert_eq!(
        plain(&child.state)["outcome"]["result"],
        json!({ "kind": "nested" })
    );
    // The aborted call's result keeps its details; programs get no partial output, which only the model read.
    let child_end = end_result(&events, "c1/1").expect("the nested end carries its result");
    assert!(child_end.is_error);
    assert_eq!(child_end.details, Some(json_value(r#"{"step":1}"#)));
    assert_eq!(child_end.structured_output, None);
    // The nested call ends, with its result, before its caller.
    let ends: Vec<(String, bool)> = lock(&events)
        .iter()
        .filter_map(|event| match event {
            AgentEvent::ToolExecutionEnd { call, result, .. } => {
                Some((call.tool_call_id.clone(), result.is_some()))
            }
            _ => None,
        })
        .collect();
    assert_eq!(ends, [("c1/1".to_owned(), true), ("c1".to_owned(), false)]);
    super::super::nested_support::assert_live_empty(&chat.harness, chat.root.id()).await;
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_nested_calls_with_their_caller() {
    let setup = setup();
    let running = deferred::<()>();
    {
        let running = running.clone();
        add_tool(
            &setup.registry,
            tool("hang", move |_, _, cx| {
                let running = running.clone();
                async move {
                    running.resolve(());
                    Err(hang(&cx).await)
                }
            }),
            None,
        )
        .unwrap();
    }
    add_tool(
        &setup.registry,
        tool("batch", |_, api, cx| async move {
            exec(&api, "hang", json!({}), &cx).await?;
            Ok(ToolExecutionResult::default())
        }),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        call_with("batch", json!({}), "c1").into(),
        done().into(),
    ]);
    let chat = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let submission = chat
        .root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    running.wait().await;
    chat.root
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    assert_eq!(
        submission.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Unanswered
    );
    let tasks = tool_tasks(&chat.harness).await;
    let (parent, child) = (plain(&tasks[0].state), plain(&tasks[1].state));
    assert_eq!(
        (&child["outcome"]["status"], &child["outcome"]["result"]),
        (&json!("aborted"), &json!({ "kind": "nested" }))
    );
    assert_eq!(parent["outcome"]["status"], "aborted");
    assert_eq!(parent["outcome"]["result"]["kind"], "model");
    super::super::nested_support::assert_live_empty(&chat.harness, chat.root.id()).await;
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_a_running_nested_call_when_its_caller_throws() {
    let setup = setup();
    let running = deferred::<()>();
    {
        let running = running.clone();
        add_tool(
            &setup.registry,
            tool("hang", move |_, _, cx| {
                let running = running.clone();
                async move {
                    running.resolve(());
                    Err(hang(&cx).await)
                }
            }),
            None,
        )
        .unwrap();
    }
    {
        let running = running.clone();
        add_tool(
            &setup.registry,
            tool("batch", move |_, api, cx| {
                let running = running.clone();
                async move {
                    drop(tokio::spawn(exec(&api, "hang", json!({}), &cx)));
                    running.wait().await;
                    Err::<ToolExecutionResult, _>(SessionError::error("caller failed"))
                }
            }),
            None,
        )
        .unwrap();
    }
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    let text = result_text(&results(&ran.entries)[0]);
    assert!(text.contains("caller failed"), "{text}");
    let child = tool_tasks(&ran.harness).await[1].clone();
    assert_eq!(outcome_status(&child), "aborted");
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reattaches_a_replay_safe_caller_to_the_nested_calls_it_made_before_a_restart() {
    let (_directory, path) = sqlite_path("pi-durable-nested-");
    let setup = setup();
    let (echo, echo_runs) = echo_tool(|_| {});
    add_tool(&setup.registry, echo, None).unwrap();
    let blocked = deferred::<()>();
    let runs = Arc::new(AtomicUsize::new(0));
    {
        let (blocked, runs) = (blocked.clone(), Arc::clone(&runs));
        add_tool(
            &setup.registry,
            tool_with(
                "batch",
                move |_, api, cx| {
                    let (blocked, runs) = (blocked.clone(), Arc::clone(&runs));
                    async move {
                        let run = runs.fetch_add(1, Ordering::SeqCst) + 1;
                        let first = exec(&api, "echo", json!({ "text": "a" }), &cx).await?;
                        if run == 1 {
                            blocked.resolve(());
                            return Err(hang(&cx).await);
                        }
                        // A call new to the rerun: its slot, after the reattached one's, is found and finishes.
                        let second = exec(&api, "echo", json!({ "text": "b" }), &cx).await?;
                        Ok(text_result(&format!(
                            "run {run}: {}, {}",
                            nested_text(&first),
                            nested_text(&second)
                        )))
                    }
                },
                |tool| tool.replay = Some(ToolReplay::Safe),
            ),
            None,
        )
        .unwrap();
    }
    setup.faux.set_responses(vec![
        call_with("batch", json!({}), "c1").into(),
        done().into(),
    ]);
    let opened = open_sqlite(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    blocked.wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_sqlite(&path, &setup).await;
    opened.harness.resume().unwrap();
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    assert_eq!(runs.load(Ordering::SeqCst), 2);
    assert_eq!(echo_runs.load(Ordering::SeqCst), 2);
    let entries = all_entries(&opened.root, context()).await.unwrap();
    assert_eq!(result_text(&results(&entries)[0]), "run 2: echo a, echo b");
    let tasks = tool_tasks(&opened.harness).await;
    assert_eq!(tasks.iter().filter(|task| is_nested(task)).count(), 2);
    assert_eq!(
        plain(&tasks[1].state)["outcome"]["result"]["kind"],
        "nested"
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn stops_only_the_wait_when_a_caller_cancels_it_the_call_runs_on_and_its_key_returns_its_result(
) {
    let setup = setup();
    let cancel = AbortController::new();
    let release = deferred::<()>();
    let attempts: Arc<Mutex<Vec<&'static str>>> = Arc::default();
    let retry: Slot<NestedToolExecutionResult> = Arc::default();
    {
        let (cancel, release) = (cancel.clone(), release.clone());
        add_tool(
            &setup.registry,
            tool("slow", move |_, _, _| {
                let (cancel, release) = (cancel.clone(), release.clone());
                async move {
                    cancel.abort(None);
                    release.wait().await;
                    Ok(text_result("slow done"))
                }
            }),
            None,
        )
        .unwrap();
    }
    {
        let (signal, release, attempts, retry) = (
            cancel.signal(),
            release.clone(),
            Arc::clone(&attempts),
            Arc::clone(&retry),
        );
        add_tool(
            &setup.registry,
            tool("batch", move |_, api, cx| {
                let (signal, release, attempts, retry) = (
                    signal.clone(),
                    release.clone(),
                    Arc::clone(&attempts),
                    Arc::clone(&retry),
                );
                async move {
                    let cancelled = with_abort_signal(&signal, &cx);
                    let first = exec_key(&api, "slow", json!({}), &cancelled, "same").await;
                    lock(&attempts).push(if first.is_ok() {
                        "first done"
                    } else {
                        "first cancelled"
                    });
                    release.resolve(());
                    let result = exec_key(&api, "slow", json!({}), &cx, "same").await?;
                    *lock(&retry) = Some(result);
                    Ok(ToolExecutionResult::default())
                }
            }),
            None,
        )
        .unwrap();
    }
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    assert_eq!(*lock(&attempts), ["first cancelled"]);
    let retry = taken(&retry);
    assert!(!retry.is_error);
    assert_eq!(nested_text(&retry), "slow done");
    assert_eq!(tool_tasks(&ran.harness).await.len(), 2);
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn admits_one_nested_call_for_a_key_used_by_concurrent_calls() {
    let setup = setup();
    let (echo, runs) = echo_tool(|_| {});
    add_tool(&setup.registry, echo, None).unwrap();
    let both: Arc<Mutex<Vec<NestedToolExecutionResult>>> = Arc::default();
    let sink = Arc::clone(&both);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                let (first, second) = futures::join!(
                    exec_key(&api, "echo", json!({ "text": "a" }), &cx, "k"),
                    exec_key(&api, "echo", json!({ "text": "a" }), &cx, "k")
                );
                lock(&sink).extend([first?, second?]);
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    assert_eq!(runs.load(Ordering::SeqCst), 1);
    let texts: Vec<String> = lock(&both).iter().map(nested_text).collect();
    assert_eq!(texts, ["echo a", "echo a"]);
    assert_eq!(tool_tasks(&ran.harness).await.len(), 2);
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_left_running_nested_calls_of_a_caller_interrupted_while_it_cleaned_them_up() {
    let (_directory, path) = sqlite_path("pi-durable-nested-");
    let setup = setup();
    let running = deferred::<()>();
    let cleaning = deferred::<()>();
    let release = deferred::<()>();
    let hang_runs = Arc::new(AtomicUsize::new(0));
    {
        let (running, cleaning, release, hang_runs) = (
            running.clone(),
            cleaning.clone(),
            release.clone(),
            Arc::clone(&hang_runs),
        );
        add_tool(
            &setup.registry,
            tool("hang", move |_, api, cx| {
                let (running, cleaning, release) =
                    (running.clone(), cleaning.clone(), release.clone());
                hang_runs.fetch_add(1, Ordering::SeqCst);
                async move {
                    api.output(ToolOutputChunk::Text("partial\n"), None)?;
                    api.details(json_value(r#"{"step":1}"#), &cx).await?;
                    running.resolve(());
                    hang(&cx).await;
                    // The caller's cleanup waits for this abort; hold it there until the Harness closes.
                    cleaning.resolve(());
                    release.wait().await;
                    Err::<ToolExecutionResult, _>(SessionError::error("aborted"))
                }
            }),
            None,
        )
        .unwrap();
    }
    {
        let running = running.clone();
        add_tool(
            &setup.registry,
            tool("batch", move |_, api, cx| {
                let running = running.clone();
                async move {
                    drop(tokio::spawn(exec(&api, "hang", json!({}), &cx)));
                    running.wait().await;
                    Ok(text_result("returned early"))
                }
            }),
            None,
        )
        .unwrap();
    }
    setup.faux.set_responses(vec![
        call_with("batch", json!({}), "c1").into(),
        done().into(),
    ]);
    let opened = open_sqlite(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    cleaning.wait().await;
    let closed = tokio::spawn(opened.harness.close(context()));
    release.resolve(());
    closed.await.unwrap().unwrap();

    let opened = open_sqlite(&path, &setup).await;
    opened.harness.resume().unwrap();
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    opened.harness.wait_for_idle(context()).await.unwrap();
    // The caller is replay-unsafe: it reports the interruption, and its cleanup aborts the nested call.
    let entries = all_entries(&opened.root, context()).await.unwrap();
    let result = &results(&entries)[0];
    assert_eq!(
        (result.tool_call_id.as_str(), result.is_error),
        ("c1", true)
    );
    assert!(
        result_text(result).contains("Tool batch was interrupted"),
        "{}",
        result_text(result)
    );
    let child = tool_tasks(&opened.harness).await[1].clone();
    assert_eq!(outcome_status(&child), "aborted");
    assert_eq!(hang_runs.load(Ordering::SeqCst), 1);
    super::super::nested_support::assert_live_empty(&opened.harness, opened.root.id()).await;
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_a_nested_call_whose_admission_was_still_committing_when_its_caller_returned() {
    let setup = setup();
    add_tool(&setup.registry, echo_tool(|_| {}).0, None).unwrap();
    add_tool(
        &setup.registry,
        tool("hang", |_, _, cx| async move { Err(hang(&cx).await) }),
        None,
    )
    .unwrap();
    add_tool(
        &setup.registry,
        tool("batch", |_, api, cx| async move {
            exec_key(&api, "echo", json!({ "text": "warm" }), &cx, "warm").await?;
            drop(tokio::spawn(exec_key(&api, "hang", json!({}), &cx, "late")));
            Ok(ToolExecutionResult::default())
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    let late = tool_tasks(&ran.harness)
        .await
        .into_iter()
        .find(|task| matches!(input_of(task), ToolTaskInput::Nested { call, .. } if call.name == "hang"))
        .expect("the late nested call");
    assert_eq!(outcome_status(&late), "aborted");
    super::super::nested_support::assert_live_empty(&ran.harness, ran.root.id()).await;
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn aborts_every_left_running_nested_call_before_waiting_for_any() {
    let setup = setup();
    let b_aborted = deferred::<()>();
    let started = [deferred::<()>(), deferred::<()>()];
    // A only stops once B was told to stop.
    {
        let (started, b_aborted) = (started[0].clone(), b_aborted.clone());
        add_tool(
            &setup.registry,
            tool("a", move |_, _, _| {
                let (started, b_aborted) = (started.clone(), b_aborted.clone());
                async move {
                    started.resolve(());
                    b_aborted.wait().await;
                    Ok(ToolExecutionResult::default())
                }
            }),
            None,
        )
        .unwrap();
    }
    {
        let (started, b_aborted) = (started[1].clone(), b_aborted.clone());
        add_tool(
            &setup.registry,
            tool("b", move |_, _, cx| {
                let (started, b_aborted) = (started.clone(), b_aborted.clone());
                async move {
                    started.resolve(());
                    hang(&cx).await;
                    b_aborted.resolve(());
                    Err::<ToolExecutionResult, _>(SessionError::error("aborted"))
                }
            }),
            None,
        )
        .unwrap();
    }
    {
        let started = started.clone();
        add_tool(
            &setup.registry,
            tool("batch", move |_, api, cx| {
                let started = started.clone();
                async move {
                    drop(tokio::spawn(exec_key(&api, "a", json!({}), &cx, "a")));
                    drop(tokio::spawn(exec_key(&api, "b", json!({}), &cx, "b")));
                    started[0].wait().await;
                    started[1].wait().await;
                    Ok(ToolExecutionResult::default())
                }
            }),
            None,
        )
        .unwrap();
    }
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    let statuses: Vec<serde_json::Value> = tool_tasks(&ran.harness)
        .await
        .iter()
        .filter(|task| is_nested(task))
        .map(|task| plain(&task.state)["status"].clone())
        .collect();
    assert_eq!(statuses, [json!("terminal"), json!("terminal")]);
    ran.harness.close(context()).await.unwrap();
}
