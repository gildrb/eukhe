//! Nested calls in `pi.live.nestedTools` and in tool events.

use std::sync::{Arc, Mutex};

use eukhe_chord::json::JsonValue;
use futures::FutureExt;
use serde_json::json;

use super::super::nested_support::{
    call_with, echo_tool, end_of, end_result, exec, exec_key, hang, listen, live, lock,
    nested_text, plain, results, starts_and_ends, taken, text_item, text_result, tool_tasks, Slot,
};
use super::super::support::{done, result_text, submit_and_wait, tool};
use super::setup;
use crate::harness::events::{AgentEvent, ToolOutputUpdate};
use crate::harness::live::LIVE_DOC;
use crate::harness::tests::chat_support::{all_entries, open_chat, OpenChat};
use crate::harness::tests::support::{add_hooks, add_tool, context, tool_task};
use crate::harness::tests::task_support::{deferred, eventually};
use crate::harness::tool::ToolTaskInput;
use crate::harness::types::{
    BeforeToolDecision, ExecuteToolOptions, InputSubmissionDraft, NestedToolExecutionResult,
    ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionResult, ToolHooks, ToolOutputChunk,
};
use crate::storage::MemoryStorage;
use crate::types::DocumentReaderExt;

fn json_value(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

async fn open(setup: &crate::harness::tests::chat_support::ChatSetup) -> OpenChat {
    setup.faux.set_responses(vec![
        call_with("batch", json!({}), "c1").into(),
        done().into(),
    ]);
    open_chat(Arc::new(MemoryStorage::new()), setup, None)
        .await
        .unwrap()
}

/// `pi.live.nestedTools` as plain JSON.
async fn nested_slots(chat: &OpenChat) -> serde_json::Value {
    let live = live(&chat.harness, chat.root.id()).await.expect("pi.live");
    plain(&live.nested_tools.unwrap_or_default())
}

#[tokio::test]
async fn reports_nested_calls_in_pi_live_nested_tools_and_as_tool_events_with_their_parent() {
    let setup = setup();
    let release = deferred::<()>();
    let running = deferred::<()>();
    {
        let (release, running) = (release.clone(), running.clone());
        add_tool(
            &setup.registry,
            tool("slow", move |_, api, cx| {
                let (release, running) = (release.clone(), running.clone());
                async move {
                    api.output(ToolOutputChunk::Text("working\n"), None)?;
                    api.details(json_value(r#"{"step":1}"#), &cx).await?;
                    running.resolve(());
                    release.wait().await;
                    Ok(text_result("slow done"))
                }
            }),
            None,
        )
        .unwrap();
    }
    add_tool(
        &setup.registry,
        tool("batch", |_, api, cx| async move {
            let result = exec(&api, "slow", json!({}), &cx).await?;
            Ok(text_result(&nested_text(&result)))
        }),
        None,
    )
    .unwrap();
    let chat = open(&setup).await;
    let (stream, events) = listen(&chat.harness, chat.root.id()).await;
    assert!(stream.snapshot().nested_tools.is_empty());
    let submission = chat
        .root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    running.wait().await;
    let slots = nested_slots(&chat).await;
    assert_eq!(
        slots,
        json!([{
            "callId": "c1/1",
            "parentCallId": "c1",
            "parentTaskId": slots[0]["parentTaskId"],
            "name": "slow",
            "taskId": slots[0]["taskId"],
            "arguments": {},
            "status": "running",
            "output": "working\n",
            "details": { "step": 1 },
        }])
    );
    assert!(slots[0]["taskId"].is_number() && slots[0]["parentTaskId"].is_number());
    release.resolve(());
    submission.wait(context()).await.unwrap();
    chat.harness.wait_for_idle(context()).await.unwrap();
    stream.stop().await;
    let c1 = || "c1".to_owned();
    assert_eq!(
        starts_and_ends(&events),
        [
            ("tool_execution_start", c1(), None),
            ("tool_execution_start", "c1/1".to_owned(), Some(c1())),
            ("tool_execution_end", "c1/1".to_owned(), Some(c1())),
            ("tool_execution_end", c1(), None),
        ]
    );
    let nested_end = end_result(&events, "c1/1").expect("the nested end carries its result");
    assert_eq!(nested_text(&nested_end), "slow done");
    assert!(!nested_end.is_error);
    // Events name the call's task and, for a nested call, the calling one.
    let tasks = tool_tasks(&chat.harness).await;
    let (parent, child) = (tasks[0].id, tasks[1].id);
    let Some(AgentEvent::ToolExecutionEnd { call: nested, .. }) = end_of(&events, "c1/1") else {
        panic!("the nested call ends");
    };
    assert_eq!(
        (nested.task_id, nested.parent_task_id),
        (Some(child), Some(parent))
    );
    let Some(AgentEvent::ToolExecutionEnd { call: model, .. }) = end_of(&events, "c1") else {
        panic!("the model-issued call ends");
    };
    assert_eq!((model.task_id, model.parent_task_id), (Some(parent), None));
    assert!(lock(&events).iter().any(|event| matches!(
        event,
        AgentEvent::ToolExecutionUpdate { call, .. }
            if call.tool_call_id == "c1/1" && call.parent_tool_call_id.as_deref() == Some("c1")
    )));
    super::super::nested_support::assert_live_empty(&chat.harness, chat.root.id()).await;
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn runs_nested_calls_of_nested_calls_and_ends_them_children_first() {
    let setup = setup();
    add_tool(&setup.registry, echo_tool(|_| {}).0, None).unwrap();
    add_tool(
        &setup.registry,
        tool("inner", |_, api, cx| async move {
            let result = exec_key(&api, "echo", json!({ "text": "deep" }), &cx, "x").await?;
            Ok(text_result(&nested_text(&result)))
        }),
        None,
    )
    .unwrap();
    add_tool(
        &setup.registry,
        tool("outer", |_, api, cx| async move {
            let result = exec(&api, "inner", json!({}), &cx).await?;
            Ok(text_result(&nested_text(&result)))
        }),
        None,
    )
    .unwrap();
    setup.faux.set_responses(vec![
        call_with("outer", json!({}), "c1").into(),
        done().into(),
    ]);
    let chat = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let (stream, events) = listen(&chat.harness, chat.root.id()).await;
    submit_and_wait(&chat.root, "go").await;
    chat.harness.wait_for_idle(context()).await.unwrap();
    stream.stop().await;
    let entries = all_entries(&chat.root, context()).await.unwrap();
    assert_eq!(result_text(&results(&entries)[0]), "echo deep");
    let tasks = tool_tasks(&chat.harness).await;
    let (outer, inner, deep) = (&tasks[0], &tasks[1], &tasks[2]);
    assert_eq!((inner.owner, deep.owner), (Some(outer.id), Some(inner.id)));
    let id = |text: &str| text.to_owned();
    assert_eq!(
        starts_and_ends(&events),
        [
            ("tool_execution_start", id("c1"), None),
            ("tool_execution_start", id("c1/1"), Some(id("c1"))),
            ("tool_execution_start", id("c1/1/x"), Some(id("c1/1"))),
            ("tool_execution_end", id("c1/1/x"), Some(id("c1/1"))),
            ("tool_execution_end", id("c1/1"), Some(id("c1"))),
            ("tool_execution_end", id("c1"), None),
        ]
    );
    super::super::nested_support::assert_live_empty(&chat.harness, chat.root.id()).await;
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn reports_the_output_of_several_running_nested_calls_and_shows_them_to_a_late_subscriber() {
    let setup = setup();
    let release = deferred::<()>();
    let running = [deferred::<()>(), deferred::<()>()];
    let wrote = [deferred::<()>(), deferred::<()>()];
    {
        let (release, running, wrote) = (release.clone(), running.clone(), wrote.clone());
        add_tool(
            &setup.registry,
            tool("slow", move |args, api, cx| {
                let name = args["text"].as_str().unwrap_or_default().to_owned();
                let index = usize::from(name == "two");
                let (release, running, wrote) = (
                    release.clone(),
                    running[index].clone(),
                    wrote[index].clone(),
                );
                async move {
                    running.resolve(());
                    wrote.wait().await;
                    api.output(ToolOutputChunk::Text(&format!("{name}\n")), None)?;
                    api.details(json_value(&format!(r#"{{"name":"{name}"}}"#)), &cx)
                        .await?;
                    release.wait().await;
                    Ok(ToolExecutionResult::default())
                }
            }),
            None,
        )
        .unwrap();
    }
    add_tool(
        &setup.registry,
        tool("batch", |_, api, cx| async move {
            let (one, two) = futures::join!(
                exec(&api, "slow", json!({ "text": "one" }), &cx),
                exec(&api, "slow", json!({ "text": "two" }), &cx)
            );
            one?;
            two?;
            Ok(ToolExecutionResult::default())
        }),
        None,
    )
    .unwrap();
    let chat = open(&setup).await;
    let submission = chat
        .root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    running[0].wait().await;
    running[1].wait().await;
    let (stream, events) = listen(&chat.harness, chat.root.id()).await;
    let listed: Vec<(String, String)> = stream
        .snapshot()
        .nested_tools
        .iter()
        .map(|slot| {
            (
                slot.call_id.clone(),
                plain(&slot.status).as_str().unwrap().to_owned(),
            )
        })
        .collect();
    assert_eq!(
        listed,
        [
            ("c1/1".to_owned(), "running".to_owned()),
            ("c1/2".to_owned(), "running".to_owned())
        ]
    );
    let updates = || -> Vec<(String, ToolOutputUpdate)> {
        lock(&events)
            .iter()
            .filter_map(|event| match event {
                AgentEvent::ToolExecutionUpdate {
                    call,
                    output: Some(output),
                    ..
                } => Some((call.tool_call_id.clone(), output.clone())),
                _ => None,
            })
            .collect()
    };
    // The second slot writes first, so a wrong slot index in the update path would show.
    wrote[1].resolve(());
    eventually(|| {
        let count = updates().len();
        async move { count == 1 }
    })
    .await;
    wrote[0].resolve(());
    eventually(|| {
        let count = updates().len();
        async move { count == 2 }
    })
    .await;
    release.resolve(());
    submission.wait(context()).await.unwrap();
    stream.stop().await;
    assert_eq!(
        updates(),
        [
            (
                "c1/2".to_owned(),
                ToolOutputUpdate::Set {
                    set: "two\n".to_owned()
                }
            ),
            (
                "c1/1".to_owned(),
                ToolOutputUpdate::Set {
                    set: "one\n".to_owned()
                }
            ),
        ]
    );
    chat.harness.close(context()).await.unwrap();
}

/// A nested call of `chatty` with `progress: false`.
fn quiet(
    api: &Arc<dyn crate::harness::types::ToolExecutionApi>,
    cx: &eukhe_chord::context::Context,
) -> futures::future::BoxFuture<'static, crate::session::SessionResult<NestedToolExecutionResult>> {
    api.execute_tool(
        "chatty",
        eukhe_types::pi_ai::JsonObject::new(),
        cx,
        ExecuteToolOptions {
            key: None,
            progress: Some(false),
        },
    )
}

fn note() -> ToolDiagnostic {
    ToolDiagnostic {
        severity: ToolDiagnosticSeverity::Info,
        code: None,
        message: "note".to_owned(),
    }
}

#[tokio::test]
async fn commits_only_the_status_of_a_nested_call_made_with_progress_false_and_keeps_its_output_in_the_result(
) {
    let setup = setup();
    let running = deferred::<()>();
    let release = deferred::<()>();
    {
        let (running, release) = (running.clone(), release.clone());
        add_tool(
            &setup.registry,
            tool("chatty", move |_, api, cx| {
                let (running, release) = (running.clone(), release.clone());
                async move {
                    api.output(ToolOutputChunk::Text("line\n"), None)?;
                    api.diagnostic(note())?;
                    api.details(json_value(r#"{"step":1}"#), &cx).await?;
                    running.resolve(());
                    release.wait().await;
                    Ok(ToolExecutionResult::default())
                }
            }),
            None,
        )
        .unwrap();
    }
    let result: Slot<NestedToolExecutionResult> = Arc::default();
    let sink = Arc::clone(&result);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                let result = quiet(&api, &cx).await?;
                *lock(&sink) = Some(result);
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let chat = open(&setup).await;
    let submission = chat
        .root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    // `details()` resolved before this, so a progress commit would have landed already.
    running.wait().await;
    let slots = nested_slots(&chat).await;
    assert_eq!(
        slots[0],
        json!({
            "callId": "c1/1",
            "parentCallId": "c1",
            "parentTaskId": slots[0]["parentTaskId"],
            "name": "chatty",
            "taskId": slots[0]["taskId"],
            "arguments": {},
            "status": "running",
        })
    );
    release.resolve(());
    submission.wait(context()).await.unwrap();
    let result = taken(&result);
    assert_eq!(nested_text(&result), "line\n");
    assert_eq!(result.details, Some(json_value(r#"{"step":1}"#)));
    assert_eq!(result.diagnostics, [note()]);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn loses_the_running_output_of_a_nested_call_made_with_progress_false_when_it_is_aborted() {
    let setup = setup();
    let running = deferred::<()>();
    {
        let running = running.clone();
        add_tool(
            &setup.registry,
            tool("chatty", move |_, api, cx| {
                let running = running.clone();
                async move {
                    api.output(ToolOutputChunk::Text("line\n"), None)?;
                    api.diagnostic(note())?;
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
                    drop(tokio::spawn(quiet(&api, &cx)));
                    running.wait().await;
                    Ok(ToolExecutionResult::default())
                }
            }),
            None,
        )
        .unwrap();
    }
    let chat = open(&setup).await;
    let (stream, events) = listen(&chat.harness, chat.root.id()).await;
    submit_and_wait(&chat.root, "go").await;
    chat.harness.wait_for_idle(context()).await.unwrap();
    stream.stop().await;
    // The abort's result is built from the slot, which never got the output.
    let result = end_result(&events, "c1/1").expect("the nested end carries its result");
    assert!(result.is_error);
    assert_eq!(result.structured_output, None);
    assert_eq!(result.details, None);
    let codes: Vec<Option<&str>> = result
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code.as_deref())
        .collect();
    assert_eq!(codes, [Some("aborted")]);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn shows_a_nested_calls_arguments_in_its_slot_as_made_then_unbounded_as_it_runs_with_them() {
    let setup = setup();
    let hook_entered = deferred::<()>();
    let hook_release = deferred::<()>();
    let running = deferred::<()>();
    let release = deferred::<()>();
    let large = "x".repeat(64 * 1024);
    {
        let (running, release) = (running.clone(), release.clone());
        add_tool(
            &setup.registry,
            tool("slow", move |_, _, _| {
                let (running, release) = (running.clone(), release.clone());
                async move {
                    running.resolve(());
                    release.wait().await;
                    Ok(ToolExecutionResult::default())
                }
            }),
            None,
        )
        .unwrap();
    }
    {
        let (hook_entered, hook_release, large) =
            (hook_entered.clone(), hook_release.clone(), large.clone());
        add_hooks(
            &setup.registry,
            tool_task(),
            ToolHooks {
                before_tool: Some(Arc::new(move |call, _, _| {
                    let nested = call.parent.is_some();
                    let (hook_entered, hook_release, large) =
                        (hook_entered.clone(), hook_release.clone(), large.clone());
                    async move {
                        if !nested {
                            return Ok(None);
                        }
                        hook_entered.resolve(());
                        hook_release.wait().await;
                        let serde_json::Value::Object(arguments) = json!({ "text": large }) else {
                            unreachable!("an object literal")
                        };
                        Ok(Some(BeforeToolDecision {
                            arguments: Some(arguments),
                            block: None,
                        }))
                    }
                    .boxed()
                })),
                ..ToolHooks::default()
            },
            None,
        )
        .unwrap();
    }
    add_tool(
        &setup.registry,
        tool("batch", |_, api, cx| async move {
            exec(&api, "slow", json!({ "text": "asked" }), &cx).await?;
            Ok(ToolExecutionResult::default())
        }),
        None,
    )
    .unwrap();
    let chat = open(&setup).await;
    let (stream, events) = listen(&chat.harness, chat.root.id()).await;
    let submission = chat
        .root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    hook_entered.wait().await;
    let slot = nested_slots(&chat).await[0].clone();
    assert_eq!(
        (&slot["status"], &slot["arguments"]),
        (&json!("pending"), &json!({ "text": "asked" }))
    );
    hook_release.resolve(());
    running.wait().await;
    let slot = nested_slots(&chat).await[0].clone();
    assert_eq!(
        (&slot["status"], &slot["arguments"]),
        (&json!("running"), &json!({ "text": large }))
    );
    release.resolve(());
    submission.wait(context()).await.unwrap();
    chat.harness.wait_for_idle(context()).await.unwrap();
    stream.stop().await;
    // The start event carries the arguments the call runs with; the task input keeps the ones it was made with.
    let start = lock(&events)
        .iter()
        .find_map(|event| match event {
            AgentEvent::ToolExecutionStart { call, args } if call.tool_call_id == "c1/1" => {
                Some(plain(args))
            }
            _ => None,
        })
        .expect("the nested call starts");
    assert_eq!(start, json!({ "text": large }));
    let nested = tool_tasks(&chat.harness)
        .await
        .into_iter()
        .find(super::super::nested_support::is_nested)
        .expect("a nested task");
    let ToolTaskInput::Nested { call, .. } = super::super::nested_support::input_of(&nested) else {
        unreachable!("a nested input")
    };
    assert_eq!(
        serde_json::Value::Object(call.arguments),
        json!({ "text": "asked" })
    );
    chat.harness.close(context()).await.unwrap();
}

/// `{ callId, status, summary }` of each nested slot.
fn slot_summaries(slots: &serde_json::Value) -> Vec<serde_json::Value> {
    slots
        .as_array()
        .expect("a slot list")
        .iter()
        .map(|slot| {
            let mut picked = json!({ "callId": slot["callId"], "status": slot["status"] });
            if let Some(summary) = slot.get("summary") {
                picked["summary"] = summary.clone();
            }
            picked
        })
        .collect()
}

#[tokio::test]
async fn finds_each_nested_calls_slot_after_slots_in_the_middle_were_removed() {
    let setup = setup();
    add_tool(&setup.registry, echo_tool(|_| {}).0, None).unwrap();
    add_tool(
        &setup.registry,
        tool("inner", |_, api, cx| async move {
            exec(&api, "echo", json!({ "text": "m1" }), &cx).await?;
            exec(&api, "echo", json!({ "text": "m2" }), &cx).await?;
            Ok(ToolExecutionResult::default())
        }),
        None,
    )
    .unwrap();
    let before = deferred::<()>();
    let checked = deferred::<()>();
    let slots: Arc<Mutex<serde_json::Value>> = Arc::default();
    {
        let (before, checked, sink) = (before.clone(), checked.clone(), Arc::clone(&slots));
        add_tool(
            &setup.registry,
            tool("batch", move |_, api, cx| {
                let (before, checked, sink) = (before.clone(), checked.clone(), Arc::clone(&sink));
                async move {
                    exec(&api, "echo", json!({ "text": "n1" }), &cx).await?;
                    // n2 makes m1 and m2 and settles, which removes them from between n2 and n3.
                    exec(&api, "inner", json!({}), &cx).await?;
                    exec(&api, "echo", json!({ "text": "n3" }), &cx).await?;
                    exec(&api, "echo", json!({ "text": "n4" }), &cx).await?;
                    let live = api.snapshot(&LIVE_DOC, api.conversation_id(), &cx).await?;
                    *lock(&sink) = live
                        .and_then(|live| live.get("nestedTools").map(plain))
                        .unwrap_or_else(|| json!([]));
                    before.resolve(());
                    checked.wait().await;
                    Ok(ToolExecutionResult::default())
                }
            }),
            None,
        )
        .unwrap();
    }
    let chat = open(&setup).await;
    let submission = chat
        .root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    before.wait().await;
    let summaries = slot_summaries(&lock(&slots));
    let expected: Vec<serde_json::Value> = summaries
        .iter()
        .zip(["c1/1", "c1/2", "c1/3", "c1/4"])
        .map(|(slot, call_id)| {
            assert!(slot["summary"]["durationMs"].is_number(), "{slot}");
            json!({
                "callId": call_id,
                "status": "done",
                "summary": { "isError": false, "durationMs": slot["summary"]["durationMs"] },
            })
        })
        .collect();
    assert_eq!(summaries, expected);
    assert_eq!(summaries.len(), 4);
    checked.resolve(());
    submission.wait(context()).await.unwrap();
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn shows_a_finished_nested_call_as_a_done_slot_with_its_summary_until_its_caller_settles() {
    let setup = setup();
    let release = deferred::<()>();
    let checked = deferred::<()>();
    // Diagnostics win over output for the error text, which is cut to 500 characters.
    add_tool(
        &setup.registry,
        tool("verbose", |_, _, _| async {
            Ok(ToolExecutionResult {
                output: Some(vec![text_item("ignored")]),
                is_error: Some(true),
                diagnostics: Some(vec![ToolDiagnostic {
                    severity: ToolDiagnosticSeverity::Error,
                    code: None,
                    message: "e".repeat(600),
                }]),
                ..ToolExecutionResult::default()
            })
        }),
        None,
    )
    .unwrap();
    let usage = json!({
        "input": 1, "output": 2, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 3,
        "cost": { "input": 0.1, "output": 0.2, "cacheRead": 0, "cacheWrite": 0, "total": 0.3 },
    });
    add_tool(&setup.registry, echo_tool(|_| {}).0, None).unwrap();
    {
        let usage: eukhe_types::pi_ai::Usage = serde_json::from_value(usage.clone()).unwrap();
        add_tool(
            &setup.registry,
            tool("paid", move |_, _, _| async move {
                Ok(ToolExecutionResult {
                    usage: Some(usage),
                    ..ToolExecutionResult::default()
                })
            }),
            None,
        )
        .unwrap();
    }
    // An error with mixed content: programs get the list, the summary its text.
    add_tool(
        &setup.registry,
        tool("broken", |_, _, _| async {
            let image = serde_json::from_value(
                json!({ "type": "image", "data": "AAAA", "mimeType": "image/png" }),
            )
            .unwrap();
            Ok(ToolExecutionResult {
                output: Some(vec![text_item("bad image"), image]),
                is_error: Some(true),
                ..ToolExecutionResult::default()
            })
        }),
        None,
    )
    .unwrap();
    {
        let (release, checked) = (release.clone(), checked.clone());
        add_tool(
            &setup.registry,
            tool("batch", move |_, api, cx| {
                let (release, checked) = (release.clone(), checked.clone());
                async move {
                    exec(&api, "echo", json!({ "text": "a" }), &cx).await?;
                    exec(&api, "missing", json!({}), &cx).await?;
                    exec(&api, "paid", json!({}), &cx).await?;
                    exec(&api, "broken", json!({}), &cx).await?;
                    exec(&api, "verbose", json!({}), &cx).await?;
                    checked.resolve(());
                    release.wait().await;
                    Ok(ToolExecutionResult::default())
                }
            }),
            None,
        )
        .unwrap();
    }
    let chat = open(&setup).await;
    let submission = chat
        .root
        .submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap();
    checked.wait().await;
    let summaries = slot_summaries(&nested_slots(&chat).await);
    let duration = |index: usize| {
        let duration = summaries[index]["summary"]["durationMs"].clone();
        assert!(duration.is_number(), "{}", summaries[index]);
        duration
    };
    assert_eq!(
        summaries,
        [
            json!({ "callId": "c1/1", "status": "done", "summary": { "isError": false, "durationMs": duration(0) } }),
            json!({
                "callId": "c1/2",
                "status": "done",
                "summary": { "isError": true, "error": "Tool missing is not available" },
            }),
            json!({
                "callId": "c1/3",
                "status": "done",
                "summary": { "isError": false, "durationMs": duration(2), "usage": usage },
            }),
            json!({
                "callId": "c1/4",
                "status": "done",
                "summary": { "isError": true, "durationMs": duration(3), "error": "bad image" },
            }),
            json!({
                "callId": "c1/5",
                "status": "done",
                "summary": { "isError": true, "durationMs": duration(4), "error": "e".repeat(500) },
            }),
        ]
    );
    release.resolve(());
    submission.wait(context()).await.unwrap();
    super::super::nested_support::assert_live_empty(&chat.harness, chat.root.id()).await;
    chat.harness.close(context()).await.unwrap();
}
