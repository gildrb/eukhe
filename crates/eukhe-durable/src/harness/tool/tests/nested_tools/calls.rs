//! Nested calls: tasks, call IDs, hooks, keys, usage, and the results callers
//! get.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use eukhe_pi_ai::typebox::Type;
use eukhe_types::pi_ai::{JsonValue as PiJsonValue, Usage, UsageCost};
use futures::FutureExt;
use serde_json::json;

use super::super::nested_support::{
    call_with, echo_tool, exec, exec_key, input_of, lock, nested_text, plain, results, run_once,
    taken, text_result, tool_tasks, Slot,
};
use super::super::support::{done, result_text, tool, tool_with};
use super::setup;
use crate::harness::define::define_tool;
use crate::harness::tests::support::{add_hooks, add_tool, context, tool_task};
use crate::harness::tool::{ToolTaskInput, NESTED_RESULT_DOC, TOOL_TASK};
use crate::harness::types::{
    BeforeToolDecision, NestedToolExecutionResult, ToolCallParent, ToolDiagnostic,
    ToolDiagnosticSeverity, ToolExecutionResult, ToolHooks, ToolRegistration,
};
use crate::harness::usage::USAGE_DOC;
use crate::types::{SubmissionStatus, TaskId};

fn usage() -> Usage {
    Usage {
        input: 1,
        output: 2,
        cache_read: 0,
        cache_write: 0,
        total_tokens: 3,
        cost: UsageCost {
            input: 0.1,
            output: 0.2,
            cache_read: 0.0,
            cache_write: 0.0,
            total: 0.3,
        },
        ..Usage::default()
    }
}

#[tokio::test]
async fn runs_a_nested_call_as_its_own_tool_task_and_returns_its_result_to_the_caller_not_the_transcript(
) {
    let setup = setup();
    let (echo, _) = echo_tool(|_| {});
    add_tool(&setup.registry, echo, None).unwrap();
    let nested: Slot<NestedToolExecutionResult> = Arc::default();
    let sink = Arc::clone(&nested);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                let result = exec(&api, "echo", json!({ "text": "a" }), &cx).await?;
                let text = nested_text(&result);
                *lock(&sink) = Some(result);
                Ok(text_result(&format!("got {text}")))
            }
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    let tasks = tool_tasks(&ran.harness).await;
    let (parent, child) = (&tasks[0], &tasks[1]);
    let nested = taken(&nested);
    assert!(nested.duration_ms.is_some());
    assert_eq!(
        nested,
        NestedToolExecutionResult {
            task_id: child.id,
            structured_output: Some(eukhe_chord::json::JsonValue::from("echo a")),
            is_error: false,
            details: None,
            diagnostics: Vec::new(),
            usage: None,
            duration_ms: nested.duration_ms,
        }
    );
    // One result entry: the model-issued call's, which records nothing of its nested calls.
    let messages = results(&ran.entries);
    let listed: Vec<(String, String)> = messages
        .iter()
        .map(|result| (result.tool_call_id.clone(), result_text(result)))
        .collect();
    assert_eq!(listed, [("c1".to_owned(), "got echo a".to_owned())]);
    assert_eq!(messages[0].nested_calls, None);
    assert!(matches!(
        input_of(parent),
        ToolTaskInput::Model { call_id, .. } if call_id == "c1"
    ));
    assert_eq!(child.owner, Some(parent.id));
    assert_eq!(
        plain(&child.input),
        json!({
            "kind": "nested",
            "parent": plain(&parent.id),
            "parentCallId": "c1",
            "key": "1",
            "call": { "type": "toolCall", "id": "c1/1", "name": "echo", "arguments": { "text": "a" } },
        })
    );
    // The receipt stays small: the result lived in the caller's documents, which retired with it.
    assert_eq!(
        plain(&child.state),
        json!({ "status": "terminal", "outcome": { "status": "completed", "result": { "kind": "nested" } } })
    );
    assert_eq!(
        ran.harness
            .snapshot(
                &NESTED_RESULT_DOC,
                (parent.id, &child.id.to_string()),
                context()
            )
            .await
            .unwrap(),
        None
    );
    super::super::nested_support::assert_live_empty(&ran.harness, ran.root.id()).await;
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn gives_each_nested_call_its_own_task_and_call_id() {
    let setup = setup();
    let seen: Arc<Mutex<Vec<(TaskId, String)>>> = Arc::default();
    let sink = Arc::clone(&seen);
    add_tool(
        &setup.registry,
        tool("who", move |_, api, _| {
            lock(&sink).push((api.task_id(), api.call_id().to_owned()));
            async { Ok(ToolExecutionResult::default()) }
        }),
        None,
    )
    .unwrap();
    add_tool(
        &setup.registry,
        tool("batch", |_, api, cx| async move {
            let (a, b) = futures::join!(
                exec_key(&api, "who", json!({}), &cx, "a"),
                exec_key(&api, "who", json!({}), &cx, "b")
            );
            a?;
            b?;
            Ok(ToolExecutionResult::default())
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    let seen = lock(&seen).clone();
    let mut call_ids: Vec<&str> = seen.iter().map(|(_, id)| id.as_str()).collect();
    call_ids.sort_unstable();
    assert_eq!(call_ids, ["c1/a", "c1/b"]);
    assert_ne!(seen[0].0, seen[1].0);
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn runs_the_tool_hooks_on_nested_calls_which_see_their_parent() {
    let setup = setup();
    let (echo, runs) = echo_tool(|_| {});
    add_tool(&setup.registry, echo, None).unwrap();
    let parents: Arc<Mutex<Vec<Option<ToolCallParent>>>> = Arc::default();
    let sink = Arc::clone(&parents);
    add_hooks(
        &setup.registry,
        tool_task(),
        ToolHooks {
            before_tool: Some(Arc::new(move |call, _, _| {
                lock(&sink).push(call.parent.clone());
                let secret = call.parent.is_some()
                    && call.arguments.get("text") == Some(&PiJsonValue::from("secret"));
                let decision = secret.then(|| BeforeToolDecision {
                    block: Some("no secrets".to_owned()),
                    ..BeforeToolDecision::default()
                });
                futures::future::ready(Ok(decision)).boxed()
            })),
            after_tool: Some(Arc::new(|call, result, _, _| {
                let replaced = call.parent.is_some().then(|| ToolExecutionResult {
                    output: Some(vec![super::super::nested_support::text_item("rewritten")]),
                    ..result.clone()
                });
                futures::future::ready(Ok(replaced)).boxed()
            })),
        },
        None,
    )
    .unwrap();
    let nested: Arc<Mutex<Vec<NestedToolExecutionResult>>> = Arc::default();
    let sink = Arc::clone(&nested);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                let first = exec(&api, "echo", json!({ "text": "secret" }), &cx).await?;
                lock(&sink).push(first);
                let second = exec(&api, "echo", json!({ "text": "public" }), &cx).await?;
                lock(&sink).push(second);
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    let parent = tool_tasks(&ran.harness).await[0].id;
    let by_parent = Some(ToolCallParent {
        task_id: parent,
        call_id: "c1".to_owned(),
    });
    assert_eq!(*lock(&parents), [None, by_parent.clone(), by_parent]);
    let nested = lock(&nested).clone();
    assert!(nested[0].is_error);
    assert_eq!(
        nested[0].diagnostics,
        [ToolDiagnostic {
            severity: ToolDiagnosticSeverity::Error,
            code: Some("blocked".to_owned()),
            message: "Tool call blocked: no secrets".to_owned(),
        }]
    );
    assert_eq!(nested_text(&nested[1]), "rewritten");
    assert_eq!(runs.load(Ordering::SeqCst), 1);
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn returns_an_error_result_for_an_unavailable_tool_and_invalid_arguments() {
    let setup = setup();
    add_tool(&setup.registry, echo_tool(|_| {}).0, None).unwrap();
    let nested: Arc<Mutex<Vec<NestedToolExecutionResult>>> = Arc::default();
    let sink = Arc::clone(&nested);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                let missing = exec(&api, "missing", json!({}), &cx).await?;
                lock(&sink).push(missing);
                let invalid =
                    exec(&api, "echo", json!({ "text": { "not": "a string" } }), &cx).await?;
                lock(&sink).push(invalid);
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    let listed: Vec<(bool, Option<String>)> = lock(&nested)
        .iter()
        .map(|result| (result.is_error, result.diagnostics[0].code.clone()))
        .collect();
    assert_eq!(
        listed,
        [
            (true, Some("tool_unavailable".to_owned())),
            (true, Some("invalid_arguments".to_owned())),
        ]
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn returns_the_call_a_key_already_names_and_rejects_reusing_the_key_for_another_call() {
    let setup = setup();
    let (echo, runs) = echo_tool(|_| {});
    add_tool(&setup.registry, echo, None).unwrap();
    let reused: Slot<NestedToolExecutionResult> = Arc::default();
    let sink = Arc::clone(&reused);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                exec_key(&api, "echo", json!({ "text": "a" }), &cx, "k").await?;
                let again = exec_key(&api, "echo", json!({ "text": "a" }), &cx, "k").await?;
                *lock(&sink) = Some(again);
                exec_key(&api, "echo", json!({ "text": "b" }), &cx, "k").await?;
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    assert_eq!(runs.load(Ordering::SeqCst), 1);
    assert_eq!(nested_text(&taken(&reused)), "echo a");
    let text = result_text(&results(&ran.entries)[0]);
    assert!(
        text.contains("Nested call c1/k was already made with another tool or other arguments"),
        "{text}"
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn matches_a_reused_keys_arguments_regardless_of_key_order() {
    let setup = setup();
    let runs = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&runs);
    add_tool(
        &setup.registry,
        define_tool(ToolRegistration::new(
            "pair",
            "pair",
            Type::object([("a", Type::string()), ("b", Type::string())]),
            move |args, _, _| {
                counted.fetch_add(1, Ordering::SeqCst);
                let text = format!(
                    "{}{}",
                    args["a"].as_str().unwrap_or_default(),
                    args["b"].as_str().unwrap_or_default()
                );
                async move { Ok(text_result(&text)) }
            },
        )),
        None,
    )
    .unwrap();
    let nested: Arc<Mutex<Vec<NestedToolExecutionResult>>> = Arc::default();
    let sink = Arc::clone(&nested);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                let first = exec_key(&api, "pair", json!({ "a": "x", "b": "y" }), &cx, "k").await?;
                lock(&sink).push(first);
                let second =
                    exec_key(&api, "pair", json!({ "b": "y", "a": "x" }), &cx, "k").await?;
                lock(&sink).push(second);
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    assert_eq!(runs.load(Ordering::SeqCst), 1);
    let texts: Vec<String> = lock(&nested).iter().map(nested_text).collect();
    assert_eq!(texts, ["xy", "xy"]);
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn records_a_nested_calls_usage_under_its_tool() {
    let setup = setup();
    add_tool(
        &setup.registry,
        tool("paid", |_, _, _| async {
            Ok(ToolExecutionResult {
                usage: Some(usage()),
                ..ToolExecutionResult::default()
            })
        }),
        None,
    )
    .unwrap();
    add_tool(
        &setup.registry,
        tool("batch", |_, api, cx| async move {
            exec(&api, "paid", json!({}), &cx).await?;
            Ok(ToolExecutionResult::default())
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    let state = ran
        .harness
        .snapshot(&USAGE_DOC, ran.root.id(), context())
        .await
        .unwrap()
        .expect("pi.usage exists");
    assert_eq!(
        plain(&eukhe_chord::json::JsonValue::Object(state))["tools"],
        json!({ "paid": plain(&usage()) })
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn rejects_explicit_keys_that_are_empty_have_a_slash_are_proto_or_are_positive_integers() {
    let setup = setup();
    add_tool(&setup.registry, echo_tool(|_| {}).0, None).unwrap();
    let errors: Arc<Mutex<Vec<String>>> = Arc::default();
    let sink = Arc::clone(&errors);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                for key in ["", "a/b", "__proto__", "7"] {
                    if let Err(error) = exec_key(&api, "echo", json!({}), &cx, key).await {
                        lock(&sink).push(error.to_string());
                    }
                }
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    let rule = r#"must be non-empty, without "/", not "__proto__", and not a positive integer"#;
    assert_eq!(
        *lock(&errors),
        [
            format!(r#"Nested call key "" {rule}"#),
            format!(r#"Nested call key "a/b" {rule}"#),
            format!(r#"Nested call key "__proto__" {rule}"#),
            format!(r#"Nested call key "7" {rule}"#),
        ]
    );
    ran.harness.close(context()).await.unwrap();
}

/// TS repairs the arguments to `{ text: undefined }`, which strict JSON
/// cannot hold; Rust deviation: the repair drops `text`, the JSON form of the
/// same value.
#[tokio::test]
async fn runs_a_nested_call_whose_repaired_arguments_set_an_optional_property_to_undefined() {
    let setup = setup();
    let seen: Arc<Mutex<Vec<PiJsonValue>>> = Arc::default();
    let sink = Arc::clone(&seen);
    add_tool(
        &setup.registry,
        tool_with(
            "repaired",
            move |args, _, _| {
                lock(&sink).push(args);
                async { Ok(ToolExecutionResult::default()) }
            },
            |tool| {
                tool.prepare_arguments = Some(Arc::new(|_| Ok(json!({}))));
            },
        ),
        None,
    )
    .unwrap();
    let result: Slot<NestedToolExecutionResult> = Arc::default();
    let sink = Arc::clone(&result);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                let result = exec(&api, "repaired", json!({ "text": "x" }), &cx).await?;
                *lock(&sink) = Some(result);
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    assert!(!taken(&result).is_error);
    assert_eq!(*lock(&seen), [json!({})]);
    ran.harness.close(context()).await.unwrap();
}

/// TS makes the result commit throw with details holding a `bigint`, which is
/// not JSON. Rust deviation: `JsonValue` cannot hold one, so the result
/// carries a usage counter beyond `Number.MAX_SAFE_INTEGER`, which strict
/// JSON conversion rejects in the same result commit.
#[tokio::test]
async fn gives_callers_a_result_with_its_task_id_and_only_diagnostics_for_a_nested_call_the_scheduler_faulted(
) {
    let setup = setup();
    add_tool(
        &setup.registry,
        tool("echo", |_, _, _| async {
            Ok(ToolExecutionResult {
                usage: Some(Usage {
                    input: u64::MAX,
                    ..Usage::default()
                }),
                ..ToolExecutionResult::default()
            })
        }),
        None,
    )
    .unwrap();
    let result: Slot<NestedToolExecutionResult> = Arc::default();
    let sink = Arc::clone(&result);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                let result = exec(&api, "echo", json!({ "text": "a" }), &cx).await?;
                *lock(&sink) = Some(result);
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    let child = tool_tasks(&ran.harness).await[1].clone();
    assert_eq!(plain(&child.state)["status"], "terminal");
    assert_eq!(plain(&child.state)["outcome"]["status"], "faulted");
    let result = taken(&result);
    assert_eq!(result.task_id, child.id);
    assert!(result.is_error);
    assert_eq!(result.structured_output, None);
    assert_eq!(result.details, None);
    assert_eq!(result.diagnostics.len(), 1);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.severity, ToolDiagnosticSeverity::Error);
    assert_eq!(diagnostic.code.as_deref(), Some("faulted"));
    assert!(
        diagnostic.message.contains("Tool echo failed"),
        "{}",
        diagnostic.message
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn gives_callers_what_a_schema_less_tool_streamed_before_it_threw() {
    let setup = setup();
    add_tool(
        &setup.registry,
        tool("fails", |_, api, _| async move {
            api.output(
                crate::harness::types::ToolOutputChunk::Text("half way\n"),
                None,
            )?;
            Err(crate::session::SessionError::error("broke"))
        }),
        None,
    )
    .unwrap();
    let result: Slot<NestedToolExecutionResult> = Arc::default();
    let sink = Arc::clone(&result);
    add_tool(
        &setup.registry,
        tool("batch", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                let result = exec(&api, "fails", json!({}), &cx).await?;
                *lock(&sink) = Some(result);
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run_once(&setup, vec![call_with("batch", json!({}), "c1"), done()]).await;
    let result = taken(&result);
    assert!(result.is_error);
    assert_eq!(nested_text(&result), "half way\n");
    let listed: Vec<(Option<&str>, &str)> = result
        .diagnostics
        .iter()
        .map(|diagnostic| (diagnostic.code.as_deref(), diagnostic.message.as_str()))
        .collect();
    assert_eq!(listed, [(Some("tool_error"), "broke")]);
    ran.harness.close(context()).await.unwrap();
}

#[test]
fn migrates_version_1_tool_task_input_to_a_model_issued_call() {
    let json = |text: &str| eukhe_chord::json::JsonValue::parse(text).unwrap();
    let migrated = TOOL_TASK
        .erase()
        .definition()
        .migrate(
            &json(r#"{"assistant":3,"callId":"c1"}"#),
            &json(r#"{"phase":"call"}"#),
            1,
        )
        .expect("ToolTask migrates")
        .unwrap();
    assert_eq!(
        plain(&migrated.input),
        json!({ "kind": "model", "assistant": 3, "callId": "c1" })
    );
    assert_eq!(plain(&migrated.checkpoint), json!({ "phase": "call" }));
}
