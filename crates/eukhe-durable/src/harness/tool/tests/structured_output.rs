//! Port of `test/harness-structured-output.test.ts`.

use std::sync::Arc;

use eukhe_chord::json::{from_json, JsonValue};
use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;
use eukhe_pi_ai::typebox::{TSchema, Type};
use eukhe_types::pi_ai::{TextContent, UserContentBlock};
use futures::FutureExt;

use super::nested_support::{
    call, codes, direct, json, lock, nested, probe, returning, run_probe, Received,
};
use super::support::{done, submit_and_wait};
use crate::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use crate::harness::events::{watch_events, AgentEvent};
use crate::harness::tests::chat_support::{chat_setup, open_chat, ChatEnv, ChatSetup};
use crate::harness::tests::support::{add_hooks, add_tool, context, tool_task};
use crate::harness::tool::NESTED_RESULT_DOC;
use crate::harness::types::{
    NestedToolExecutionResult, ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionResult,
    ToolHooks, ToolRegistration,
};
use crate::storage::MemoryStorage;
use crate::tools::{create_bash_tool, BashToolOptions};
use crate::types::{CommitChange, DocumentCommitChange};

fn setup() -> ChatSetup {
    chat_setup(RegisterFauxProviderOptions::default())
}

/// TS `Count`.
fn count() -> TSchema {
    Type::object([("count", Type::number())])
}

fn with_count(tool: &mut ToolRegistration) {
    tool.structured_output_schema = Some(count().into());
}

fn text(value: &str) -> UserContentBlock {
    UserContentBlock::Text(TextContent::new(value))
}

fn output(items: Vec<UserContentBlock>) -> ToolExecutionResult {
    ToolExecutionResult {
        output: Some(items),
        ..ToolExecutionResult::default()
    }
}

fn structured(value: &str) -> ToolExecutionResult {
    ToolExecutionResult {
        structured_output: Some(json(value)),
        ..ToolExecutionResult::default()
    }
}

fn received_all(received: &Received) -> Vec<NestedToolExecutionResult> {
    lock(received).clone()
}

#[tokio::test]
async fn gives_callers_a_schema_less_tools_output_one_text_as_a_string_one_image_as_itself_else_the_list(
) {
    let image_json = r#"{"type":"image","data":"AAAA","mimeType":"image/png"}"#;
    let image: UserContentBlock = serde_json::from_str(image_json).unwrap();
    let text_json = r#"{"type":"text","text":"one"}"#;
    let cases: Vec<(Vec<UserContentBlock>, JsonValue)> = vec![
        (vec![text("one")], json(r#""one""#)),
        (vec![image.clone()], json(image_json)),
        (Vec::new(), json(r#""""#)),
        (
            vec![text("one"), image.clone()],
            json(&format!("[{text_json},{image_json}]")),
        ),
        (
            vec![text("one"), text("one")],
            json(&format!("[{text_json},{text_json}]")),
        ),
    ];
    for (items, value) in cases {
        let setup = setup();
        add_tool(
            &setup.registry,
            returning("plain", output(items), |_| {}),
            None,
        )
        .unwrap();
        let received = nested(&setup, "plain").await;
        assert_eq!(
            received,
            NestedToolExecutionResult {
                task_id: received.task_id,
                structured_output: Some(value),
                is_error: false,
                details: None,
                diagnostics: Vec::new(),
                usage: None,
                duration_ms: received.duration_ms,
            }
        );
    }
}

#[tokio::test]
async fn gives_callers_the_bounded_output_as_the_model_sees_it_without_the_rendered_diagnostics() {
    let setup = setup();
    let result = ToolExecutionResult {
        diagnostics: Some(vec![ToolDiagnostic {
            severity: ToolDiagnosticSeverity::Info,
            code: None,
            message: "note".to_owned(),
        }]),
        ..output(vec![text("a\nb\nc")])
    };
    add_tool(
        &setup.registry,
        returning("long", result, |tool| {
            tool.output_limits = Some(crate::harness::types::ToolOutputLimits {
                max_lines: Some(1),
                ..Default::default()
            });
        }),
        None,
    )
    .unwrap();
    let received = nested(&setup, "long").await;
    assert_eq!(received.structured_output, Some(json(r#""a\n""#)));
    assert_eq!(codes(&received.diagnostics), [None, Some("truncated")]);
}

#[tokio::test]
async fn stores_exactly_what_callers_and_events_get_without_the_models_output_and_keeps_a_stored_null(
) {
    let setup = setup();
    add_tool(
        &setup.registry,
        returning("plain", output(vec![text("a")]), |_| {}),
        None,
    )
    .unwrap();
    add_tool(
        &setup.registry,
        returning("nothing", structured("null"), |tool| {
            tool.structured_output_schema = Some(Type::null().into());
        }),
        None,
    )
    .unwrap();
    let (registration, received) = probe(vec![
        ("plain", serde_json::json!({})),
        ("nothing", serde_json::json!({})),
    ]);
    add_tool(&setup.registry, registration, None).unwrap();
    setup
        .faux
        .set_responses(vec![call("probe").into(), done().into()]);
    let chat = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    // Rust deviation: TS wraps `storage.commit` to record the created
    // documents; the commit publications carry the same adopted values.
    let stored: Arc<std::sync::Mutex<Vec<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&stored);
    let subscription = chat
        .harness
        .subscribe_commits(Arc::new(move |publication, _| {
            for change in &publication.changes {
                if let CommitChange::Document(DocumentCommitChange::Document {
                    record,
                    value: Some(value),
                    ..
                }) = change
                {
                    if record.kind == NESTED_RESULT_DOC.definition().kind {
                        lock(&sink).push(value.get("result").cloned().unwrap());
                    }
                }
            }
        }))
        .unwrap();
    let stream = watch_events(&chat.harness, chat.root.id(), context())
        .await
        .unwrap();
    let ends: Arc<std::sync::Mutex<Vec<Option<NestedToolExecutionResult>>>> = Arc::default();
    let ending = Arc::clone(&ends);
    stream
        .start(Arc::new(move |batch, _| {
            for event in batch.iter() {
                if let AgentEvent::ToolExecutionEnd { call, result, .. } = event {
                    if call.parent_tool_call_id.is_some() {
                        lock(&ending).push(result.clone());
                    }
                }
            }
            futures::future::ready(Ok(())).boxed()
        }))
        .unwrap();
    submit_and_wait(&chat.root, "go").await;
    chat.harness.wait_for_idle(context()).await.unwrap();
    stream.stop().await;
    drop(subscription);
    chat.harness.close(context()).await.unwrap();

    let received = received_all(&received);
    assert_eq!(received[0].structured_output, Some(json(r#""a""#)));
    assert!(!received[0].is_error);
    assert_eq!(received[1].structured_output, Some(JsonValue::Null));
    assert!(!received[1].is_error);
    let stored: Vec<NestedToolExecutionResult> = lock(&stored)
        .iter()
        .map(|value| from_json(value).unwrap())
        .collect();
    assert_eq!(stored, received);
    let ends: Vec<NestedToolExecutionResult> = lock(&ends)
        .iter()
        .map(|result| result.clone().expect("a nested end carries its result"))
        .collect();
    assert_eq!(ends, received);
}

#[tokio::test]
async fn gives_callers_a_schema_tools_validated_structured_output_which_the_transcript_does_not_store(
) {
    let result = ToolExecutionResult {
        structured_output: Some(json(r#"{"count":3}"#)),
        ..output(vec![text("3 things")])
    };
    let setup = setup();
    add_tool(
        &setup.registry,
        returning("counter", result.clone(), with_count),
        None,
    )
    .unwrap();
    let received = nested(&setup, "counter").await;
    assert_eq!(received.structured_output, Some(json(r#"{"count":3}"#)));
    assert!(!received.is_error);

    let model_setup = self::setup();
    add_tool(
        &model_setup.registry,
        returning("counter", result, with_count),
        None,
    )
    .unwrap();
    let stored = direct(&model_setup, "counter").await;
    assert!(!stored.is_error);
    assert_eq!(stored.content, vec![text("3 things")]);
    let stored = serde_json::to_value(&stored).unwrap();
    assert!(stored.get("structuredOutput").is_none(), "{stored}");
}

#[tokio::test]
async fn turns_structured_output_that_breaks_the_schema_into_an_error_result_for_callers_and_a_report_for_the_models_calls(
) {
    let cases: Vec<(&str, ToolExecutionResult, bool, &str)> = vec![
        (
            "wrong",
            structured(r#"{"count":"three"}"#),
            true,
            "does not match its schema: count:",
        ),
        (
            "missing",
            output(Vec::new()),
            true,
            "returned no structuredOutput",
        ),
        (
            "undeclared",
            structured(r#"{"count":3}"#),
            false,
            "declares no structuredOutputSchema",
        ),
    ];
    for (name, result, schema, message) in cases {
        let extra = |tool: &mut ToolRegistration| {
            if schema {
                with_count(tool);
            }
        };
        let setup = setup();
        add_tool(
            &setup.registry,
            returning(name, result.clone(), extra),
            None,
        )
        .unwrap();
        let received = nested(&setup, name).await;
        assert!(received.is_error);
        // The broken value is dropped; a schema-less tool's error result still carries its output, here none.
        if schema {
            assert_eq!(received.structured_output, None);
        } else {
            assert_eq!(received.structured_output, Some(json(r#""""#)));
        }
        assert_eq!(
            codes(&received.diagnostics),
            [Some("invalid_structured_output")]
        );
        assert!(
            received.diagnostics[0].message.contains(message),
            "{}",
            received.diagnostics[0].message
        );

        let model_setup = self::setup();
        add_tool(&model_setup.registry, returning(name, result, extra), None).unwrap();
        // The model never sees structured output: its call stands, and the host gets a report.
        let stored = direct(&model_setup, name).await;
        assert!(!stored.is_error);
        assert!(!serde_json::to_string(&stored.content)
            .unwrap()
            .contains(message));
        let reports: Vec<String> = model_setup
            .reports()
            .iter()
            .map(ToString::to_string)
            .collect();
        assert!(reports.join("\n").contains(message), "{reports:?}");
    }
}

#[tokio::test]
async fn gives_callers_the_output_of_an_error_result_of_a_tool_without_a_schema() {
    let setup = setup();
    let result = ToolExecutionResult {
        is_error: Some(true),
        ..output(vec![text("bad")])
    };
    add_tool(&setup.registry, returning("bad", result, |_| {}), None).unwrap();
    let received = nested(&setup, "bad").await;
    assert!(received.is_error);
    assert_eq!(received.structured_output, Some(json(r#""bad""#)));
}

#[tokio::test]
async fn gives_callers_no_structured_output_for_an_error_result_the_harness_wrote_only_diagnostics()
{
    let setup = setup();
    let received = nested(&setup, "missing").await;
    assert!(received.is_error);
    assert_eq!(codes(&received.diagnostics), [Some("tool_unavailable")]);
    assert_eq!(received.structured_output, None);
}

#[tokio::test]
async fn lets_an_error_result_of_a_schema_tool_omit_structured_output_and_keeps_none_of_its_output()
{
    let setup = setup();
    let result = ToolExecutionResult {
        is_error: Some(true),
        ..output(vec![text("nope")])
    };
    add_tool(
        &setup.registry,
        returning("fails", result, with_count),
        None,
    )
    .unwrap();
    let received = nested(&setup, "fails").await;
    assert!(received.is_error);
    assert!(received.diagnostics.is_empty());
    assert_eq!(received.structured_output, None);
}

#[tokio::test]
async fn keeps_structured_output_when_after_tool_replaces_the_output_and_validates_one_after_tool_replaces(
) {
    let setup = setup();
    add_tool(
        &setup.registry,
        returning("plain", output(vec![text("secret")]), |_| {}),
        None,
    )
    .unwrap();
    add_tool(
        &setup.registry,
        returning("counter", structured(r#"{"count":1}"#), with_count),
        None,
    )
    .unwrap();
    add_tool(
        &setup.registry,
        returning("other", structured(r#"{"count":1}"#), with_count),
        None,
    )
    .unwrap();
    add_hooks(
        &setup.registry,
        tool_task(),
        ToolHooks {
            after_tool: Some(Arc::new(|call, result, _, _| {
                let replaced = match call.name.as_str() {
                    "other" => ToolExecutionResult {
                        structured_output: Some(json(r#"{"count":"broken"}"#)),
                        ..result.clone()
                    },
                    "probe" => result.clone(),
                    _ => ToolExecutionResult {
                        output: Some(vec![text("rewritten")]),
                        ..result.clone()
                    },
                };
                futures::future::ready(Ok(Some(replaced))).boxed()
            })),
            ..ToolHooks::default()
        },
        None,
    )
    .unwrap();
    let (registration, received) = probe(vec![
        ("plain", serde_json::json!({})),
        ("counter", serde_json::json!({})),
        ("other", serde_json::json!({})),
    ]);
    add_tool(&setup.registry, registration, None).unwrap();
    let chat = run_probe(&setup).await;
    chat.harness.close(context()).await.unwrap();
    let received = received_all(&received);
    // A schema-less tool's value is its output, so redacting the output redacts what programs get.
    assert_eq!(received[0].structured_output, Some(json(r#""rewritten""#)));
    assert_eq!(received[1].structured_output, Some(json(r#"{"count":1}"#)));
    assert!(received[2].is_error);
    assert_eq!(
        codes(&received[2].diagnostics),
        [Some("invalid_structured_output")]
    );
}

#[tokio::test]
async fn gives_callers_of_bash_its_retained_output_and_exit_code_also_for_a_nonzero_exit() {
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-structured-")
        .tempdir()
        .expect("temp dir");
    let setup = setup();
    add_tool(
        &setup.registry,
        create_bash_tool(BashToolOptions::default()),
        None,
    )
    .unwrap();
    let (registration, received) = probe(vec![
        ("bash", serde_json::json!({ "command": "printf ok" })),
        (
            "bash",
            serde_json::json!({ "command": "printf bad; exit 4" }),
        ),
    ]);
    add_tool(&setup.registry, registration, None).unwrap();
    setup
        .faux
        .set_responses(vec![call("probe").into(), done().into()]);
    let env: Arc<dyn ExecutionEnv> = Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: directory.path().to_string_lossy().into_owned(),
        ..NativeExecutionEnvOptions::default()
    }));
    let chat = open_chat(
        Arc::new(MemoryStorage::new()),
        &setup,
        Some(ChatEnv::One(env)),
    )
    .await
    .unwrap();
    submit_and_wait(&chat.root, "go").await;
    chat.harness.close(context()).await.unwrap();
    let received = received_all(&received);
    assert!(!received[0].is_error);
    assert_eq!(
        received[0].structured_output,
        Some(json(r#"{"output":"ok","truncated":false,"exitCode":0}"#))
    );
    assert!(received[1].is_error);
    assert_eq!(
        received[1].structured_output,
        Some(json(r#"{"output":"bad","truncated":false,"exitCode":4}"#))
    );
    assert_eq!(codes(&received[1].diagnostics), [Some("exit_code")]);
}
