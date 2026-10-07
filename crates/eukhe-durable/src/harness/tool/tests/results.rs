//! Port of `test/harness-tools.test.ts` `describe("tool results")`.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::JsonValue;
use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, ImageContent, JsonValue as PiJsonValue, Message, TextContent,
    UserContentBlock,
};
use futures::FutureExt;

use super::support::{
    calls, content_text, done, empty_content, result_text, results, run, run_with, submit_and_wait,
    tool, tool_with,
};
use crate::entries::TOOL_RESULT_ENTRY;
use crate::env::{ShellOutputSkip, ShellOutputWindow};
use crate::harness::agent::AGENT_DOC;
use crate::harness::define::{define_extension, hook};
use crate::harness::tests::chat_support::{all_entries, chat_setup, ChatSetup};
use crate::harness::tests::support::{add_hooks, add_tool, context, generation_task, tool_task};
use crate::harness::types::{
    AgentChange, BeforeToolDecision, ConversationCreateOptions, Extension, ExtensionsChange,
    FieldChange, GenerationHooks, HarnessSettings, ModelRef, OutputRetain, PartialProgressPolicy,
    ToolControl, ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionResult, ToolHooks,
    ToolOutputChunk, ToolOutputLimits, ToolRegistration, ToolsChange,
};
use crate::harness::{Conversation, Harness};
use crate::session::SessionError;
use crate::tasks::{define_task, TaskDefinition};
use crate::types::{
    ConversationId, ConversationOwnership, EntryId, SubmissionStatus, TaskOptions, TaskOwnership,
    TaskQuery, TaskStatus,
};

fn setup() -> ChatSetup {
    chat_setup(RegisterFauxProviderOptions::default())
}

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn harness_error(message: &str) -> String {
    format!("<harness>\n[error] {message}\n</harness>")
}

fn text(text: &str) -> UserContentBlock {
    UserContentBlock::Text(TextContent::new(text))
}

fn limits(max_lines: u64, retain: Option<OutputRetain>) -> ToolOutputLimits {
    ToolOutputLimits {
        max_bytes: None,
        max_lines: Some(max_lines),
        retain,
    }
}

fn locked<T: Clone>(value: &Mutex<T>) -> T {
    value.lock().unwrap_or_else(PoisonError::into_inner).clone()
}

#[tokio::test(flavor = "multi_thread")]
async fn uses_retained_output_and_the_last_details_when_the_result_omits_them_with_diagnostics_in_order(
) {
    let setup = setup();
    add_tool(
        &setup.registry,
        tool_with(
            "log",
            |_, api, cx| async move {
                api.output(ToolOutputChunk::Text("line 1\n"), None)?;
                api.output(ToolOutputChunk::Bytes(b"line 2\nline 3\n"), None)?;
                api.diagnostic(ToolDiagnostic {
                    severity: ToolDiagnosticSeverity::Info,
                    code: None,
                    message: "from api".to_owned(),
                })?;
                api.details(json(r#"{"step":1}"#), &cx).await?;
                api.details(json(r#"{"step":2}"#), &cx).await?;
                Ok(ToolExecutionResult {
                    diagnostics: Some(vec![ToolDiagnostic {
                        severity: ToolDiagnosticSeverity::Warn,
                        code: None,
                        message: "from result".to_owned(),
                    }]),
                    ..ToolExecutionResult::default()
                })
            },
            |tool| tool.output_limits = Some(limits(2, None)),
        ),
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[("log", serde_json::json!({}), "c1")]).into(),
            done().into(),
        ],
    )
    .await;
    let [result] = results(&ran.entries).try_into().unwrap();
    assert_eq!(result.details, Some(serde_json::json!({ "step": 2 })));
    assert_eq!(
        result_text(&result),
        "line 1\nline 2\n|<harness>\n[info] from api\n[warn] from result\n[warn] Output truncated to its beginning: 1 lines, 7 bytes dropped\n</harness>"
    );
    let entry = ran
        .entries
        .iter()
        .find(|candidate| TOOL_RESULT_ENTRY.is(Some(candidate)))
        .unwrap();
    let typed = TOOL_RESULT_ENTRY.narrow(entry.clone()).unwrap().unwrap();
    let codes: Vec<Option<&str>> = typed
        .data()
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code.as_deref())
        .collect();
    assert_eq!(codes, [None, None, Some("truncated")]);
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn offers_the_tail_window_with_the_configured_pace_not_a_head_window_and_accepts_skipped_output(
) {
    let setup = setup();
    setup.settings.set(HarnessSettings {
        progress: Some(PartialProgressPolicy {
            output_interval_ms: Some(250.0),
            ..PartialProgressPolicy::default()
        }),
        ..HarnessSettings::default()
    });
    let windows: Arc<Mutex<Vec<Option<ShellOutputWindow>>>> = Arc::default();
    let tailed = Arc::clone(&windows);
    add_tool(
        &setup.registry,
        tool_with(
            "tailed",
            move |_, api, _| {
                let windows = Arc::clone(&tailed);
                async move {
                    windows
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(api.output_window());
                    api.output(ToolOutputChunk::Text("dropped\n"), None)?;
                    api.output(
                        ToolOutputChunk::Text("x\ny\n"),
                        Some(ShellOutputSkip {
                            bytes: 8,
                            newlines: 1,
                            ends_with_newline: true,
                        }),
                    )?;
                    Ok(ToolExecutionResult::default())
                }
            },
            |tool| tool.output_limits = Some(limits(1, Some(OutputRetain::Tail))),
        ),
        None,
    )
    .unwrap();
    let headed = Arc::clone(&windows);
    add_tool(
        &setup.registry,
        tool_with(
            "headed",
            move |_, api, _| {
                headed
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(api.output_window());
                async { Ok(ToolExecutionResult::default()) }
            },
            |tool| tool.output_limits = Some(limits(1, None)),
        ),
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[
                ("tailed", serde_json::json!({}), "c1"),
                ("headed", serde_json::json!({}), "c2"),
            ])
            .into(),
            done().into(),
        ],
    )
    .await;
    let windows = locked(&windows);
    assert!(windows.contains(&Some(ShellOutputWindow {
        max_bytes: 50 * 1024,
        max_lines: 1,
        min_interval_ms: 250.0,
        bytes_per_second: 100.0 * 1024.0,
    })));
    assert!(windows.contains(&None));
    // 8 bytes written, 8 skipped, then "x\n" dropped by the window: 3 lines, 18 bytes in all.
    let tailed = results(&ran.entries)
        .into_iter()
        .find(|result| result.tool_call_id == "c1")
        .unwrap();
    assert_eq!(
        result_text(&tailed),
        "y\n|<harness>\n[warn] Output truncated to its end: 3 lines, 18 bytes dropped\n</harness>"
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn bounds_explicit_text_content_and_keeps_other_content() {
    let setup = setup();
    add_tool(
        &setup.registry,
        tool_with(
            "big",
            |_, _, _| async {
                Ok(ToolExecutionResult {
                    content: Some(vec![
                        text("a\nb\n"),
                        UserContentBlock::Image(ImageContent {
                            data: "AAAA".to_owned(),
                            mime_type: "image/png".to_owned(),
                        }),
                        text("c\nd\n"),
                    ]),
                    ..ToolExecutionResult::default()
                })
            },
            |tool| tool.output_limits = Some(limits(2, Some(OutputRetain::Tail))),
        ),
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[("big", serde_json::json!({}), "c1")]).into(),
            done().into(),
        ],
    )
    .await;
    assert_eq!(
        result_text(&results(&ran.entries)[0]),
        "[image]|c\nd\n|<harness>\n[warn] Output truncated to its end: 2 lines, 4 bytes dropped\n</harness>"
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn turns_a_throw_into_a_tool_error_result_with_the_partial_output() {
    let setup = setup();
    add_tool(
        &setup.registry,
        tool("fail", |_, api, _| async move {
            api.output(ToolOutputChunk::Text("partial\n"), None)?;
            Err(SessionError::error("boom"))
        }),
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[("fail", serde_json::json!({}), "c1")]).into(),
            done().into(),
        ],
    )
    .await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    let [result] = results(&ran.entries).try_into().unwrap();
    assert!(result.is_error);
    assert_eq!(
        result_text(&result),
        "partial\n|<harness>\n[error] boom\n</harness>"
    );
    ran.harness.close(context()).await.unwrap();
}

/// A tool `echo` recording its arguments.
fn recording_echo(seen: &Arc<Mutex<Vec<PiJsonValue>>>) -> Arc<ToolRegistration> {
    let seen = Arc::clone(seen);
    tool("echo", move |args, _, _| {
        seen.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(args);
        async { Ok(empty_content()) }
    })
}

#[tokio::test(flavor = "multi_thread")]
async fn validates_arguments_before_and_after_before_tool_and_applies_blocks_and_replacements() {
    let setup = setup();
    let seen: Arc<Mutex<Vec<PiJsonValue>>> = Arc::default();
    add_tool(&setup.registry, recording_echo(&seen), None).unwrap();
    add_hooks(
        &setup.registry,
        tool_task(),
        ToolHooks {
            before_tool: Some(Arc::new(|call, _, _| {
                let decision = match call.id.as_str() {
                    "block" => Ok(Some(BeforeToolDecision {
                        block: Some("not today".to_owned()),
                        ..BeforeToolDecision::default()
                    })),
                    "throw" => Err(SessionError::error("hook failed")),
                    "bad" => Ok(Some(BeforeToolDecision {
                        arguments: Some(
                            serde_json::json!({ "text": { "not": "a string" } })
                                .as_object()
                                .unwrap()
                                .clone(),
                        ),
                        ..BeforeToolDecision::default()
                    })),
                    _ => {
                        let text = call.arguments["text"].as_str().unwrap_or("undefined");
                        Ok(Some(BeforeToolDecision {
                            arguments: Some(
                                serde_json::json!({ "text": format!("{text}!") })
                                    .as_object()
                                    .unwrap()
                                    .clone(),
                            ),
                            ..BeforeToolDecision::default()
                        }))
                    }
                };
                futures::future::ready(decision).boxed()
            })),
            ..ToolHooks::default()
        },
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[
                ("echo", serde_json::json!({ "text": 1 }), "coerced"),
                (
                    "echo",
                    serde_json::json!({ "text": { "not": "a string" } }),
                    "invalid",
                ),
                ("echo", serde_json::json!({}), "block"),
                ("echo", serde_json::json!({}), "throw"),
                ("echo", serde_json::json!({ "text": "x" }), "bad"),
                ("echo", serde_json::json!({ "text": "x" }), "ok"),
            ])
            .into(),
            done().into(),
        ],
    )
    .await;
    // Parallel tools append their results in completion order.
    let by_id: BTreeMap<String, (bool, String)> = results(&ran.entries)
        .iter()
        .map(|result| {
            (
                result.tool_call_id.clone(),
                (result.is_error, result_text(result)),
            )
        })
        .collect();
    assert_eq!(
        by_id["block"],
        (true, harness_error("Tool call blocked: not today"))
    );
    assert_eq!(
        by_id["throw"],
        (true, harness_error("Tool call blocked: hook failed"))
    );
    assert!(by_id["bad"].0);
    assert!(by_id["bad"].1.contains("Validation failed"));
    assert_eq!(by_id["ok"], (false, String::new()));
    assert!(by_id["invalid"].0);
    assert!(by_id["invalid"].1.contains("Validation failed"));
    // pi-ai coerces a number to a string before the first validation.
    assert_eq!(by_id["coerced"], (false, String::new()));
    let mut seen = locked(&seen);
    seen.sort_by_key(ToString::to_string);
    assert_eq!(
        seen,
        [
            serde_json::json!({ "text": "1!" }),
            serde_json::json!({ "text": "x!" })
        ]
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn repairs_arguments_with_prepare_arguments_before_validation_and_a_throwing_repair_is_invalid(
) {
    let setup = setup();
    let seen: Arc<Mutex<Vec<PiJsonValue>>> = Arc::default();
    let recorded = Arc::clone(&seen);
    add_tool(
        &setup.registry,
        tool_with(
            "echo",
            move |args, _, _| {
                recorded
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(args);
                async { Ok(empty_content()) }
            },
            |tool| {
                tool.prepare_arguments = Some(Arc::new(|args| {
                    let text = &args["text"];
                    if text == "throw" {
                        return Err(SessionError::error("cannot repair"));
                    }
                    Ok(match text.as_f64() {
                        Some(number) => serde_json::json!({ "text": format!("#{number}") }),
                        None => args,
                    })
                }));
            },
        ),
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[
                ("echo", serde_json::json!({ "text": 7 }), "fixed"),
                ("echo", serde_json::json!({ "text": "throw" }), "broken"),
            ])
            .into(),
            done().into(),
        ],
    )
    .await;
    let by_id: BTreeMap<String, String> = results(&ran.entries)
        .iter()
        .map(|result| (result.tool_call_id.clone(), result_text(result)))
        .collect();
    assert_eq!(by_id["fixed"], "");
    assert_eq!(by_id["broken"], harness_error("cannot repair"));
    assert_eq!(locked(&seen), [serde_json::json!({ "text": "#7" })]);
    // The stored call keeps what the model sent.
    let Some([Message::Assistant(assistant)]) = ran.entries[2].model.as_deref() else {
        panic!("assistant entry without an assistant message");
    };
    let call = assistant.content.iter().find_map(|item| match item {
        AssistantContentBlock::ToolCall(call) => Some(call),
        AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
    });
    assert_eq!(
        call.map(|call| serde_json::Value::Object(call.arguments.clone())),
        Some(serde_json::json!({ "text": 7 }))
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn lets_the_first_before_tool_block_win_and_skips_later_handlers() {
    let setup = setup();
    add_tool(
        &setup.registry,
        tool("echo", |_, _, _| async { Ok(empty_content()) }),
        None,
    )
    .unwrap();
    let asked: Arc<Mutex<Vec<&'static str>>> = Arc::default();
    for name in ["first", "second"] {
        let asked = Arc::clone(&asked);
        add_hooks(
            &setup.registry,
            tool_task(),
            ToolHooks {
                before_tool: Some(Arc::new(move |_, _, _| {
                    asked
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(name);
                    futures::future::ready(Ok(Some(BeforeToolDecision {
                        block: Some(format!("{name} says no")),
                        ..BeforeToolDecision::default()
                    })))
                    .boxed()
                })),
                ..ToolHooks::default()
            },
            None,
        )
        .unwrap();
    }
    let ran = run(
        &setup,
        vec![
            calls(&[("echo", serde_json::json!({}), "c1")]).into(),
            done().into(),
        ],
    )
    .await;
    assert_eq!(locked(&asked), ["first"]);
    assert_eq!(
        result_text(&results(&ran.entries)[0]),
        harness_error("Tool call blocked: first says no")
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn chains_after_tool_replacements_and_observes_the_round_with_after_tools() {
    let setup = setup();
    add_tool(
        &setup.registry,
        tool("echo", |_, _, _| async {
            Ok(ToolExecutionResult {
                content: Some(vec![text("raw")]),
                ..ToolExecutionResult::default()
            })
        }),
        None,
    )
    .unwrap();
    add_hooks(
        &setup.registry,
        tool_task(),
        ToolHooks {
            after_tool: Some(Arc::new(|_, result, _, _| {
                let replaced = ToolExecutionResult {
                    content: Some(vec![text("first")]),
                    ..result.clone()
                };
                futures::future::ready(Ok(Some(replaced))).boxed()
            })),
            ..ToolHooks::default()
        },
        None,
    )
    .unwrap();
    add_hooks(
        &setup.registry,
        tool_task(),
        ToolHooks {
            after_tool: Some(Arc::new(|_, result, _, _| {
                let replaced = content_text(result.content.as_deref().unwrap_or_default());
                let details = json(&serde_json::json!({ "replaced": replaced }).to_string());
                let replaced = ToolExecutionResult {
                    details: Some(details),
                    ..result.clone()
                };
                futures::future::ready(Ok(Some(replaced))).boxed()
            })),
            ..ToolHooks::default()
        },
        None,
    )
    .unwrap();
    let observed: Arc<Mutex<Vec<Observed>>> = Arc::default();
    let observing = Arc::clone(&observed);
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            after_tools: Some(Arc::new(move |assistant, entries, _, _| {
                observing
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push((assistant, entries.to_vec()));
                futures::future::ready(Ok(())).boxed()
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[("echo", serde_json::json!({}), "c1")]).into(),
            done().into(),
        ],
    )
    .await;
    let [result] = results(&ran.entries).try_into().unwrap();
    assert_eq!(result_text(&result), "first");
    assert_eq!(
        result.details,
        Some(serde_json::json!({ "replaced": "first" }))
    );
    let result_entry = ran
        .entries
        .iter()
        .find(|entry| TOOL_RESULT_ENTRY.is(Some(entry)))
        .unwrap();
    assert_eq!(
        locked(&observed),
        [(ran.entries[2].id, vec![result_entry.id])]
    );
    ran.harness.close(context()).await.unwrap();
}

/// What `after_tools` observed: the assistant entry and the result entries.
type Observed = (EntryId, Vec<EntryId>);

/// A conversation owned by a live task of `root_id` whose definition no
/// registry holds, so it stays pending.
async fn task_owned_child(harness: &Harness, root_id: ConversationId) -> Conversation {
    // An owner task no registered definition takes stays live and pending.
    let owner = define_task(
        TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
            "test.owner",
            1,
            |_| Ok(json(r#"{"phase":"never"}"#)),
            |_, _, _| async { Ok(()) },
        )
        .phase("never", |_, _, _| async { Ok(()) }),
    );
    let child_id = harness
        .commit(
            move |tx| async move {
                let task_id = tx
                    .create_task(
                        owner.erase().as_definition_ref(),
                        JsonValue::object(),
                        TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: Some(root_id),
                            background: None,
                        },
                    )
                    .await?;
                Ok(tx
                    .create_conversation(ConversationOwnership::Task { task_id })
                    .await?
                    .id)
            },
            context(),
        )
        .await
        .unwrap();
    harness
        .conversation(child_id, context())
        .await
        .unwrap()
        .unwrap()
}

#[tokio::test(flavor = "multi_thread")]
async fn runs_the_hooks_of_the_selected_extensions_a_task_owned_child_copies_its_owners_selection()
{
    let setup = setup();
    let called_in = Arc::new(Mutex::new(Vec::new()));
    let echo = define_extension(Extension {
        tools: vec![tool("echo", |_, _, _| async { Ok(empty_content()) })],
        ..Extension::named("echo")
    });
    let calling = Arc::clone(&called_in);
    let audit = define_extension(Extension {
        hooks: vec![hook(
            tool_task(),
            ToolHooks {
                before_tool: Some(Arc::new(move |_, api, _| {
                    calling
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(api.conversation_id());
                    futures::future::ready(Ok(None)).boxed()
                })),
                ..ToolHooks::default()
            },
        )],
        ..Extension::named("audit")
    });
    setup.registry.install(Arc::clone(&echo)).unwrap();
    setup.registry.install(Arc::clone(&audit)).unwrap();
    // Audit is installed but not in the default selection.
    setup
        .settings
        .update(|settings| settings.extensions = Some(vec![Arc::clone(&echo)]));
    let first = run(&setup, vec![done().into()]).await;
    first
        .root
        .configure(
            AgentChange {
                extensions: FieldChange::Set(ExtensionsChange::Edit {
                    add: Some(vec![audit]),
                    remove: None,
                }),
                ..AgentChange::default()
            },
            context(),
        )
        .await
        .unwrap();
    let child = task_owned_child(&first.harness, first.root.id()).await;
    let other = first
        .harness
        .create_conversation(
            ConversationCreateOptions {
                agent: Some(AgentChange {
                    model: FieldChange::Set(ModelRef {
                        provider: "faux".to_owned(),
                        model_id: "faux-1".to_owned(),
                    }),
                    ..AgentChange::default()
                }),
                ..ConversationCreateOptions::new(ConversationOwnership::Ownerless)
            },
            context(),
        )
        .await
        .unwrap();
    for conversation in [&first.root, &child, &other] {
        setup.faux.set_responses(vec![
            calls(&[("echo", serde_json::json!({}), "c1")]).into(),
            done().into(),
        ]);
        submit_and_wait(conversation, "go").await;
    }
    assert_eq!(locked(&called_in), [first.root.id(), child.id()]);
    first.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn applies_add_tools_and_terminates_only_when_every_result_of_the_round_asks_to() {
    let setup = setup();
    let stop = tool("stop", |_, _, _| async {
        Ok(ToolExecutionResult {
            control: Some(ToolControl {
                terminate: true,
                ..ToolControl::default()
            }),
            ..empty_content()
        })
    });
    let grow = tool("grow", |_, _, _| async {
        Ok(ToolExecutionResult {
            control: Some(ToolControl {
                add_tools: Some(vec!["extra".to_owned(), "stop".to_owned()]),
                ..ToolControl::default()
            }),
            ..empty_content()
        })
    });
    add_tool(&setup.registry, Arc::clone(&stop), None).unwrap();
    add_tool(&setup.registry, Arc::clone(&grow), None).unwrap();
    add_tool(
        &setup.registry,
        tool("extra", |_, _, _| async { Ok(empty_content()) }),
        None,
    )
    .unwrap();
    let offered = vec![stop, grow];
    let first = run_with(
        &setup,
        vec![calls(&[("stop", serde_json::json!({}), "c1")]).into()],
        Some(Box::new(move |_, root| {
            async move {
                root.configure(
                    AgentChange {
                        tools: FieldChange::Set(ToolsChange::Exactly(offered)),
                        ..AgentChange::default()
                    },
                    context(),
                )
                .await
                .unwrap();
            }
            .boxed()
        })),
        None,
    )
    .await;
    assert_eq!(first.status, SubmissionStatus::Done);
    assert_eq!(first.entries.last().unwrap().kind, "pi.tool-result");
    let root_id = first.root.id();
    let settled = first
        .harness
        .commit(
            move |tx| async move {
                tx.scan_tasks(
                    TaskQuery {
                        conversation_id: Some(root_id),
                        ..TaskQuery::default()
                    },
                    20,
                    None,
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    assert!(settled
        .items
        .iter()
        .all(|task| task.state.status() == TaskStatus::Terminal));

    setup.faux.set_responses(vec![
        calls(&[
            ("stop", serde_json::json!({}), "c1"),
            ("grow", serde_json::json!({}), "c2"),
        ])
        .into(),
        done().into(),
    ]);
    assert_eq!(
        submit_and_wait(&first.root, "again").await,
        SubmissionStatus::Done
    );
    let entries = all_entries(&first.root, context()).await.unwrap();
    assert_eq!(entries.last().unwrap().kind, "pi.assistant");
    // addTools appends to the stored tool array, skipping names it already holds.
    let agent = first
        .harness
        .snapshot(&AGENT_DOC, first.root.id(), context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        agent.get("tools"),
        Some(&json(r#"["stop","grow","extra"]"#))
    );
    first.harness.close(context()).await.unwrap();
}
