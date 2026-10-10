//! Port of `test/harness-tools.test.ts` `describe("tool round")`.

use std::sync::{Arc, Mutex, OnceLock, PoisonError};
use std::time::Duration;

use eukhe_chord::json::JsonValue;
use eukhe_pi_ai::providers::faux::{FauxResponseStep, RegisterFauxProviderOptions};
use eukhe_types::pi_ai::{
    Message, TextContent, ToolReference, ToolResultMessage, UserContentBlock,
};
use futures::FutureExt;

use super::support::{
    calls, done, empty_content, result_text, results, run, run_with, submit_and_wait, tool,
    tool_with,
};
use crate::entries::TOOL_RESULT_ENTRY;
use crate::harness::live::LIVE_DOC;
use crate::harness::tests::chat_support::{all_entries, chat_setup, ChatSetup};
use crate::harness::tests::support::{add_tool, context, Installed};
use crate::harness::types::{
    AgentChange, FieldChange, ToolExecutionMode, ToolExecutionResult, ToolsChange,
};
use crate::harness::Conversation;
use crate::types::{EntryRecord, SubmissionStatus, TaskQuery};

type Events = Arc<Mutex<Vec<String>>>;

fn push(events: &Events, event: impl Into<String>) {
    events
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .push(event.into());
}

fn taken(events: &Events) -> Vec<String> {
    events
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

fn setup() -> ChatSetup {
    chat_setup(RegisterFauxProviderOptions::default())
}

fn kinds(entries: &[EntryRecord]) -> Vec<&str> {
    entries.iter().map(|entry| entry.kind.as_str()).collect()
}

fn last_system(entries: &[EntryRecord]) -> eukhe_types::pi_ai::SystemMessage {
    match entries
        .iter()
        .rev()
        .find(|entry| entry.kind == "pi.system")
        .and_then(|entry| entry.model.as_deref())
    {
        Some([Message::System(system)]) => system.clone(),
        other => panic!("no system message: {other:?}"),
    }
}

fn harness_error(message: &str) -> String {
    format!("<harness>\n[error] {message}\n</harness>")
}

#[tokio::test(flavor = "multi_thread")]
async fn runs_input_tool_call_tool_result_and_answer_and_settles_the_input() {
    let setup = setup();
    let echo = tool("echo", |args, _, _| async move {
        let text = args["text"].as_str().unwrap_or("undefined").to_owned();
        Ok(ToolExecutionResult {
            output: Some(vec![UserContentBlock::Text(TextContent::new(format!(
                "echo {text}"
            )))]),
            ..ToolExecutionResult::default()
        })
    });
    add_tool(&setup.registry, Arc::clone(&echo), None).unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[("echo", serde_json::json!({ "text": "hi" }), "c1")]).into(),
            done().into(),
        ],
    )
    .await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    let entries = &ran.entries;
    assert_eq!(
        kinds(entries),
        [
            "pi.user",
            "pi.system",
            "pi.assistant",
            "pi.tool-result",
            "pi.assistant"
        ]
    );
    let Some([Message::System(system)]) = entries[1].model.as_deref() else {
        panic!("system entry without a system message");
    };
    // TS `parameters: expect.any(Object)`: the stored schema is the plain JSON Schema.
    let added: Vec<(&str, &str, &serde_json::Value)> = system
        .tools_added
        .iter()
        .flatten()
        .map(|declared| {
            (
                declared.name.as_str(),
                declared.description.as_str(),
                declared.parameters.json(),
            )
        })
        .collect();
    assert_eq!(added, [("echo", "The echo tool", echo.parameters.json())]);
    let [result] = results(entries).try_into().unwrap();
    assert_eq!(
        result,
        ToolResultMessage {
            tool_call_id: "c1".to_owned(),
            tool_name: "echo".to_owned(),
            content: vec![UserContentBlock::Text(TextContent::new("echo hi"))],
            details: None,
            usage: None,
            nested_calls: None,
            is_error: false,
            timestamp: result.timestamp,
            // TS `toMatchObject`: the measured execution time is any value.
            duration_ms: result.duration_ms,
        }
    );
    assert_eq!(result_text(&result), "echo hi");
    assert!(TOOL_RESULT_ENTRY.is(Some(&entries[3])));
    assert_eq!(
        entries[3].data,
        Some(JsonValue::parse(r#"{"diagnostics":[]}"#).unwrap())
    );
    assert!(entries[3].by_task_id.is_some());
    // The second request sees the tool result right after its call.
    assert_eq!(setup.faux.state().call_count, 2);
    let live = ran
        .harness
        .snapshot(&LIVE_DOC, ran.root.id(), context())
        .await
        .unwrap();
    assert_eq!(live.map(JsonValue::Object), Some(JsonValue::object()));
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn answers_calls_to_tools_the_request_did_not_offer_without_a_task() {
    let setup = setup();
    add_tool(
        &setup.registry,
        tool("echo", |_, _, _| async { Ok(empty_content()) }),
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[
                ("ghost", serde_json::json!({}), "c1"),
                ("echo", serde_json::json!({}), "c2"),
            ])
            .into(),
            done().into(),
        ],
    )
    .await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    let [ghost, echo] = results(&ran.entries).try_into().unwrap();
    assert_eq!((ghost.tool_call_id.as_str(), ghost.is_error), ("c1", true));
    assert_eq!(
        result_text(&ghost),
        harness_error("Tool ghost is not available")
    );
    assert_eq!((echo.tool_call_id.as_str(), echo.is_error), ("c2", false));
    let ghost_entry = ran
        .entries
        .iter()
        .find(|entry| TOOL_RESULT_ENTRY.is(Some(entry)))
        .unwrap();
    assert_eq!(
        ghost_entry.data,
        Some(
            JsonValue::parse(
                r#"{"diagnostics":[{"severity":"error","code":"tool_unavailable","message":"Tool ghost is not available"}]}"#
            )
            .unwrap()
        )
    );
    let root_id = ran.root.id();
    let tasks = ran
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
    assert_eq!(
        tasks
            .items
            .iter()
            .filter(|task| task.kind == "pi.tool")
            .count(),
        1
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn answers_a_call_to_a_tool_deactivated_after_preparation_with_tool_unavailable() {
    let setup = setup();
    let seen: Events = Arc::default();
    let ran_events = Arc::clone(&seen);
    add_tool(
        &setup.registry,
        tool("echo", move |_, _, _| {
            push(&ran_events, "ran");
            async { Ok(empty_content()) }
        }),
        None,
    )
    .unwrap();
    let root: Arc<OnceLock<Conversation>> = Arc::default();
    let deactivating = Arc::clone(&root);
    let deactivate = FauxResponseStep::Factory(Arc::new(move |_, _, _, _| {
        let root = deactivating.get().unwrap().clone();
        async move {
            root.configure(
                AgentChange {
                    tools: FieldChange::Set(ToolsChange::Exactly(Vec::new())),
                    ..AgentChange::default()
                },
                context(),
            )
            .await
            .unwrap();
            Ok(calls(&[("echo", serde_json::json!({}), "c1")]))
        }
        .boxed()
    }));
    let prepared = Arc::clone(&root);
    let result = run_with(
        &setup,
        vec![deactivate, done().into()],
        Some(Box::new(move |_, conversation| {
            prepared.set(conversation).ok().unwrap();
            async {}.boxed()
        })),
        None,
    )
    .await;
    assert_eq!(taken(&seen), Vec::<String>::new());
    assert_eq!(
        result_text(&results(&result.entries)[0]),
        harness_error("Tool echo is not available")
    );
    // The next preparation removes it.
    assert_eq!(
        last_system(&result.entries).tools_removed,
        Some(vec![ToolReference {
            name: "echo".to_owned()
        }])
    );
    result.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn removes_unregistered_active_tools_from_the_offer_and_adds_them_back_after_re_registration()
{
    let setup = setup();
    let echo = tool("echo", |_, _, _| async { Ok(empty_content()) });
    let registration = add_tool(&setup.registry, Arc::clone(&echo), None).unwrap();
    let first = run(&setup, vec![done().into()]).await;
    registration.dispose();
    setup.faux.set_responses(vec![
        calls(&[("echo", serde_json::json!({}), "c1")]).into(),
        done().into(),
    ]);
    assert_eq!(
        submit_and_wait(&first.root, "again").await,
        SubmissionStatus::Done
    );
    let entries = all_entries(&first.root, context()).await.unwrap();
    assert_eq!(
        last_system(&entries).tools_removed,
        Some(vec![ToolReference {
            name: "echo".to_owned()
        }])
    );
    assert!(results(&entries)[0].is_error);
    // The stored agent is not rewritten; the tool is only not resolved.
    assert!(first.root.agent(context()).await.unwrap().tools.is_empty());

    add_tool(&setup.registry, echo, None).unwrap();
    setup.faux.set_responses(vec![done().into()]);
    submit_and_wait(&first.root, "back").await;
    let entries = all_entries(&first.root, context()).await.unwrap();
    let added: Option<Vec<String>> = last_system(&entries)
        .tools_added
        .map(|tools| tools.into_iter().map(|declared| declared.name).collect());
    assert_eq!(added, Some(vec!["echo".to_owned()]));
    first.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn produces_tool_unavailable_when_the_implementation_is_unregistered_before_its_task_runs() {
    let setup = setup();
    let second: Arc<OnceLock<Installed>> = Arc::default();
    let disposing = Arc::clone(&second);
    add_tool(
        &setup.registry,
        tool_with(
            "first",
            move |_, _, _| {
                disposing.get().unwrap().dispose();
                async { Ok(empty_content()) }
            },
            |tool| tool.execution_mode = Some(ToolExecutionMode::Sequential),
        ),
        None,
    )
    .unwrap();
    let installed = add_tool(
        &setup.registry,
        tool("second", |_, _, _| async {
            Ok(ToolExecutionResult {
                output: Some(vec![UserContentBlock::Text(TextContent::new("ran"))]),
                ..ToolExecutionResult::default()
            })
        }),
        None,
    )
    .unwrap();
    second.set(installed).ok().unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[
                ("first", serde_json::json!({}), "c1"),
                ("second", serde_json::json!({}), "c2"),
            ])
            .into(),
            done().into(),
        ],
    )
    .await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    let [_, late] = results(&ran.entries).try_into().unwrap();
    assert_eq!(
        result_text(&late),
        harness_error("Tool second is not available")
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn reads_the_execution_mode_when_a_round_starts_and_keeps_it_for_the_round() {
    let setup = setup();
    let events: Events = Arc::default();
    for name in ["a", "b"] {
        let (events, settings) = (Arc::clone(&events), Arc::clone(&setup.settings));
        add_tool(
            &setup.registry,
            tool(name, move |_, _, _| {
                let (events, settings) = (Arc::clone(&events), Arc::clone(&settings));
                async move {
                    push(&events, format!("start {name}"));
                    // Changed after the round started: not seen by this round.
                    settings.update(|settings| {
                        settings.tool_execution = Some(ToolExecutionMode::Parallel);
                    });
                    tokio::time::sleep(Duration::from_millis(20)).await;
                    push(&events, format!("end {name}"));
                    Ok(empty_content())
                }
            }),
            None,
        )
        .unwrap();
    }
    // Changed while the model request runs: the round that follows uses it.
    let settings = Arc::clone(&setup.settings);
    let request = FauxResponseStep::factory(move |_, _, _, _| {
        settings.update(|settings| settings.tool_execution = Some(ToolExecutionMode::Sequential));
        Ok(calls(&[
            ("a", serde_json::json!({}), "c1"),
            ("b", serde_json::json!({}), "c2"),
        ]))
    });
    let ran = run(&setup, vec![request, done().into()]).await;
    assert_eq!(taken(&events), ["start a", "end a", "start b", "end b"]);
    ran.harness.close(context()).await.unwrap();
}

/// The events of a round calling `a` then `b`, each sleeping 20 ms.
async fn trace(setup: &ChatSetup) -> Vec<String> {
    let events: Events = Arc::default();
    for name in ["a", "b"] {
        let events = Arc::clone(&events);
        add_tool(
            &setup.registry,
            tool(name, move |_, _, _| {
                let events = Arc::clone(&events);
                async move {
                    push(&events, format!("start {name}"));
                    tokio::time::sleep(Duration::from_millis(20)).await;
                    push(&events, format!("end {name}"));
                    Ok(empty_content())
                }
            }),
            None,
        )
        .unwrap();
    }
    let ran = run(
        setup,
        vec![
            calls(&[
                ("a", serde_json::json!({}), "c1"),
                ("b", serde_json::json!({}), "c2"),
            ])
            .into(),
            done().into(),
        ],
    )
    .await;
    ran.harness.close(context()).await.unwrap();
    taken(&events)
}

#[tokio::test(flavor = "multi_thread")]
async fn runs_a_round_in_parallel_by_default_and_sequentially_when_configured_or_required_by_a_tool(
) {
    // Both start before either ends; on a multi-thread runtime the two
    // parallel tool tasks may start in either order (JS runs them in creation order).
    let mut started = trace(&setup()).await[..2].to_vec();
    started.sort();
    assert_eq!(started, ["start a", "start b"]);
    let configured = setup();
    configured
        .settings
        .update(|settings| settings.tool_execution = Some(ToolExecutionMode::Sequential));
    assert_eq!(
        trace(&configured).await,
        ["start a", "end a", "start b", "end b"]
    );

    let per_tool = setup();
    let events: Events = Arc::default();
    let a_events = Arc::clone(&events);
    add_tool(
        &per_tool.registry,
        tool_with(
            "a",
            move |_, _, _| {
                let events = Arc::clone(&a_events);
                async move {
                    tokio::time::sleep(Duration::from_millis(20)).await;
                    push(&events, "a");
                    Ok(empty_content())
                }
            },
            |tool| tool.execution_mode = Some(ToolExecutionMode::Sequential),
        ),
        None,
    )
    .unwrap();
    let b_events = Arc::clone(&events);
    add_tool(
        &per_tool.registry,
        tool("b", move |_, _, _| {
            push(&b_events, "b");
            async { Ok(empty_content()) }
        }),
        None,
    )
    .unwrap();
    let ran = run(
        &per_tool,
        vec![
            calls(&[
                ("a", serde_json::json!({}), "c1"),
                ("b", serde_json::json!({}), "c2"),
            ])
            .into(),
            done().into(),
        ],
    )
    .await;
    let root_id = ran.root.id();
    let tasks = ran
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
    let mut tools: Vec<_> = tasks
        .items
        .iter()
        .filter(|task| task.kind == "pi.tool")
        .collect();
    tools.sort_by_key(|task| task.id.get());
    // The generation owns both tools and creates the second only after the first ended.
    let generation = tasks
        .items
        .iter()
        .find(|task| task.kind == "pi.generation")
        .unwrap();
    assert_eq!(
        tools.iter().map(|task| task.owner).collect::<Vec<_>>(),
        [Some(generation.id), Some(generation.id)]
    );
    assert_eq!(taken(&events), ["a", "b"]);
    ran.harness.close(context()).await.unwrap();
}
