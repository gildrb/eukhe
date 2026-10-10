//! Port of `test/harness-tools.test.ts` `describe("tool progress and
//! lifetime")`.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::json::{from_json, JsonValue};
use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;
use eukhe_types::pi_ai::{IndexMap, Message, TextContent, UserContentBlock};
use futures::FutureExt;
use tokio::task::JoinHandle;

use super::support::{
    calls, done, empty_content, result_text, results, run, run_with, tool, Prepare,
};
use crate::harness::agent::AGENT_DOC;
use crate::harness::define::{define_extension, hook, section};
use crate::harness::live::LIVE_DOC;
use crate::harness::tests::chat_support::{all_entries, chat_setup, open_chat, OpenChat};
use crate::harness::tests::support::{add_hooks, add_tool, context, generation_task, tool_task};
use crate::harness::tests::task_support::{aborted, deferred, Deferred};
use crate::harness::types::{
    AgentChange, Extension, FieldChange, GenerationHooks, InputSubmissionDraft,
    InvocationTaskOptions, ToolControl, ToolExecutionApiExt, ToolExecutionResult, ToolHooks,
    ToolOutputChunk, ToolsChange,
};
use crate::session::{SessionError, SessionResult, WatchEnd};
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, TaskDefinition};
use crate::types::{
    DocumentObserverExt, DocumentReaderExt, SubmissionStatus, TaskId, TaskOwnership,
};

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

fn text(text: &str) -> ToolExecutionResult {
    ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
        ..ToolExecutionResult::default()
    }
}

fn one_call(name: &str) -> Vec<eukhe_pi_ai::providers::faux::FauxResponseStep> {
    vec![
        calls(&[(name, serde_json::json!({}), "c1")]).into(),
        done().into(),
    ]
}

fn input() -> InputSubmissionDraft {
    InputSubmissionDraft::new("go")
}

/// The task of the first tool slot of `pi.live`.
async fn first_tool_task(
    harness: &crate::harness::Harness,
    root: &crate::harness::Conversation,
) -> TaskId {
    let live = harness
        .snapshot(&LIVE_DOC, root.id(), context())
        .await
        .unwrap()
        .unwrap();
    from_json(&live.get("tools").unwrap()[0]["taskId"]).unwrap()
}

#[tokio::test]
async fn applies_the_default_output_limits() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(
        &setup.registry,
        tool("lines", |_, api, _| async move {
            for index in 1..=2500 {
                api.output(ToolOutputChunk::Text(&format!("{index}\n")), None)?;
            }
            Ok(ToolExecutionResult::default())
        }),
        None,
    )
    .unwrap();
    let ran = run(&setup, one_call("lines")).await;
    let text = result_text(&results(&ran.entries)[0]);
    assert!(text.starts_with("1\n2\n"), "{text}");
    assert!(
        text.ends_with("\n2000\n|<harness>\n[warn] Output truncated to its beginning: 500 lines, 2500 bytes dropped\n</harness>"),
        "{text}"
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn sanitizes_running_output_but_keeps_explicit_result_content_as_the_tool_returned_it() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let slot_output: Arc<Mutex<Option<String>>> = Arc::default();
    let sink = Arc::clone(&slot_output);
    add_tool(
        &setup.registry,
        tool("noisy", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                api.output(ToolOutputChunk::Text("a\u{7}b\r\n"), None)?;
                api.details(json(r#"{"ready":true}"#), &cx).await?;
                let live = api.snapshot(&LIVE_DOC, api.conversation_id(), &cx).await?;
                *lock(&sink) = live
                    .and_then(|live| live.get("tools").map(|tools| tools[0]["output"].clone()))
                    .and_then(|output| output.as_str().map(str::to_owned));
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    add_tool(
        &setup.registry,
        tool("explicit", |_, _, _| async { Ok(text("c\u{1b}d")) }),
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[
                ("noisy", serde_json::json!({}), "c1"),
                ("explicit", serde_json::json!({}), "c2"),
            ])
            .into(),
            done().into(),
        ],
    )
    .await;
    assert_eq!(lock(&slot_output).as_deref(), Some("ab\n"));
    let by_id: HashMap<String, String> = results(&ran.entries)
        .iter()
        .map(|result| (result.tool_call_id.clone(), result_text(result)))
        .collect();
    assert_eq!(by_id["c1"], "ab\n");
    assert_eq!(by_id["c2"], "c\u{1b}d");
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn drops_control_keys_set_to_undefined_instead_of_faulting() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(
        &setup.registry,
        tool("grow", |_, _, _| async {
            Ok(ToolExecutionResult {
                // TS `terminate: undefined`: Rust has no undefined key, only the absent default.
                control: Some(ToolControl {
                    add_tools: Some(vec!["extra".to_owned()]),
                    ..ToolControl::default()
                }),
                ..empty_content()
            })
        }),
        None,
    )
    .unwrap();
    let extra = tool("extra", |_, _, _| async { Ok(empty_content()) });
    add_tool(&setup.registry, Arc::clone(&extra), None).unwrap();
    let prepare: Prepare = Box::new(move |_, conversation| {
        async move {
            conversation
                .configure(
                    AgentChange {
                        tools: FieldChange::Set(ToolsChange::Remove(vec![extra])),
                        ..AgentChange::default()
                    },
                    context(),
                )
                .await
                .unwrap();
        }
        .boxed()
    });
    let ran = run_with(&setup, one_call("grow"), Some(prepare), None).await;
    assert_eq!(ran.status, SubmissionStatus::Done);
    // addTools deletes the name from a stored `{ remove }` filter.
    let agent = ran
        .harness
        .snapshot(&AGENT_DOC, ran.root.id(), context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(agent.get("tools"), Some(&json(r#"{"remove":[]}"#)));
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn uses_explicit_null_details_instead_of_the_last_reported_value() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(
        &setup.registry,
        tool("null", |_, api, cx| async move {
            api.details(json(r#"{"old":1}"#), &cx).await?;
            Ok(ToolExecutionResult {
                details: Some(JsonValue::Null),
                ..empty_content()
            })
        }),
        None,
    )
    .unwrap();
    let ran = run(&setup, one_call("null")).await;
    assert_eq!(
        results(&ran.entries)[0].details,
        Some(serde_json::Value::Null)
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn settles_details_promises_with_coalesced_progress_commits_and_the_terminal_commit() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let settled: Arc<Mutex<Vec<&'static str>>> = Arc::default();
    let sink = Arc::clone(&settled);
    add_tool(
        &setup.registry,
        tool("details", move |_, api, cx| {
            let sink = Arc::clone(&sink);
            async move {
                // Three updates in one throttle window coalesce; the last is still pending when execute() returns.
                // One observer awaits them in call order, like the promise reactions TS chains.
                let first = api.details(json(r#"{"n":1}"#), &cx);
                let second = api.details(json(r#"{"n":2}"#), &cx);
                let (first_done, first_settled) = tokio::sync::oneshot::channel::<()>();
                let (third_sender, third) = tokio::sync::oneshot::channel::<
                    futures::future::BoxFuture<'static, SessionResult<()>>,
                >();
                let observer = Arc::clone(&sink);
                drop(tokio::spawn(async move {
                    if first.await.is_ok() {
                        lock(&observer).push("first");
                    }
                    let _ = first_done.send(());
                    if second.await.is_ok() {
                        lock(&observer).push("second");
                    }
                    if let Ok(third) = third.await {
                        if third.await.is_ok() {
                            lock(&observer).push("third");
                        }
                    }
                }));
                let _ = first_settled.await;
                let _ = third_sender.send(api.details(json(r#"{"n":3}"#), &cx));
                Ok(empty_content())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run(&setup, one_call("details")).await;
    crate::harness::tests::task_support::eventually(|| {
        let count = lock(&settled).len();
        async move { count == 3 }
    })
    .await;
    assert_eq!(*lock(&settled), ["first", "second", "third"]);
    assert_eq!(
        results(&ran.entries)[0].details,
        Some(serde_json::json!({ "n": 3 }))
    );
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn finishes_a_call_under_the_implementation_it_resolved_when_the_tool_is_replaced_mid_call() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let started: Deferred = deferred();
    let finished: Deferred = deferred();
    let (start, finish) = (started.clone(), finished.clone());
    let v1 = tool("work", move |_, _, _| {
        let (start, finish) = (start.clone(), finish.clone());
        async move {
            start.resolve(());
            finish.wait().await;
            Ok(text("v1"))
        }
    });
    add_tool(&setup.registry, v1, None).unwrap();
    setup.faux.set_responses(one_call("work"));
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let submission = root.submit(input(), context()).await.unwrap();
    started.wait().await;
    // The same extension name replaces the old one in place.
    add_tool(
        &setup.registry,
        tool("work", |_, _, _| async { Ok(text("v2")) }),
        None,
    )
    .unwrap();
    finished.resolve(());
    submission.wait(context()).await.unwrap();
    let entries = all_entries(&root, context()).await.unwrap();
    assert_eq!(result_text(&results(&entries)[0]), "v1");
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn uses_a_section_and_hook_extension_reloaded_mid_run_from_the_runs_next_request() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let requests: Arc<Mutex<Vec<&'static str>>> = Arc::default();
    let prompt = |version: &'static str| {
        let requests = Arc::clone(&requests);
        define_extension(Extension {
            sections: vec![section(
                "mode",
                move |_, _| futures::future::ready(Ok(Some(version.to_owned()))).boxed(),
                None,
            )],
            hooks: vec![hook(
                generation_task(),
                GenerationHooks {
                    before_request: Some(Arc::new(move |_, _, _| {
                        lock(&requests).push(version);
                        futures::future::ready(Ok(None)).boxed()
                    })),
                    ..GenerationHooks::default()
                },
            )],
            ..Extension::named("prompt")
        })
    };
    setup.registry.install(prompt("v1")).unwrap();
    let running: Deferred = deferred();
    let reloaded: Deferred = deferred();
    let (run_gate, reload_gate) = (running.clone(), reloaded.clone());
    add_tool(
        &setup.registry,
        tool("work", move |_, _, _| {
            let (run_gate, reload_gate) = (run_gate.clone(), reload_gate.clone());
            async move {
                run_gate.resolve(());
                reload_gate.wait().await;
                Ok(empty_content())
            }
        }),
        None,
    )
    .unwrap();
    setup.faux.set_responses(one_call("work"));
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let submission = root.submit(input(), context()).await.unwrap();
    running.wait().await;
    setup.registry.install(prompt("v2")).unwrap();
    reloaded.resolve(());
    submission.wait(context()).await.unwrap();
    let sections: Vec<IndexMap<String, Option<String>>> = all_entries(&root, context())
        .await
        .unwrap()
        .into_iter()
        .filter_map(|entry| match entry.model.as_deref() {
            Some([Message::System(message), ..]) => message.sections.clone(),
            _ => None,
        })
        .collect();
    let mode = |text: &str| -> IndexMap<String, Option<String>> {
        let mut sections = IndexMap::default();
        sections.insert("mode".to_owned(), Some(text.to_owned()));
        sections
    };
    assert_eq!(
        sections,
        [mode("<mode>\nv1\n</mode>"), mode("<mode>\nv2\n</mode>")]
    );
    assert_eq!(*lock(&requests), ["v1", "v2"]);
    harness.close(context()).await.unwrap();
}

type Pending<T> = Arc<Mutex<Option<JoinHandle<T>>>>;

#[tokio::test]
async fn rejects_invocation_bound_waits_and_stops_watches_when_the_tools_invocation_ends() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let never = define_task(
        TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
            "test.never",
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"never"}"#)),
            |_, _, _| async { Ok(()) },
        )
        .phase("never", |_, _, _| async { Ok(()) }),
    );
    let wait: Pending<SessionResult<crate::tasks::SettledTask>> = Arc::default();
    let watch_closed: Pending<WatchEnd> = Arc::default();
    let (wait_slot, closed_slot) = (Arc::clone(&wait), Arc::clone(&watch_closed));
    add_tool(
        &setup.registry,
        tool("detach", move |_, api, cx| {
            let (never, wait_slot, closed_slot) = (
                never.clone(),
                Arc::clone(&wait_slot),
                Arc::clone(&closed_slot),
            );
            async move {
                // The child's definition is not registered, so it stays pending.
                let options = InvocationTaskOptions {
                    ownership: TaskOwnership::Conversation,
                    background: None,
                    abandon_on_restart: None,
                };
                let child = api.create_task(&never, &json("{}"), options, &cx).await?;
                *lock(&wait_slot) = Some(tokio::spawn(api.wait_for_task(child, &cx)));
                let watch = api
                    .watch_doc(&LIVE_DOC, api.conversation_id(), &cx)
                    .await?
                    .expect("pi.live exists");
                *lock(&closed_slot) = Some(tokio::spawn(watch.closed()));
                Ok(empty_content())
            }
        }),
        None,
    )
    .unwrap();
    let ran = run(&setup, one_call("detach")).await;
    let wait = lock(&wait).take().expect("the tool waited");
    let error = wait.await.unwrap().expect_err("the wait rejects");
    assert!(
        error.to_string().contains("invocation has ended"),
        "{error}"
    );
    let closed = lock(&watch_closed).take().expect("the tool watched");
    closed.await.unwrap();
    ran.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn rejects_details_still_waiting_when_the_call_is_aborted_during_after_tool() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let pending_details: Pending<SessionResult<()>> = Arc::default();
    let in_after_tool: Deferred = deferred();
    let slot = Arc::clone(&pending_details);
    add_tool(
        &setup.registry,
        tool("slow", move |_, api, cx| {
            let slot = Arc::clone(&slot);
            async move {
                api.output(ToolOutputChunk::Text("first\n"), None)?;
                // The output commit is in flight, so these details wait for the next throttle window.
                *lock(&slot) = Some(tokio::spawn(api.details(json(r#"{"step":1}"#), &cx)));
                Ok(ToolExecutionResult::default())
            }
        }),
        None,
    )
    .unwrap();
    let reached = in_after_tool.clone();
    add_hooks(
        &setup.registry,
        tool_task(),
        ToolHooks {
            after_tool: Some(Arc::new(move |_, _, _, cx| {
                let (reached, signal) =
                    (reached.clone(), cx.abort_signal().expect("an abort signal"));
                async move {
                    reached.resolve(());
                    aborted(&signal).await;
                    Ok(None)
                }
                .boxed()
            })),
            ..ToolHooks::default()
        },
        None,
    )
    .unwrap();
    setup.faux.set_responses(one_call("slow"));
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let submission = root.submit(input(), context()).await.unwrap();
    in_after_tool.wait().await;
    let task = first_tool_task(&harness, &root).await;
    harness.abort_task(task, context()).await.unwrap();
    let pending = lock(&pending_details)
        .take()
        .expect("the tool reported details");
    assert!(pending.await.unwrap().is_err());
    submission.wait(context()).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn answers_an_aborted_tool_with_only_its_durable_output_discarding_buffered_output() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let buffered: Deferred = deferred();
    let reached = buffered.clone();
    add_tool(
        &setup.registry,
        tool("slow", move |_, api, cx| {
            let reached = reached.clone();
            async move {
                api.output(ToolOutputChunk::Text("durable\n"), None)?;
                // The first output commits at once; this one waits for the next throttle window.
                tokio::time::sleep(Duration::from_millis(20)).await;
                api.output(ToolOutputChunk::Text("buffered\n"), None)?;
                reached.resolve(());
                let signal = cx.abort_signal().expect("an abort signal");
                Err::<ToolExecutionResult, _>(SessionError::Aborted(signal.cancelled().await))
            }
        }),
        None,
    )
    .unwrap();
    setup.faux.set_responses(one_call("slow"));
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    let submission = root.submit(input(), context()).await.unwrap();
    buffered.wait().await;
    let task = first_tool_task(&harness, &root).await;
    harness.abort_task(task, context()).await.unwrap();
    submission.wait(context()).await.unwrap();
    let entries = all_entries(&root, context()).await.unwrap();
    assert_eq!(
        result_text(&results(&entries)[0]),
        "durable\n|<harness>\n[error] Tool slow was aborted\n</harness>"
    );
    harness.close(context()).await.unwrap();
}
