//! Port of `test/harness-tools-recovery.test.ts`.
//!
//! "lets context derivation answer a faulted tool": TS makes the result
//! commit throw with details holding a function, which is not strict JSON.
//! `JsonValue` cannot hold one, so the result here carries a usage counter
//! beyond `Number.MAX_SAFE_INTEGER`, which strict JSON conversion rejects in
//! the same result commit.

use std::future::Future;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{from_json, JsonValue};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{
    AssistantMessage, JsonObject as PiJsonObject, Message, StopReason, ToolResultMessage, Usage,
    UserContentBlock,
};
use futures::FutureExt;

use crate::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use crate::harness::define::define_tool;
use crate::harness::live::{LiveState, ToolSlot, LIVE_DOC};
use crate::harness::tests::chat_support::{
    all_entries, chat_setup, open_chat, wait_for, ChatEnv, ChatSetup, OpenChat,
};
use crate::harness::tests::support::{
    add_hooks, add_tool, context, empty_object_schema, generation_task, tool_task, Installed,
};
use crate::harness::tests::task_support::{aborted, deferred, Deferred};
use crate::harness::tool::ToolTaskCheckpoint;
use crate::harness::types::{
    AgentChange, EnvFactory, EnvTarget, ExtensionsChange, FieldChange, GenerationHooks,
    InputSubmissionDraft, ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionApi,
    ToolExecutionResult, ToolHooks, ToolRegistration, ToolReplay,
};
use crate::harness::{Harness, TaskAbortResult};
use crate::session::SessionResult;
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::tools::{create_bash_tool, BashToolOptions};
use crate::types::{
    EntryRecord, Storage, SubmissionStatus, TaskId, TaskOutcome, TaskQuery, TaskState,
};

/// TS `sqlitePath()`: a fresh directory (removed when dropped, the TS
/// `afterEach`) and the database path inside it.
fn sqlite_path() -> (tempfile::TempDir, PathBuf) {
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-tools-")
        .tempdir()
        .expect("create a temp dir");
    let path = directory.path().join("session.sqlite");
    (directory, path)
}

async fn sqlite(path: &Path) -> Arc<dyn Storage> {
    Arc::new(
        open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
            .await
            .expect("open the SQLite storage"),
    )
}

/// TS `open(path, setup, env?)`: open the chat and resume scheduling.
async fn open(path: &Path, setup: &ChatSetup, env: Option<ChatEnv>) -> OpenChat {
    let opened = open_chat(sqlite(path).await, setup, env).await.unwrap();
    opened.harness.resume().unwrap();
    opened
}

/// TS `tool(name, execute, extra)` without extras.
fn tool<F, Fut>(name: &str, execute: F) -> ToolRegistration
where
    F: Fn(Arc<dyn ToolExecutionApi>, eukhe_chord::context::Context) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = SessionResult<ToolExecutionResult>> + Send + 'static,
{
    ToolRegistration::new(name, name, empty_object_schema(), move |_, api, cx| {
        execute(api, cx)
    })
}

fn with_replay(mut registration: ToolRegistration, replay: ToolReplay) -> Arc<ToolRegistration> {
    registration.replay = Some(replay);
    define_tool(registration)
}

fn call(name: &str, id: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_tool_call(
            name,
            PiJsonObject::new(),
            Some(id.to_owned()),
        )],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
}

fn done() -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text("done")],
        FauxAssistantMessageOptions::default(),
    )
}

fn go() -> InputSubmissionDraft {
    InputSubmissionDraft::new("go")
}

fn results(entries: &[EntryRecord]) -> Vec<ToolResultMessage> {
    entries
        .iter()
        .filter(|entry| entry.kind == "pi.tool-result")
        .map(
            |entry| match &entry.model.as_ref().expect("a model message")[0] {
                Message::ToolResult(message) => message.clone(),
                other => panic!("not a tool result: {other:?}"),
            },
        )
        .collect()
}

fn text(message: Option<&ToolResultMessage>) -> String {
    message
        .map(|message| {
            message
                .content
                .iter()
                .map(|item| match item {
                    UserContentBlock::Text(text) => text.text.as_str(),
                    UserContentBlock::Image(_) => "",
                })
                .collect::<Vec<_>>()
                .join("|")
        })
        .unwrap_or_default()
}

async fn live(harness: &Harness, chat: &OpenChat) -> Option<LiveState> {
    harness
        .snapshot(&LIVE_DOC, chat.root.id(), context())
        .await
        .unwrap()
        .map(|value| from_json(&JsonValue::Object(value)).unwrap())
}

async fn first_slot(chat: &OpenChat) -> Option<ToolSlot> {
    live(&chat.harness, chat)
        .await
        .and_then(|live| live.tools)
        .and_then(|tools| tools.into_iter().next())
}

async fn tool_task_id(chat: &OpenChat) -> TaskId {
    let id: Arc<Mutex<Option<TaskId>>> = Arc::default();
    wait_for(
        || {
            let slot = first_slot(chat);
            let id = Arc::clone(&id);
            async move {
                let found = slot.await.and_then(|slot| slot.task_id);
                *id.lock().unwrap_or_else(PoisonError::into_inner) = found;
                found.is_some()
            }
        },
        5000,
    )
    .await;
    let found = id.lock().unwrap_or_else(PoisonError::into_inner).take();
    found.expect("a tool task")
}

async fn settle(chat: &OpenChat, id: crate::types::SubmissionId) -> SubmissionStatus {
    chat.harness
        .submission(id, context())
        .await
        .unwrap()
        .expect("the submission exists")
        .wait(context())
        .await
        .unwrap()
        .state
        .status()
}

fn json(value: &serde_json::Value) -> JsonValue {
    JsonValue::from(value.clone())
}

/// TS `blockingTool`: writes output, then blocks until its invocation is
/// cancelled the first time it runs. `started` resolves once the output is
/// durable.
struct Blocking {
    registration: ToolRegistration,
    started: Deferred,
    runs: Arc<AtomicUsize>,
}

fn blocking_tool(name: &str) -> Blocking {
    let started: Deferred = deferred();
    let runs = Arc::new(AtomicUsize::new(0));
    let (gate, counter) = (started.clone(), Arc::clone(&runs));
    let registration = tool(name, move |api, cx| {
        let (gate, counter) = (gate.clone(), Arc::clone(&counter));
        async move {
            let run = counter.fetch_add(1, Ordering::SeqCst) + 1;
            api.output(
                crate::harness::types::ToolOutputChunk::Text(&format!("run {run}\n")),
                None,
            )?;
            api.details(json(&serde_json::json!({ "run": run })), &cx)
                .await?;
            if run <= 1 {
                gate.resolve(());
                return Err(aborted(&cx.abort_signal().expect("a call signal")).await);
            }
            Ok(ToolExecutionResult::default())
        }
    });
    Blocking {
        registration,
        started,
        runs,
    }
}

#[tokio::test]
async fn answers_an_unsafe_tool_interrupted_after_intent_with_its_durable_partial_output() {
    let (_directory, path) = sqlite_path();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let blocking = blocking_tool("work");
    add_tool(&setup.registry, define_tool(blocking.registration), None).unwrap();
    setup
        .faux
        .set_responses(vec![call("work", "c1").into(), done().into()]);
    let opened = open(&path, &setup, None).await;
    let id = opened.root.submit(go(), context()).await.unwrap().id();
    blocking.started.wait().await;
    let task_id = tool_task_id(&opened).await;
    opened.harness.close(context()).await.unwrap();

    let opened = open(&path, &setup, None).await;
    let record = opened
        .harness
        .get_task(task_id, context())
        .await
        .unwrap()
        .expect("the tool task exists");
    let checkpoint: ToolTaskCheckpoint =
        from_json(record.state.checkpoint().expect("a live checkpoint")).unwrap();
    assert_eq!(
        checkpoint,
        ToolTaskCheckpoint::Execute {
            arguments: PiJsonObject::new(),
            replay: ToolReplay::Unsafe,
        }
    );
    assert_eq!(settle(&opened, id).await, SubmissionStatus::Done);
    assert_eq!(blocking.runs.load(Ordering::SeqCst), 1);
    let entries = all_entries(&opened.root, context()).await.unwrap();
    let all = results(&entries);
    let result = all.first();
    assert!(result.unwrap().is_error);
    assert_eq!(
        result.unwrap().details,
        Some(serde_json::json!({ "run": 1 }))
    );
    assert_eq!(
        text(result),
        "run 1\n|<harness>\n[error] Tool work was interrupted and may have partially run\n</harness>"
    );
    assert_eq!(
        live(&opened.harness, &opened).await,
        Some(LiveState::default())
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reruns_a_tool_only_when_both_the_stored_and_the_current_replay_policy_are_safe() {
    let cases = [
        (ToolReplay::Safe, ToolReplay::Safe, true),
        (ToolReplay::Safe, ToolReplay::Unsafe, false),
        (ToolReplay::Unsafe, ToolReplay::Safe, false),
    ];
    for (stored, current, reruns) in cases {
        let (_directory, path) = sqlite_path();
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let blocking = blocking_tool("work");
        let registration: Installed = add_tool(
            &setup.registry,
            with_replay(blocking.registration.clone(), stored),
            None,
        )
        .unwrap();
        setup
            .faux
            .set_responses(vec![call("work", "c1").into(), done().into()]);
        let opened = open(&path, &setup, None).await;
        let id = opened.root.submit(go(), context()).await.unwrap().id();
        blocking.started.wait().await;
        opened.harness.close(context()).await.unwrap();

        registration.dispose();
        add_tool(
            &setup.registry,
            with_replay(blocking.registration.clone(), current),
            None,
        )
        .unwrap();
        let opened = open(&path, &setup, None).await;
        assert_eq!(settle(&opened, id).await, SubmissionStatus::Done);
        let entries = all_entries(&opened.root, context()).await.unwrap();
        let all = results(&entries);
        let result = all.first();
        assert_eq!(
            blocking.runs.load(Ordering::SeqCst),
            if reruns { 2 } else { 1 }
        );
        assert_eq!(result.unwrap().is_error, !reruns);
        if reruns {
            assert_eq!(text(result), "run 2\n");
        }
        opened.harness.close(context()).await.unwrap();
    }
}

#[derive(Clone, Copy)]
enum Change {
    Cwd,
    Deselect,
}

#[tokio::test]
async fn reruns_a_safe_tool_with_the_environment_of_the_conversations_cwd_at_rerun_and_not_once_it_is_deselected(
) {
    for change in [Change::Cwd, Change::Deselect] {
        let (_directory, path) = sqlite_path();
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let cwds: Arc<Mutex<Vec<Option<String>>>> = Arc::default();
        let started: Deferred = deferred();
        let (seen, gate) = (Arc::clone(&cwds), started.clone());
        let work = tool("work", move |api, cx| {
            let (seen, gate) = (Arc::clone(&seen), gate.clone());
            async move {
                let count = {
                    let mut seen = seen.lock().unwrap_or_else(PoisonError::into_inner);
                    seen.push(api.env().map(|env| env.cwd().to_owned()));
                    seen.len()
                };
                if count == 1 {
                    gate.resolve(());
                    return Err(aborted(&cx.abort_signal().expect("a call signal")).await);
                }
                Ok(ToolExecutionResult::default())
            }
        });
        add_tool(&setup.registry, with_replay(work, ToolReplay::Safe), None).unwrap();
        setup
            .faux
            .set_responses(vec![call("work", "c1").into(), done().into()]);
        let env = || {
            ChatEnv::Factory(
                Arc::new(|target: EnvTarget, _: &eukhe_chord::context::Context| {
                    let cwd = target.cwd.unwrap_or_else(|| "/".to_owned());
                    let env: Arc<dyn ExecutionEnv> =
                        Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                            cwd,
                            ..NativeExecutionEnvOptions::default()
                        }));
                    futures::future::ready(Ok(Some(env))).boxed()
                }) as EnvFactory,
            )
        };
        let opened = open(&path, &setup, Some(env())).await;
        opened
            .root
            .configure(
                AgentChange {
                    cwd: FieldChange::Set("/one".to_owned()),
                    ..AgentChange::default()
                },
                context(),
            )
            .await
            .unwrap();
        let id = opened.root.submit(go(), context()).await.unwrap().id();
        started.wait().await;
        let configured = match change {
            Change::Cwd => AgentChange {
                cwd: FieldChange::Set("/two".to_owned()),
                ..AgentChange::default()
            },
            Change::Deselect => AgentChange {
                extensions: FieldChange::Set(ExtensionsChange::Exactly(Vec::new())),
                ..AgentChange::default()
            },
        };
        opened.root.configure(configured, context()).await.unwrap();
        opened.harness.close(context()).await.unwrap();

        let opened = open(&path, &setup, Some(env())).await;
        assert_eq!(settle(&opened, id).await, SubmissionStatus::Done);
        let entries = all_entries(&opened.root, context()).await.unwrap();
        let all = results(&entries);
        let result = all.first();
        let seen = cwds.lock().unwrap_or_else(PoisonError::into_inner).clone();
        match change {
            Change::Cwd => {
                assert_eq!(seen, [Some("/one".to_owned()), Some("/two".to_owned())]);
                assert!(!result.unwrap().is_error);
            }
            Change::Deselect => {
                // A tool that no longer resolves is treated as unsafe: interrupted, not rerun.
                assert_eq!(seen, [Some("/one".to_owned())]);
                assert!(text(result).contains("was interrupted"));
            }
        }
        opened.harness.close(context()).await.unwrap();
    }
}

#[tokio::test]
async fn reruns_before_tool_when_interrupted_before_intent_and_executes_once() {
    let (_directory, path) = sqlite_path();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let runs = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&runs);
    let work = tool("work", move |_, _| {
        counter.fetch_add(1, Ordering::SeqCst);
        async {
            Ok(ToolExecutionResult {
                content: Some(Vec::new()),
                ..ToolExecutionResult::default()
            })
        }
    });
    add_tool(&setup.registry, define_tool(work), None).unwrap();
    let reached: Deferred = deferred();
    let asked = Arc::new(AtomicUsize::new(0));
    let decisions: Arc<Mutex<Vec<String>>> = Arc::default();
    let (gate, count, decided) = (reached.clone(), Arc::clone(&asked), Arc::clone(&decisions));
    add_hooks(
        &setup.registry,
        tool_task(),
        ToolHooks {
            before_tool: Some(Arc::new(move |_, api, cx| {
                let asked = count.fetch_add(1, Ordering::SeqCst) + 1;
                // A durable first-writer-wins decision survives the rerun.
                let memo = api.memo_or("test:decision", &format!("attempt {asked}"), cx);
                let (gate, decided, cx) = (gate.clone(), Arc::clone(&decided), cx.clone());
                async move {
                    let decision = memo.await?;
                    decided
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(decision);
                    if asked == 1 {
                        gate.resolve(());
                        return Err(aborted(&cx.abort_signal().expect("a call signal")).await);
                    }
                    Ok(None)
                }
                .boxed()
            })),
            ..ToolHooks::default()
        },
        None,
    )
    .unwrap();
    setup
        .faux
        .set_responses(vec![call("work", "c1").into(), done().into()]);
    let opened = open(&path, &setup, None).await;
    let id = opened.root.submit(go(), context()).await.unwrap().id();
    reached.wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open(&path, &setup, None).await;
    assert_eq!(settle(&opened, id).await, SubmissionStatus::Done);
    assert_eq!(
        [asked.load(Ordering::SeqCst), runs.load(Ordering::SeqCst)],
        [2, 1]
    );
    assert_eq!(
        *decisions.lock().unwrap_or_else(PoisonError::into_inner),
        ["attempt 1", "attempt 1"]
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reruns_the_generation_tools_phase_interrupted_before_its_commit() {
    let (_directory, path) = sqlite_path();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let work = tool("work", |_, _| async {
        Ok(ToolExecutionResult {
            content: Some(Vec::new()),
            ..ToolExecutionResult::default()
        })
    });
    add_tool(&setup.registry, define_tool(work), None).unwrap();
    let reached: Deferred = deferred();
    let observed = Arc::new(AtomicUsize::new(0));
    let (gate, count) = (reached.clone(), Arc::clone(&observed));
    add_hooks(
        &setup.registry,
        generation_task(),
        GenerationHooks {
            after_tools: Some(Arc::new(move |_, _, _, cx| {
                let observed = count.fetch_add(1, Ordering::SeqCst) + 1;
                let (gate, cx) = (gate.clone(), cx.clone());
                async move {
                    if observed == 1 {
                        gate.resolve(());
                        return Err(aborted(&cx.abort_signal().expect("a call signal")).await);
                    }
                    Ok(())
                }
                .boxed()
            })),
            ..GenerationHooks::default()
        },
        None,
    )
    .unwrap();
    setup
        .faux
        .set_responses(vec![call("work", "c1").into(), done().into()]);
    let opened = open(&path, &setup, None).await;
    let id = opened.root.submit(go(), context()).await.unwrap().id();
    reached.wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open(&path, &setup, None).await;
    assert_eq!(settle(&opened, id).await, SubmissionStatus::Done);
    assert_eq!(observed.load(Ordering::SeqCst), 2);
    let kinds: Vec<String> = all_entries(&opened.root, context())
        .await
        .unwrap()
        .into_iter()
        .map(|entry| entry.kind)
        .collect();
    assert_eq!(
        kinds,
        [
            "pi.user",
            "pi.system",
            "pi.assistant",
            "pi.tool-result",
            "pi.assistant"
        ]
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn answers_an_aborted_tool_with_its_partial_output_and_continues_the_run() {
    let (_directory, path) = sqlite_path();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let blocking = blocking_tool("work");
    add_tool(&setup.registry, define_tool(blocking.registration), None).unwrap();
    setup
        .faux
        .set_responses(vec![call("work", "c1").into(), done().into()]);
    let opened = open(&path, &setup, None).await;
    let submission = opened.root.submit(go(), context()).await.unwrap();
    blocking.started.wait().await;
    let task_id = tool_task_id(&opened).await;
    assert_eq!(
        opened.harness.abort_task(task_id, context()).await.unwrap(),
        TaskAbortResult::Marked
    );
    let outcome = opened
        .harness
        .wait_for_task(task_id, context())
        .await
        .unwrap()
        .outcome;
    assert!(
        matches!(
            &outcome,
            TaskOutcome::Aborted { result: Some(result), .. }
                if result.get("entryId").and_then(JsonValue::as_f64).is_some()
        ),
        "{outcome:?}"
    );
    assert_eq!(
        submission.wait(context()).await.unwrap().state.status(),
        SubmissionStatus::Done
    );
    let entries = all_entries(&opened.root, context()).await.unwrap();
    assert_eq!(
        text(results(&entries).first()),
        "run 1\n|<harness>\n[error] Tool work was aborted\n</harness>"
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lets_context_derivation_answer_a_faulted_tool_and_continues_the_run() {
    let (_directory, path) = sqlite_path();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    // A result that is not strict JSON makes the result commit throw, so the scheduler faults the task.
    let bad = tool("bad", |_, _| async {
        Ok(ToolExecutionResult {
            content: Some(Vec::new()),
            usage: Some(Usage {
                input: u64::MAX,
                ..Usage::default()
            }),
            ..ToolExecutionResult::default()
        })
    });
    add_tool(&setup.registry, define_tool(bad), None).unwrap();
    let requests: Arc<Mutex<Vec<String>>> = Arc::default();
    let seen = Arc::clone(&requests);
    setup.faux.set_responses(vec![
        call("bad", "c1").into(),
        FauxResponseStep::factory(move |request, _, _, _| {
            let result = request.messages().iter().find_map(|message| match message {
                Message::ToolResult(result) => Some(result),
                _ => None,
            });
            seen.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(result.map_or_else(|| "none".to_owned(), |result| text(Some(result))));
            Ok(done())
        }),
    ]);
    let opened = open(&path, &setup, None).await;
    let settled = opened
        .root
        .submit(go(), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_eq!(settled.state.status(), SubmissionStatus::Done);
    let entries = all_entries(&opened.root, context()).await.unwrap();
    assert_eq!(results(&entries), Vec::<ToolResultMessage>::new());
    assert_eq!(
        *requests.lock().unwrap_or_else(PoisonError::into_inner),
        ["Tool result unavailable: history ends before this call completed."]
    );
    let conversation_id = opened.root.id();
    let tasks = opened
        .harness
        .commit(
            move |tx| async move {
                tx.scan_tasks(
                    TaskQuery {
                        conversation_id: Some(conversation_id),
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
    let faulted = tasks
        .items
        .iter()
        .find(|task| task.kind == "pi.tool")
        .expect("the tool task");
    assert!(
        matches!(
            faulted.state,
            TaskState::Terminal {
                outcome: TaskOutcome::Faulted { .. }
            }
        ),
        "{:?}",
        faulted.state
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn answers_a_real_bash_command_interrupted_by_close_and_reopen_then_finishes_the_run() {
    let (directory, path) = sqlite_path();
    let env = || {
        ChatEnv::One(Arc::new(NativeExecutionEnv::new(
            NativeExecutionEnvOptions {
                cwd: directory.path().to_string_lossy().into_owned(),
                ..NativeExecutionEnvOptions::default()
            },
        )))
    };
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(
        &setup.registry,
        create_bash_tool(BashToolOptions::default()),
        None,
    )
    .unwrap();
    let serde_json::Value::Object(arguments) =
        serde_json::json!({ "command": "echo started; sleep 30" })
    else {
        unreachable!("an object literal");
    };
    setup.faux.set_responses(vec![
        faux_assistant_message(
            vec![faux_tool_call("bash", arguments, Some("b".to_owned()))],
            FauxAssistantMessageOptions {
                stop_reason: Some(StopReason::ToolUse),
                ..FauxAssistantMessageOptions::default()
            },
        )
        .into(),
        done().into(),
    ]);
    let opened = open(&path, &setup, Some(env())).await;
    let id = opened.root.submit(go(), context()).await.unwrap().id();
    wait_for(
        || {
            let slot = first_slot(&opened);
            async move { slot.await.and_then(|slot| slot.output).as_deref() == Some("started\n") }
        },
        5000,
    )
    .await;
    opened.harness.close(context()).await.unwrap();

    let opened = open(&path, &setup, Some(env())).await;
    assert_eq!(settle(&opened, id).await, SubmissionStatus::Done);
    let entries = all_entries(&opened.root, context()).await.unwrap();
    assert_eq!(
        text(results(&entries).first()),
        "started\n|<harness>\n[error] Tool bash was interrupted and may have partially run\n</harness>"
    );
    opened.harness.close(context()).await.unwrap();
}

fn info(message: &str) -> ToolDiagnostic {
    ToolDiagnostic {
        severity: ToolDiagnosticSeverity::Info,
        code: None,
        message: message.to_owned(),
    }
}

#[tokio::test]
async fn clears_the_interrupted_attempts_progress_before_a_safe_rerun() {
    let (_directory, path) = sqlite_path();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let started: [Deferred; 2] = [deferred(), deferred()];
    let runs = Arc::new(AtomicUsize::new(0));
    let (gates, counter) = (started.clone(), Arc::clone(&runs));
    let work = tool("work", move |api, cx| {
        let (gates, counter) = (gates.clone(), Arc::clone(&counter));
        async move {
            let run = counter.fetch_add(1, Ordering::SeqCst);
            if run == 0 {
                api.diagnostic(info("first a"))?;
                api.diagnostic(info("first b"))?;
                api.details(json(&serde_json::json!({ "run": 1, "extra": true })), &cx)
                    .await?;
            } else {
                api.diagnostic(info("second"))?;
                api.details(json(&serde_json::json!({ "run": 2 })), &cx)
                    .await?;
            }
            gates[run].resolve(());
            Err(aborted(&cx.abort_signal().expect("a call signal")).await)
        }
    });
    add_tool(&setup.registry, with_replay(work, ToolReplay::Safe), None).unwrap();
    setup
        .faux
        .set_responses(vec![call("work", "c1").into(), done().into()]);
    let opened = open(&path, &setup, None).await;
    opened.root.submit(go(), context()).await.unwrap();
    started[0].wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open(&path, &setup, None).await;
    started[1].wait().await;
    let slot = first_slot(&opened).await.expect("the tool slot");
    assert_eq!(slot.diagnostics, Some(vec![info("second")]));
    assert_eq!(slot.details, Some(json(&serde_json::json!({ "run": 2 }))));
    opened.harness.close(context()).await.unwrap();
}
