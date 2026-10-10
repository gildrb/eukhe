//! Port of `test/harness-nested-tools-restart.test.ts`: nested tool calls
//! across a restart.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use eukhe_chord::json::JsonValue;
use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;
use futures::FutureExt;
use serde_json::json;

use super::nested_support::{
    call_with, end_result, exec, exec_key, hang, listen, lock, nested_tasks, open_sqlite, plain,
    results, settle, sqlite_path, submit_go, text_result, Slot,
};
use super::support::{done, tool, tool_with};
use crate::harness::define::define_extension;
use crate::harness::tests::chat_support::{all_entries, chat_setup, ChatSetup};
use crate::harness::tests::support::{add_hooks, add_tool, context, tool_task};
use crate::harness::tests::task_support::{deferred, eventually};
use crate::harness::types::{
    ConversationAbortOptions, Extension, InvocationTaskOptions, NestedToolExecutionResult,
    SchedulingState, TaskInspectionState, ToolExecutionApiExt, ToolExecutionResult, ToolHooks,
    ToolOutputChunk, ToolReplay,
};
use crate::harness::Harness;
use crate::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use crate::types::{
    ConversationOwnership, SubmissionStatus, TaskAbortReason, TaskId, TaskOptions, TaskOutcome,
    TaskOwnership, TaskStatus,
};

type NullTask = Task<JsonValue, JsonValue, JsonValue, ()>;
type Aborts = Arc<Mutex<Vec<Option<TaskAbortReason>>>>;

fn setup() -> ChatSetup {
    chat_setup(RegisterFauxProviderOptions::default())
}

fn json_value(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn aborted_state() -> NextTaskState<JsonValue, JsonValue> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: None,
            result: None,
        },
    }
}

/// A task that runs until aborted, records each `work` phase in `phases`
/// and resolves `started`, and whose abort handler records the abort reason
/// in `aborts` and ends it `aborted`.
fn worker(
    name: &'static str,
    phases: &Arc<Mutex<Vec<String>>>,
    aborts: &Aborts,
    started: &crate::harness::tests::task_support::Deferred,
) -> NullTask {
    let (phases, aborts, started) = (Arc::clone(phases), Arc::clone(aborts), started.clone());
    define_task(
        TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
            name,
            1,
            |_: &JsonValue| Ok(json_value(r#"{"phase":"work"}"#)),
            move |task, runtime, cx| {
                lock(&aborts).push(task.abort_reason);
                async move {
                    runtime
                        .commit(|_tx, _current| async { Ok(Some(aborted_state())) }, &cx)
                        .await
                }
            },
        )
        .phase("work", move |_task, runtime, _cx| {
            lock(&phases).push("work".to_owned());
            let started = started.clone();
            async move {
                started.resolve(());
                crate::harness::tests::task_support::aborted(&runtime.signal()).await;
                Ok(())
            }
        }),
    )
}

/// A `spawn` tool that creates `task` owned by its call and waits for it,
/// recording its ID in `worker`.
fn spawn_tool(
    task: &NullTask,
    worker: &Slot<TaskId>,
) -> Arc<crate::harness::types::ToolRegistration> {
    let (task, worker) = (task.clone(), Arc::clone(worker));
    tool("spawn", move |_, api, cx| {
        let (task, worker) = (task.clone(), Arc::clone(&worker));
        async move {
            let options = InvocationTaskOptions {
                ownership: TaskOwnership::Task {
                    task_id: api.task_id(),
                },
                background: None,
                abandon_on_restart: None,
            };
            let id = api
                .create_task(&task, &JsonValue::Null, options, &cx)
                .await?
                .erase();
            *lock(&worker) = Some(id);
            api.wait_for_task(id, &cx).await?;
            Ok(ToolExecutionResult::default())
        }
    })
}

/// A `batch` tool that makes one nested `spawn` call.
fn batch_spawn() -> Arc<crate::harness::types::ToolRegistration> {
    tool("batch", |_, api, cx| async move {
        exec(&api, "spawn", json!({}), &cx).await?;
        Ok(ToolExecutionResult::default())
    })
}

fn extension(name: &str, task: &NullTask) -> Arc<Extension> {
    define_extension(Extension {
        name: name.to_owned(),
        tasks: vec![task.erase()],
        ..Extension::default()
    })
}

fn queue(setup: &ChatSetup, tool: &str) {
    setup
        .faux
        .set_responses(vec![call_with(tool, json!({}), "c1").into(), done().into()]);
}

fn codes(result: Option<&NestedToolExecutionResult>) -> Vec<String> {
    result
        .map(|result| {
            result
                .diagnostics
                .iter()
                .filter_map(|diagnostic| diagnostic.code.clone())
                .collect()
        })
        .unwrap_or_default()
}

async fn state_of(harness: &Harness, id: TaskId) -> serde_json::Value {
    plain(
        &harness
            .get_task(id, context())
            .await
            .unwrap()
            .expect("the task exists")
            .state,
    )
}

#[tokio::test]
#[expect(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn abandons_a_replay_unsafe_callers_unfinished_nested_calls_before_they_run_again() {
    let (_directory, path) = sqlite_path("pi-durable-nested-restart-");
    let setup = setup();
    let started_runs = Arc::new(AtomicUsize::new(0));
    let gated_runs = Arc::new(AtomicUsize::new(0));
    let running = deferred::<()>();
    let gated = deferred::<()>();
    // Replay-safe, so only the abandonment keeps it from rerunning.
    {
        let (runs, running) = (Arc::clone(&started_runs), running.clone());
        add_tool(
            &setup.registry,
            tool_with(
                "started",
                move |_, api, cx| {
                    runs.fetch_add(1, Ordering::SeqCst);
                    let running = running.clone();
                    async move {
                        api.output(ToolOutputChunk::Text("partial\n"), None)?;
                        api.details(json_value(r#"{"step":1}"#), &cx).await?;
                        running.resolve(());
                        Err(hang(&cx).await)
                    }
                },
                |tool| tool.replay = Some(ToolReplay::Safe),
            ),
            None,
        )
        .unwrap();
    }
    {
        let runs = Arc::clone(&gated_runs);
        add_tool(
            &setup.registry,
            tool("gated", move |_, _, _| {
                runs.fetch_add(1, Ordering::SeqCst);
                async { Ok(ToolExecutionResult::default()) }
            }),
            None,
        )
        .unwrap();
    }
    // Holds `gated` in its `call` phase, before intent, until the Harness closes.
    {
        let gated = gated.clone();
        add_hooks(
            &setup.registry,
            tool_task(),
            ToolHooks {
                before_tool: Some(Arc::new(move |call, _, cx| {
                    let is_gated = call.name == "gated";
                    let (gated, cx) = (gated.clone(), cx.clone());
                    async move {
                        if !is_gated {
                            return Ok(None);
                        }
                        gated.resolve(());
                        Err(hang(&cx).await)
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
            let (first, second) = futures::join!(
                exec(&api, "started", json!({}), &cx),
                exec(&api, "gated", json!({}), &cx)
            );
            first?;
            second?;
            Ok(ToolExecutionResult::default())
        }),
        None,
    )
    .unwrap();
    queue(&setup, "batch");
    let opened = open_sqlite(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    running.wait().await;
    gated.wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_sqlite(&path, &setup).await;
    let (stream, events) = listen(&opened.harness, opened.root.id()).await;
    opened.harness.resume().unwrap();
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    opened.harness.wait_for_idle(context()).await.unwrap();
    stream.stop().await;
    assert_eq!(
        (
            started_runs.load(Ordering::SeqCst),
            gated_runs.load(Ordering::SeqCst)
        ),
        (1, 0)
    );
    for task in nested_tasks(&opened.harness).await {
        assert!(task.abandon_on_restart && task.abort_requested, "{task:?}");
        assert_eq!(task.abort_reason, Some(TaskAbortReason::Restart));
        let state = plain(&task.state);
        assert_eq!(
            (&state["status"], &state["outcome"]["status"]),
            (&json!("terminal"), &json!("aborted"))
        );
    }
    let started = end_result(&events, "c1/1");
    assert_eq!(codes(started.as_ref()), ["interrupted"]);
    let started = started.expect("the started call ends with a result");
    assert!(started.is_error);
    assert_eq!(started.details, Some(json_value(r#"{"step":1}"#)));
    assert_eq!(started.structured_output, None);
    assert_eq!(codes(end_result(&events, "c1/2").as_ref()), ["abandoned"]);
    // The caller reports the interruption.
    let entries = all_entries(&opened.root, context()).await.unwrap();
    let result = &results(&entries)[0];
    assert_eq!(
        (result.tool_call_id.as_str(), result.is_error),
        ("c1", true)
    );
    super::nested_support::assert_live_empty(&opened.harness, opened.root.id()).await;
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn abandons_the_work_an_abandoned_nested_call_owns_which_never_runs_a_phase_again() {
    let (_directory, path) = sqlite_path("pi-durable-nested-restart-");
    let setup = setup();
    let phases: Arc<Mutex<Vec<String>>> = Arc::default();
    let aborts: Aborts = Arc::default();
    let started = deferred::<()>();
    let task = worker("test.worker", &phases, &aborts, &started);
    setup.registry.install(extension("worker", &task)).unwrap();
    let worker_id: Slot<TaskId> = Arc::default();
    add_tool(&setup.registry, spawn_tool(&task, &worker_id), None).unwrap();
    add_tool(&setup.registry, batch_spawn(), None).unwrap();
    queue(&setup, "batch");
    let opened = open_sqlite(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    started.wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_sqlite(&path, &setup).await;
    opened.harness.resume().unwrap();
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    opened.harness.wait_for_idle(context()).await.unwrap();
    assert_eq!(*lock(&phases), ["work"]);
    // The cascade passed the restart reason on.
    assert_eq!(*lock(&aborts), [Some(TaskAbortReason::Restart)]);
    let worker = lock(&worker_id).expect("the worker was created");
    let state = state_of(&opened.harness, worker).await;
    assert_eq!(
        (&state["status"], &state["outcome"]["status"]),
        (&json!("terminal"), &json!("aborted"))
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_an_abandoned_task_whose_definition_is_missing_waiting_until_it_is_installed_then_runs_its_abort(
) {
    let (_directory, path) = sqlite_path("pi-durable-nested-restart-");
    let setup = setup();
    let phases: Arc<Mutex<Vec<String>>> = Arc::default();
    let aborts: Aborts = Arc::default();
    let started = deferred::<()>();
    let task = worker("test.late", &phases, &aborts, &started);
    let late = extension("late", &task);
    setup.registry.install(Arc::clone(&late)).unwrap();
    let worker_id: Slot<TaskId> = Arc::default();
    add_tool(&setup.registry, spawn_tool(&task, &worker_id), None).unwrap();
    add_tool(&setup.registry, batch_spawn(), None).unwrap();
    queue(&setup, "batch");
    let opened = open_sqlite(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    started.wait().await;
    opened.harness.close(context()).await.unwrap();

    setup.registry.uninstall(&late);
    let opened = open_sqlite(&path, &setup).await;
    opened.harness.resume().unwrap();
    let worker = lock(&worker_id).expect("the worker was created");
    let harness = opened.harness.clone();
    eventually(|| {
        let harness = harness.clone();
        async move {
            harness
                .inspect(context())
                .await
                .unwrap()
                .tasks
                .into_iter()
                .find(|task| task.record.id == worker)
                .is_some_and(|task| matches!(task.state, TaskInspectionState::Blocked { .. }))
        }
    })
    .await;
    assert_ne!(
        state_of(&opened.harness, worker).await["status"],
        "terminal"
    );
    assert!(lock(&aborts).is_empty());
    setup.registry.install(Arc::clone(&late)).unwrap();
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    assert_eq!(*lock(&aborts), [Some(TaskAbortReason::Restart)]);
    let state = state_of(&opened.harness, worker).await;
    assert_eq!(
        (&state["status"], &state["outcome"]["status"]),
        (&json!("terminal"), &json!("aborted"))
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn orphans_an_abandoned_task_whose_definition_is_missing_once_an_abort_is_requested() {
    let (_directory, path) = sqlite_path("pi-durable-nested-restart-");
    let setup = setup();
    let phases: Arc<Mutex<Vec<String>>> = Arc::default();
    let aborts: Aborts = Arc::default();
    let started = deferred::<()>();
    let task = worker("test.gone", &phases, &aborts, &started);
    let gone = extension("gone", &task);
    setup.registry.install(Arc::clone(&gone)).unwrap();
    let worker_id: Slot<TaskId> = Arc::default();
    add_tool(&setup.registry, spawn_tool(&task, &worker_id), None).unwrap();
    add_tool(&setup.registry, batch_spawn(), None).unwrap();
    queue(&setup, "batch");
    let opened = open_sqlite(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    started.wait().await;
    opened.harness.close(context()).await.unwrap();

    setup.registry.uninstall(&gone);
    let opened = open_sqlite(&path, &setup).await;
    opened.harness.resume().unwrap();
    let worker = lock(&worker_id).expect("the worker was created");
    let harness = opened.harness.clone();
    eventually(|| {
        let harness = harness.clone();
        async move {
            harness
                .get_task(worker, context())
                .await
                .unwrap()
                .is_some_and(|record| record.abort_reason == Some(TaskAbortReason::Restart))
        }
    })
    .await;
    opened
        .root
        .abort(ConversationAbortOptions::default(), context())
        .await
        .unwrap();
    let state = state_of(&opened.harness, worker).await;
    assert_eq!(
        (&state["status"], &state["outcome"]),
        (
            &json!("terminal"),
            &json!({ "status": "orphaned", "reason": "missing_task" })
        )
    );
    assert_eq!(
        settle(&opened.harness, id).await,
        SubmissionStatus::Unanswered
    );
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn marks_nothing_when_the_reopened_harness_never_starts_scheduling() {
    let (_directory, path) = sqlite_path("pi-durable-nested-restart-");
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
    queue(&setup, "batch");
    let opened = open_sqlite(&path, &setup).await;
    submit_go(&opened.root).await;
    running.wait().await;
    opened.harness.close(context()).await.unwrap();

    // An inspection-only open: no resume, no submission.
    let opened = open_sqlite(&path, &setup).await;
    let inspected = opened.harness.inspect(context()).await.unwrap();
    assert_eq!(inspected.scheduling, SchedulingState::Paused);
    opened.harness.close(context()).await.unwrap();

    let opened = open_sqlite(&path, &setup).await;
    let nested = nested_tasks(&opened.harness).await;
    let nested = &nested[0];
    assert!(
        nested.abandon_on_restart && !nested.abort_requested,
        "{nested:?}"
    );
    assert_eq!(nested.state.status(), TaskStatus::Pending);
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn lets_a_replay_safe_callers_unfinished_nested_calls_recover_and_reattaches_to_them_by_key()
{
    let (_directory, path) = sqlite_path("pi-durable-nested-restart-");
    let setup = setup();
    let safe_runs = Arc::new(AtomicUsize::new(0));
    let unsafe_runs = Arc::new(AtomicUsize::new(0));
    let caller_runs = Arc::new(AtomicUsize::new(0));
    let running = [deferred::<()>(), deferred::<()>()];
    {
        let (runs, running) = (Arc::clone(&safe_runs), running[0].clone());
        add_tool(
            &setup.registry,
            tool_with(
                "safe",
                move |_, _, cx| {
                    let run = runs.fetch_add(1, Ordering::SeqCst) + 1;
                    let running = running.clone();
                    async move {
                        if run == 1 {
                            running.resolve(());
                            hang(&cx).await;
                        }
                        Ok(text_result(&format!("safe run {run}")))
                    }
                },
                |tool| tool.replay = Some(ToolReplay::Safe),
            ),
            None,
        )
        .unwrap();
    }
    {
        let (runs, running) = (Arc::clone(&unsafe_runs), running[1].clone());
        add_tool(
            &setup.registry,
            tool("unsafe", move |_, _, cx| {
                runs.fetch_add(1, Ordering::SeqCst);
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
    let received: Arc<Mutex<Vec<NestedToolExecutionResult>>> = Arc::default();
    {
        let (runs, sink) = (Arc::clone(&caller_runs), Arc::clone(&received));
        add_tool(
            &setup.registry,
            tool_with(
                "batch",
                move |_, api, cx| {
                    runs.fetch_add(1, Ordering::SeqCst);
                    let sink = Arc::clone(&sink);
                    async move {
                        let (safe, unsafe_) = futures::join!(
                            exec(&api, "safe", json!({}), &cx),
                            exec(&api, "unsafe", json!({}), &cx)
                        );
                        *lock(&sink) = vec![safe?, unsafe_?];
                        Ok(ToolExecutionResult::default())
                    }
                },
                |tool| tool.replay = Some(ToolReplay::Safe),
            ),
            None,
        )
        .unwrap();
    }
    queue(&setup, "batch");
    let opened = open_sqlite(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    running[0].wait().await;
    running[1].wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_sqlite(&path, &setup).await;
    opened.harness.resume().unwrap();
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    assert_eq!(
        (
            safe_runs.load(Ordering::SeqCst),
            unsafe_runs.load(Ordering::SeqCst),
            caller_runs.load(Ordering::SeqCst)
        ),
        (2, 1, 2)
    );
    // Default keys follow call order, so the rerun found both calls.
    let nested = nested_tasks(&opened.harness).await;
    assert_eq!(nested.len(), 2);
    for task in &nested {
        assert!(!task.abandon_on_restart, "{task:?}");
        assert_eq!(task.abort_reason, None);
    }
    let received = lock(&received).clone();
    assert_eq!(
        received[0].structured_output,
        Some(JsonValue::from("safe run 2"))
    );
    assert_eq!(codes(received.get(1)), ["interrupted"]);
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reattaches_a_replay_safe_caller_by_default_and_explicit_keys_and_rejects_a_rerun_that_calls_differently(
) {
    for swapped in [false, true] {
        let (_directory, path) = sqlite_path("pi-durable-nested-restart-");
        let setup = setup();
        let runs: Arc<Mutex<Vec<String>>> = Arc::default();
        {
            let runs = Arc::clone(&runs);
            add_tool(
                &setup.registry,
                tool("echo", move |args, _, _| {
                    let text = args["text"].as_str().unwrap_or_default().to_owned();
                    lock(&runs).push(text.clone());
                    async move { Ok(text_result(&format!("echo {text}"))) }
                }),
                None,
            )
            .unwrap();
        }
        let blocked = deferred::<()>();
        let caller_runs = Arc::new(AtomicUsize::new(0));
        let seen: Arc<Mutex<Vec<String>>> = Arc::default();
        {
            let (blocked, caller_runs, seen) =
                (blocked.clone(), Arc::clone(&caller_runs), Arc::clone(&seen));
            add_tool(
                &setup.registry,
                tool_with(
                    "batch",
                    move |_, api, cx| {
                        let run = caller_runs.fetch_add(1, Ordering::SeqCst) + 1;
                        let (blocked, seen) = (blocked.clone(), Arc::clone(&seen));
                        async move {
                            let first = if run == 2 && swapped { "b" } else { "a" };
                            let one = exec(&api, "echo", json!({ "text": first }), &cx).await?;
                            let named =
                                exec_key(&api, "echo", json!({ "text": "named" }), &cx, "named")
                                    .await?;
                            if run == 1 {
                                blocked.resolve(());
                                return Err(hang(&cx).await);
                            }
                            *lock(&seen) = [one, named]
                                .iter()
                                .map(|result| {
                                    result
                                        .structured_output
                                        .as_ref()
                                        .and_then(JsonValue::as_str)
                                        .unwrap_or_default()
                                        .to_owned()
                                })
                                .collect();
                            Ok(ToolExecutionResult::default())
                        }
                    },
                    |tool| tool.replay = Some(ToolReplay::Safe),
                ),
                None,
            )
            .unwrap();
        }
        queue(&setup, "batch");
        let opened = open_sqlite(&path, &setup).await;
        let id = submit_go(&opened.root).await;
        blocked.wait().await;
        opened.harness.close(context()).await.unwrap();

        let opened = open_sqlite(&path, &setup).await;
        opened.harness.resume().unwrap();
        assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
        let entries = all_entries(&opened.root, context()).await.unwrap();
        let result = &results(&entries)[0];
        assert_eq!(*lock(&runs), ["a", "named"]);
        if swapped {
            // Key 1 was made with other arguments: the rerun throws instead of reusing a different call's result.
            assert!(result.is_error);
            let content = serde_json::to_string(&result.content).unwrap();
            assert!(
                content.contains("Nested call c1/1 was already made with another tool"),
                "{content}"
            );
        } else {
            assert_eq!(*lock(&seen), ["echo a", "echo named"]);
            assert!(!result.is_error);
        }
        opened.harness.close(context()).await.unwrap();
    }
}

#[tokio::test]
async fn abandons_the_child_tasks_a_replay_unsafe_tool_created_and_awaited_in_memory() {
    let (_directory, path) = sqlite_path("pi-durable-nested-restart-");
    let setup = setup();
    let phases: Arc<Mutex<Vec<String>>> = Arc::default();
    let aborts: Aborts = Arc::default();
    let started = deferred::<()>();
    let task = worker("test.direct-worker", &phases, &aborts, &started);
    setup
        .registry
        .install(extension("direct-worker", &task))
        .unwrap();
    let worker_id: Slot<TaskId> = Arc::default();
    // TS names this tool `work`; it is the `spawn` tool under that name.
    let mut work = (*spawn_tool(&task, &worker_id)).clone();
    work.name = "work".to_owned();
    add_tool(
        &setup.registry,
        crate::harness::define::define_tool(work),
        None,
    )
    .unwrap();
    queue(&setup, "work");
    let opened = open_sqlite(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    started.wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_sqlite(&path, &setup).await;
    opened.harness.resume().unwrap();
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    let aborts: Vec<String> = lock(&aborts)
        .iter()
        .map(|reason| format!("abort {}", plain(reason).as_str().unwrap_or("undefined")))
        .collect();
    let mut seen = lock(&phases).clone();
    seen.extend(aborts);
    assert_eq!(seen, ["work", "abort restart"]);
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn leaves_background_work_under_an_abandoned_nested_call_running_and_settles_without_it() {
    let (_directory, path) = sqlite_path("pi-durable-nested-restart-");
    let setup = setup();
    let phases: Arc<Mutex<Vec<String>>> = Arc::default();
    let aborts: Aborts = Arc::default();
    let started = deferred::<()>();
    let task = worker("test.background", &phases, &aborts, &started);
    setup
        .registry
        .install(extension("background", &task))
        .unwrap();
    let background: Slot<TaskId> = Arc::default();
    {
        let (task, background) = (task.clone(), Arc::clone(&background));
        add_tool(
            &setup.registry,
            tool("spawn", move |_, api, cx| {
                let (definition, background) = (task.as_definition_ref(), Arc::clone(&background));
                async move {
                    // A conversation the call owns, with background work in it, as a persistent subagent has.
                    let task_id = api.task_id();
                    let id = api
                        .commit(
                            move |tx| async move {
                                let child = tx
                                    .create_conversation(ConversationOwnership::Task { task_id })
                                    .await?;
                                tx.create_task(
                                    definition,
                                    JsonValue::Null,
                                    TaskOptions {
                                        ownership: TaskOwnership::Conversation,
                                        conversation_id: Some(child.id),
                                        background: Some(true),
                                        abandon_on_restart: None,
                                    },
                                )
                                .await
                            },
                            &cx,
                        )
                        .await?;
                    *lock(&background) = Some(id);
                    Err(hang(&cx).await)
                }
            }),
            None,
        )
        .unwrap();
    }
    add_tool(&setup.registry, batch_spawn(), None).unwrap();
    queue(&setup, "batch");
    let opened = open_sqlite(&path, &setup).await;
    let id = submit_go(&opened.root).await;
    started.wait().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_sqlite(&path, &setup).await;
    opened.harness.resume().unwrap();
    assert_eq!(settle(&opened.harness, id).await, SubmissionStatus::Done);
    let spawn = nested_tasks(&opened.harness).await[0].clone();
    assert_eq!(spawn.abort_reason, Some(TaskAbortReason::Restart));
    assert_eq!(spawn.state.status(), TaskStatus::Terminal);
    let background = lock(&background).expect("the background task was created");
    let record = opened
        .harness
        .get_task(background, context())
        .await
        .unwrap()
        .expect("the background task exists");
    assert!(!record.abort_requested);
    assert_eq!(record.state.status(), TaskStatus::Running);
    opened
        .harness
        .abort_task(background, context())
        .await
        .unwrap();
    opened.harness.close(context()).await.unwrap();
}
