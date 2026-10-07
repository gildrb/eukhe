//! Port of `test/harness-tools.test.ts` `describe("tool execution api")`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{to_json, JsonValue};
use eukhe_pi_ai::providers::faux::RegisterFauxProviderOptions;
use futures::FutureExt;

use super::support::{calls, done, empty_content, result_text, results, run_with, tool};
use crate::env::{ExecutionEnv, NativeExecutionEnv, NativeExecutionEnvOptions};
use crate::harness::agent::configure;
use crate::harness::tests::chat_support::{chat_setup, open_chat, ChatEnv, OpenChat};
use crate::harness::tests::support::{add_task, add_tool, context};
use crate::harness::tests::task_support::completed;
use crate::harness::types::{
    AgentChange, EnvFactory, EnvTarget, FieldChange, InputSubmissionDraft, InvocationTaskOptions,
    ToolExecutionApiExt, ToolExecutionMode, ToolExecutionResult, ToolRegistration,
};
use crate::session::SessionError;
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, Task, TaskDefinition};
use crate::types::{ConversationId, EntryDraft, TaskOwnership};
use eukhe_types::pi_ai::{TextContent, UserContentBlock};

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

type JsonTask = Task<JsonValue, JsonValue, JsonValue, ()>;
type Targets = Arc<Mutex<Vec<(ConversationId, Option<String>)>>>;

/// TS `test.child`: completes with twice its input `n`.
fn child_task() -> JsonTask {
    define_task(
        TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
            "test.child",
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"run"}"#)),
            |_, _, _| async { Ok(()) },
        )
        .phase("run", |task, runtime, cx| async move {
            let n = task.input["n"].as_f64().expect("numeric input");
            runtime
                .commit(
                    move |_, _| async move { Ok(Some(completed(to_json(&(n * 2.0))?))) },
                    &cx,
                )
                .await
        }),
    )
}

/// TS `probe`: records its environment, agent, registry, commit, memos, and
/// a child task's outcome.
fn probe_tool(child: JsonTask, sink: Arc<Mutex<Vec<JsonValue>>>) -> Arc<ToolRegistration> {
    tool("probe", move |_, api, cx| {
        let (sink, child) = (Arc::clone(&sink), child.clone());
        async move {
            let push = |value: JsonValue| lock(&sink).push(value);
            push(to_json(&api.env().map(|env| env.cwd().to_owned()))?);
            let names: Vec<String> = api
                .agent(&cx)
                .await?
                .tools
                .iter()
                .map(|each| each.name.clone())
                .collect();
            push(to_json(&names)?);
            push(JsonValue::Bool(
                api.registry().extension("tool:probe").is_some(),
            ));
            let (conversation, call_id) = (api.conversation_id(), api.call_id().to_owned());
            let entry = api
                .commit(
                    move |tx| async move {
                        // The next call runs in the new directory: its environment is built when it executes.
                        configure(
                            &tx,
                            conversation,
                            &AgentChange {
                                cwd: FieldChange::Set("/".to_owned()),
                                ..AgentChange::default()
                            },
                        )
                        .await?;
                        tx.append_entry(
                            conversation,
                            EntryDraft {
                                data: Some(JsonValue::from(call_id)),
                                ..EntryDraft::new("test.note")
                            },
                        )
                        .await
                    },
                    &cx,
                )
                .await?;
            push(JsonValue::Bool(entry.by_task_id == Some(api.task_id())));
            push(api.memo_or_store("m", json("1"), &cx).await?);
            push(api.memo_or_store("m", json("2"), &cx).await?);
            let options = InvocationTaskOptions {
                ownership: TaskOwnership::Conversation,
                background: None,
            };
            let id = api
                .create_task(&child, &json(r#"{"n":21}"#), options, &cx)
                .await?;
            let done = api.wait_for_task(id, &cx).await?;
            push(to_json(&done.outcome)?);
            Ok(empty_content())
        }
    })
}

#[tokio::test]
async fn builds_the_environment_per_call_from_the_conversations_cwd_and_runs_commits_memos_and_child_tasks(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let child = child_task();
    add_task(&setup.registry, child.erase(), None).unwrap();
    let seen: Arc<Mutex<Vec<JsonValue>>> = Arc::default();
    add_tool(&setup.registry, probe_tool(child, Arc::clone(&seen)), None).unwrap();
    setup.faux.set_responses(vec![
        calls(&[
            ("probe", serde_json::json!({}), "c1"),
            ("probe", serde_json::json!({}), "c2"),
        ])
        .into(),
        done().into(),
    ]);
    setup
        .settings
        .update(|settings| settings.tool_execution = Some(ToolExecutionMode::Sequential));
    let targets: Targets = Arc::default();
    let recorded = Arc::clone(&targets);
    let env: EnvFactory = Arc::new(move |target: EnvTarget, _| {
        lock(&recorded).push((target.conversation_id, target.cwd.clone()));
        let env: Arc<dyn ExecutionEnv> =
            Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                cwd: target.cwd.unwrap_or_else(|| "/tmp".to_owned()),
                ..NativeExecutionEnvOptions::default()
            }));
        futures::future::ready(Ok(Some(env))).boxed()
    });
    let OpenChat { harness, root } = open_chat(
        Arc::new(MemoryStorage::new()),
        &setup,
        Some(ChatEnv::Factory(env)),
    )
    .await
    .unwrap();
    root.configure(
        AgentChange {
            cwd: FieldChange::Set("/tmp".to_owned()),
            ..AgentChange::default()
        },
        context(),
    )
    .await
    .unwrap();
    root.submit(InputSubmissionDraft::new("go"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    let call = |cwd: &str| {
        format!(r#""{cwd}",["probe"],true,true,1,1,{{"status":"completed","result":42}}"#)
    };
    assert_eq!(
        JsonValue::Array(lock(&seen).clone().into()),
        json(&format!("[{},{}]", call("/tmp"), call("/")))
    );
    let targets = lock(&targets).clone();
    assert!(targets.contains(&(root.id(), Some("/tmp".to_owned()))));
    assert!(targets.contains(&(root.id(), Some("/".to_owned()))));
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn answers_a_throwing_environment_with_a_tool_error_result_and_reports_it_once_while_preparing(
) {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    add_tool(
        &setup.registry,
        tool("probe", |_, _, _| async {
            Ok(ToolExecutionResult {
                content: Some(vec![UserContentBlock::Text(TextContent::new("ran"))]),
                ..ToolExecutionResult::default()
            })
        }),
        None,
    )
    .unwrap();
    let env: EnvFactory =
        Arc::new(|_, _| futures::future::ready(Err(SessionError::error("no sandbox"))).boxed());
    let ran = run_with(
        &setup,
        vec![
            calls(&[("probe", serde_json::json!({}), "c1")]).into(),
            done().into(),
        ],
        None,
        Some(ChatEnv::Factory(env)),
    )
    .await;
    let result = &results(&ran.entries)[0];
    assert!(result.is_error);
    assert_eq!(
        result_text(result),
        "<harness>\n[error] no sandbox\n</harness>"
    );
    // Each preparation reports the failure and renders without an environment.
    assert_eq!(
        setup
            .reports()
            .iter()
            .filter(|error| error.to_string() == "no sandbox")
            .count(),
        2
    );
    ran.harness.close(context()).await.unwrap();
}
