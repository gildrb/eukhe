//! The goal extension on a real Harness with faux models: goal
//! continuation and completion, durable counters across a reopen, the
//! autonomous limits and gates, the no-progress cap, the budget steer, and
//! aborts.

use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::{ASSISTANT_ENTRY, USER_ENTRY};
use eukhe_durable::env::{NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{
    AgentChange, ConversationAbortOptions, Extension, FieldChange, HarnessOptions,
    InputSubmissionDraft, ModelRef, ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use eukhe_durable::storage::jsonl::{JsonlStorage, JsonlStorageOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{EntryRecord, Storage};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::typebox::{TSchema, Type};
use eukhe_types::pi_ai::{
    AssistantMessage, JsonObject, Message, StopReason, UserContent, UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::{json, Value};
use tokio::sync::watch;

use super::docs::{read_doc, AUTONOMOUS_DOC, GOAL_DOC};
use super::ops::{is_goal_nudge, user_text};
use super::{
    goal_state, goals_extension, set_autonomous, start_goal, watch_goal_updates, AutonomousChange,
    AutonomousStop,
};
use crate::autonomous::{
    is_autonomous_continuation, AgentAutonomousConfig, AgentAutonomousGateConfig,
    ChildProcessResult, GateCommandRunner,
};
use crate::durable::entries::{CustomEntryData, CUSTOM_ENTRY};
use crate::durable::{HarnessCell, HostCall, HostRequestRegistry};
use crate::goals::{GoalState, GoalStatus};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// Gate runs scripted in order; the workspace snapshot is unavailable, so a
/// failed gate always re-runs.
#[derive(Default)]
struct ScriptedGates {
    results: Mutex<Vec<ChildProcessResult>>,
    commands: Mutex<Vec<String>>,
}

impl GateCommandRunner for ScriptedGates {
    fn run_gate(
        &self,
        command: &str,
        _timeout_ms: u64,
    ) -> Pin<Box<dyn Future<Output = anyhow::Result<ChildProcessResult>> + Send + '_>> {
        self.commands
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(command.to_owned());
        let mut results = self.results.lock().unwrap_or_else(PoisonError::into_inner);
        let result = if results.is_empty() {
            Err(anyhow::anyhow!("no scripted gate result"))
        } else {
            Ok(results.remove(0))
        };
        Box::pin(async move { result })
    }
}

/// Models, registry, and host services that survive a close/reopen.
struct Setup {
    faux: FauxProviderHandle,
    models: Models,
    registry: Registry,
    cell: HarnessCell,
    requests: HostRequestRegistry,
    gates: Arc<ScriptedGates>,
}

fn setup() -> Setup {
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let registry = create_registry();
    let cell = HarnessCell::default();
    let requests = HostRequestRegistry::default();
    let gates = Arc::new(ScriptedGates::default());
    registry
        .install(goals_extension(
            cell.clone(),
            Arc::clone(&gates) as Arc<dyn GateCommandRunner>,
            &requests,
        ))
        .expect("the goal extension installs");
    registry
        .install(finish_extension(requests.clone()))
        .expect("the test tool installs");
    Setup {
        faux,
        models,
        registry,
        cell,
        requests,
        gates,
    }
}

/// A `finish` tool that runs the kernel's `await goal.complete()` through
/// the registered host request.
fn finish_extension(requests: HostRequestRegistry) -> Arc<Extension> {
    let schema: TSchema = Type::object(Vec::<(String, TSchema)>::new());
    let tool = define_tool(ToolRegistration::new(
        "finish",
        "finish tool",
        schema,
        move |_, api, _| {
            let handler = requests
                .get("goal.complete")
                .expect("goal.complete is registered");
            async move {
                let response = handler(HostCall {
                    data: json!({ "type": "goal.complete" }),
                    cell_source_code: None,
                    call: Some(api),
                })
                .await
                .map_err(|error| eukhe_durable::session::SessionError::error(error.to_string()))?;
                Ok(ToolExecutionResult {
                    output: Some(vec![UserContentBlock::Text(
                        eukhe_types::pi_ai::TextContent::new(response.to_string()),
                    )]),
                    ..ToolExecutionResult::default()
                })
            }
        },
    ));
    define_extension(Extension {
        name: "test.finish".to_owned(),
        tools: vec![tool],
        ..Extension::default()
    })
}

impl Setup {
    async fn open(&self, storage: Arc<dyn Storage>) -> (Harness, Conversation) {
        let options = HarnessOptions::new(self.models.clone(), Arc::new(self.registry.clone()));
        let harness = Harness::open(storage, options, cx())
            .await
            .expect("the Harness opens");
        let root = harness
            .root(
                RootOptions {
                    agent: Some(AgentChange {
                        model: FieldChange::Set(ModelRef {
                            provider: "faux".to_owned(),
                            model_id: "faux-1".to_owned(),
                        }),
                        ..AgentChange::default()
                    }),
                    ..RootOptions::default()
                },
                cx(),
            )
            .await
            .expect("the root opens");
        self.cell.set(harness.clone(), root.clone());
        (harness, root)
    }

    async fn host_request(&self, request_type: &str, data: Value) -> anyhow::Result<Value> {
        let handler = self
            .requests
            .get(request_type)
            .expect("the request type is registered");
        handler(HostCall {
            data,
            cell_source_code: None,
            call: None,
        })
        .await
    }
}

fn answer(text: &str) -> FauxResponseStep {
    faux_assistant_message(text, FauxAssistantMessageOptions::default()).into()
}

fn answer_at(text: &str, timestamp: u64) -> FauxResponseStep {
    let mut message: AssistantMessage =
        faux_assistant_message(text, FauxAssistantMessageOptions::default());
    message.timestamp = timestamp;
    message.into()
}

fn finish_call() -> FauxResponseStep {
    faux_assistant_message(
        faux_tool_call("finish", JsonObject::new(), Some("call-finish".to_owned())),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

/// A response that never arrives; resolves `reached` once requested.
fn blocked() -> (FauxResponseStep, watch::Receiver<bool>) {
    let (reached, receiver) = watch::channel(false);
    let step = FauxResponseStep::Factory(Arc::new(move |_, options, _, _| {
        reached.send_replace(true);
        let signal = options.and_then(|options| options.stream.request.signal.clone());
        let pending: BoxFuture<'static, _> = async move {
            match signal {
                Some(signal) => Err(signal.cancelled().await),
                None => futures::future::pending().await,
            }
        }
        .boxed();
        pending
    }));
    (step, receiver)
}

async fn submit(root: &Conversation, text: &str) {
    let handle = root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text(text.to_owned()),
                when_busy: None,
            },
            cx(),
        )
        .await
        .expect("the input is admitted");
    handle.wait(cx()).await.expect("the input settles");
}

/// Entries oldest first.
async fn entries(conversation: &Conversation) -> Vec<EntryRecord> {
    let page = conversation
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .expect("entries read");
    page.items.into_iter().rev().collect()
}

fn user_texts(entries: &[EntryRecord]) -> Vec<String> {
    entries
        .iter()
        .filter(|entry| entry.kind == USER_ENTRY.kind())
        .filter_map(|entry| match entry.model.as_ref()?.first()? {
            Message::User(message) => Some(user_text(&message.content)),
            _ => None,
        })
        .collect()
}

fn assistants(entries: &[EntryRecord]) -> Vec<AssistantMessage> {
    entries
        .iter()
        .filter(|entry| entry.kind == ASSISTANT_ENTRY.kind())
        .filter_map(|entry| match entry.model.as_ref()?.first()? {
            Message::Assistant(message) => Some(message.clone()),
            _ => None,
        })
        .collect()
}

fn goal_contexts(entries: &[EntryRecord]) -> Vec<(CustomEntryData, bool)> {
    entries
        .iter()
        .filter(|entry| entry.kind == CUSTOM_ENTRY.kind())
        .filter_map(|entry| {
            let data: CustomEntryData =
                serde_json::from_value(serde_json::to_value(entry.data.as_ref()?).ok()?).ok()?;
            (data.custom_type == "goal_context").then_some((data, entry.model.is_some()))
        })
        .collect()
}

async fn stored_goal(harness: &Harness, root: &Conversation) -> GoalState {
    read_doc(harness, &GOAL_DOC, root.id(), cx())
        .await
        .expect("the goal reads")
        .expect("the goal exists")
}

#[tokio::test]
async fn a_goal_continues_with_its_context_until_completed() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let created = setup
        .host_request(
            "goal.create",
            json!({ "type": "goal.create", "objective": "ship it", "token_budget": 1_000_000 }),
        )
        .await
        .expect("goal.create succeeds");
    assert_eq!(created["goal"]["objective"], "ship it");
    assert_eq!(created["goal"]["status"], "active");
    setup.faux.set_responses(vec![
        answer("step one"),
        answer("step two"),
        finish_call(),
        answer("done"),
    ]);

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let entries = entries(&root).await;
    let texts = user_texts(&entries);
    assert_eq!(texts.len(), 3, "{texts:?}");
    assert_eq!(texts[0], "work");
    assert!(texts[1]
        .starts_with("[goal: continuation]\n\nContinue working toward the active thread goal."));
    assert!(texts[1].contains("<objective>\nship it\n</objective>"));
    assert!(texts[2].starts_with("[goal: continuation]"));
    assert!(texts[1..].iter().all(|text| is_goal_nudge(text)));
    assert!(!is_goal_nudge("work"));
    // One display row per continuation, never in model context.
    let contexts = goal_contexts(&entries);
    assert_eq!(contexts.len(), 2);
    assert!(contexts
        .iter()
        .all(|(data, in_model)| !in_model && data.display));
    assert_eq!(
        contexts[1]
            .0
            .details
            .as_ref()
            .map(|details| details["continuationsUsed"].clone()),
        Some(json!(2))
    );
    let goal = stored_goal(&harness, &root).await;
    assert_eq!(goal.status, GoalStatus::Complete);
    assert!(!goal.active);
    assert_eq!(goal.continuations_used, 2);
    assert_eq!(goal.last_reason.as_deref(), Some("Goal achieved"));
    // Every response while the goal was active spent its budget; the final
    // "done" came after the completion.
    let answers = assistants(&entries);
    let spent: u64 = answers[..answers.len() - 1]
        .iter()
        .map(|message| message.usage.input + message.usage.output)
        .sum();
    assert_eq!(goal.tokens_used, spent);
    assert_eq!(setup.faux.get_pending_response_count(), 0);

    let got = setup
        .host_request("goal.get", json!({ "type": "goal.get" }))
        .await
        .expect("goal.get succeeds");
    assert_eq!(got["goal"]["status"], "complete");
    let error = setup
        .host_request("goal.create", json!({ "objective": 3 }))
        .await
        .expect_err("a non-string objective fails");
    assert_eq!(error.to_string(), "goal.create objective must be a string");
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn goal_create_refuses_while_a_goal_is_active_and_complete_needs_a_goal() {
    let setup = setup();
    let (harness, _root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let error = setup
        .host_request("goal.complete", json!({}))
        .await
        .expect_err("no goal to complete");
    assert_eq!(
        error.to_string(),
        "cannot complete goal because this thread has no goal"
    );
    setup
        .host_request("goal.create", json!({ "objective": "one" }))
        .await
        .expect("goal.create succeeds");
    let error = setup
        .host_request("goal.create", json!({ "objective": "two" }))
        .await
        .expect_err("an active goal refuses");
    assert!(error
        .to_string()
        .starts_with("cannot create a new goal because this thread already has an active goal"));
    let error = setup
        .host_request(
            "goal.create",
            json!({ "objective": "x", "token_budget": "lots" }),
        )
        .await
        .expect_err("a bad budget fails");
    assert_eq!(
        error.to_string(),
        "goal.create token_budget must be an integer when provided"
    );
    let completed = setup
        .host_request("goal.complete", json!({}))
        .await
        .expect("goal.complete succeeds");
    assert_eq!(completed["goal"]["status"], "complete");
    harness.close(cx()).await.expect("close");
}

async fn open_jsonl(dir: &std::path::Path) -> Arc<dyn Storage> {
    let fs = Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: dir.to_string_lossy().into_owned(),
        ..NativeExecutionEnvOptions::default()
    }));
    Arc::new(
        JsonlStorage::open(
            &dir.join("session").to_string_lossy(),
            fs,
            cx(),
            JsonlStorageOptions { fsync: true },
        )
        .await
        .expect("the JSONL storage opens"),
    )
}

#[tokio::test]
async fn goal_counters_survive_a_reopen_mid_continuation() {
    let dir = tempfile::tempdir().expect("tempdir");
    let setup = setup();
    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    setup
        .host_request("goal.create", json!({ "objective": "persist" }))
        .await
        .expect("goal.create succeeds");
    let (stuck, mut reached) = blocked();
    setup.faux.set_responses(vec![answer("first"), stuck]);
    root.submit(
        InputSubmissionDraft {
            request_id: Some("work".to_owned()),
            content: UserContent::Text("work".to_owned()),
            when_busy: None,
        },
        cx(),
    )
    .await
    .expect("admitted");
    reached
        .wait_for(|reached| *reached)
        .await
        .expect("the continuation's request is sent");
    let before = stored_goal(&harness, &root).await;
    assert_eq!(before.continuations_used, 1);
    assert!(before.tokens_used > 0);
    // A crash mid-continuation: the Harness closes with the run in flight.
    harness.close(cx()).await.expect("close");
    setup.cell.clear();

    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    let reopened = stored_goal(&harness, &root).await;
    assert_eq!(reopened.goal_id, before.goal_id);
    assert_eq!(reopened.continuations_used, 1);
    assert_eq!(reopened.tokens_used, before.tokens_used);
    assert_eq!(reopened.created_at, before.created_at);
    setup
        .faux
        .set_responses(vec![answer("second"), finish_call(), answer("done")]);
    harness.resume().expect("resume");
    harness.wait_for_idle(cx()).await.expect("idle");
    let goal = stored_goal(&harness, &root).await;
    assert_eq!(goal.status, GoalStatus::Complete);
    // The resumed run minted exactly one more continuation.
    assert_eq!(goal.continuations_used, 2);
    let texts = user_texts(&entries(&root).await);
    assert_eq!(texts.len(), 3, "{texts:?}");
    assert_eq!(texts[0], "work");
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn no_continuation_after_an_abort() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .host_request("goal.create", json!({ "objective": "keep going" }))
        .await
        .expect("goal.create succeeds");
    set_autonomous(
        &harness,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig::default()),
        cx(),
    )
    .await
    .expect("autonomous on");
    let (stuck, mut reached) = blocked();
    setup.faux.set_responses(vec![stuck, answer("unused")]);
    root.submit(
        InputSubmissionDraft {
            request_id: None,
            content: UserContent::Text("work".to_owned()),
            when_busy: None,
        },
        cx(),
    )
    .await
    .expect("admitted");
    reached
        .wait_for(|reached| *reached)
        .await
        .expect("requested");
    root.abort(ConversationAbortOptions::default(), cx())
        .await
        .expect("abort");
    harness.wait_for_idle(cx()).await.expect("idle");

    let entries = entries(&root).await;
    assert_eq!(user_texts(&entries), vec!["work".to_owned()]);
    assert!(goal_contexts(&entries).is_empty());
    let goal = stored_goal(&harness, &root).await;
    // An abort keeps the goal and charges nothing.
    assert_eq!(goal.status, GoalStatus::Active);
    assert_eq!(goal.continuations_used, 0);
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    let autonomous = read_doc(&harness, &AUTONOMOUS_DOC, root.id(), cx())
        .await
        .expect("read")
        .expect("exists");
    assert_eq!(autonomous.continuations_used, 0);
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn autonomous_runs_continue_until_their_continuation_limit() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let status = set_autonomous(
        &harness,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig {
            max_continuations: Some(2),
            ..AgentAutonomousConfig::default()
        }),
        cx(),
    )
    .await
    .expect("autonomous on");
    assert!(status.enabled);
    assert_eq!(status.limits.max_continuations, 2);
    setup.faux.set_responses(vec![
        answer("a"),
        answer("b"),
        answer("c"),
        answer("unused"),
    ]);

    submit(&root, "go").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let entries = entries(&root).await;
    let texts = user_texts(&entries);
    assert_eq!(texts.len(), 3, "{texts:?}");
    assert!(texts[1..]
        .iter()
        .all(|text| is_autonomous_continuation(text)));
    assert!(texts[1].starts_with("[autonomous-continuation]\n\nNo human input is available"));
    let state = read_doc(&harness, &AUTONOMOUS_DOC, root.id(), cx())
        .await
        .expect("read")
        .expect("exists");
    assert_eq!(state.continuations_used, 2);
    assert_eq!(state.turns_used, 3);
    let spent: u64 = assistants(&entries)
        .iter()
        .map(|message| message.usage.input + message.usage.output + message.usage.cache_write)
        .sum();
    assert_eq!(state.tokens_used, spent);
    assert_eq!(state.last_stop, Some(AutonomousStop::MaxContinuations));
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    // The `/autonomous` row.
    let rows: Vec<_> = entries
        .iter()
        .filter(|entry| entry.kind == CUSTOM_ENTRY.kind())
        .collect();
    assert_eq!(rows.len(), 1);
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn autonomous_gates_continue_on_failure_and_stop_on_pass() {
    let setup = setup();
    *setup
        .gates
        .results
        .lock()
        .unwrap_or_else(PoisonError::into_inner) = vec![
        ChildProcessResult {
            status: Some(1),
            stdout: "1 failed".to_owned(),
            ..ChildProcessResult::default()
        },
        ChildProcessResult {
            status: Some(0),
            ..ChildProcessResult::default()
        },
    ];
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    set_autonomous(
        &harness,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig {
            gates: Some(AgentAutonomousGateConfig {
                commands: Some(vec!["make test".to_owned()]),
                ..AgentAutonomousGateConfig::default()
            }),
            ..AgentAutonomousConfig::default()
        }),
        cx(),
    )
    .await
    .expect("autonomous on");
    setup
        .faux
        .set_responses(vec![answer("try"), answer("fixed"), answer("unused")]);

    submit(&root, "go").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let texts = user_texts(&entries(&root).await);
    assert_eq!(texts.len(), 2, "{texts:?}");
    assert!(texts[1].starts_with(
        "[autonomous-continuation: gate-failed]\n\nAutonomous quality gate failed (attempt 1/3): `make test`"
    ));
    assert_eq!(
        *setup
            .gates
            .commands
            .lock()
            .unwrap_or_else(PoisonError::into_inner),
        vec!["make test".to_owned(), "make test".to_owned()]
    );
    let state = read_doc(&harness, &AUTONOMOUS_DOC, root.id(), cx())
        .await
        .expect("read")
        .expect("exists");
    assert_eq!(state.last_stop, Some(AutonomousStop::GatePassed));
    assert_eq!(state.continuations_used, 1);
    harness.close(cx()).await.expect("close");
}

#[tokio::test(start_paused = true)]
async fn empty_answers_back_off_and_hit_the_no_progress_cap() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .host_request("goal.create", json!({ "objective": "make progress" }))
        .await
        .expect("goal.create succeeds");
    let created_at = stored_goal(&harness, &root)
        .await
        .created_at
        .expect("created_at");
    setup.faux.set_responses(vec![
        answer_at("", created_at + 1_000),
        answer_at("", created_at + 2_000),
        answer_at("", created_at + 3_000),
        answer("unused"),
    ]);

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let goal = stored_goal(&harness, &root).await;
    assert_eq!(goal.status, GoalStatus::Error);
    assert_eq!(goal.no_progress_streak, Some(3));
    assert_eq!(
        goal.last_error.as_deref(),
        Some("Goal continuation cap reached: consecutive turns made no progress")
    );
    // Two strikes waited out their backoff and continued; the third capped.
    assert_eq!(goal.continuations_used, 2);
    assert_eq!(user_texts(&entries(&root).await).len(), 3);
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn a_budget_crossing_steers_the_budget_limit_context() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .host_request(
            "goal.create",
            json!({ "objective": "small", "token_budget": 1 }),
        )
        .await
        .expect("goal.create succeeds");
    setup.faux.set_responses(vec![
        answer("spent"),
        answer("wrapping up"),
        answer("unused"),
    ]);

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let entries = entries(&root).await;
    let texts = user_texts(&entries);
    assert_eq!(texts.len(), 2, "{texts:?}");
    assert!(texts[1].starts_with(
        "[goal: budget-limit]\n\nThe active thread goal has reached its token budget."
    ));
    let goal = stored_goal(&harness, &root).await;
    assert_eq!(goal.status, GoalStatus::BudgetLimited);
    assert_eq!(
        goal.last_reason.as_deref(),
        Some("Reached 1 token goal budget")
    );
    let first = &assistants(&entries)[0];
    assert_eq!(goal.tokens_used, first.usage.input + first.usage.output);
    assert_eq!(goal_contexts(&entries).len(), 1);
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn goal_updates_emit_changes_and_start_submits_the_first_context() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let mut updates = watch_goal_updates(&harness, root.id(), cx()).expect("watch");
    let initial = updates.next().await.expect("initial");
    assert_eq!(initial.status, GoalStatus::Idle);
    setup
        .faux
        .set_responses(vec![finish_call(), answer("done")]);
    let started = start_goal(&harness, root.id(), "from the user", None, cx())
        .await
        .expect("start");
    assert_eq!(started.status, GoalStatus::Active);
    let update = updates.next().await.expect("started update");
    assert_eq!(update.goal_id, started.goal_id);
    harness.wait_for_idle(cx()).await.expect("idle");
    let texts = user_texts(&entries(&root).await);
    assert_eq!(texts.len(), 1);
    assert!(texts[0].starts_with("[goal: continuation]"));
    let goal = goal_state(&harness, root.id(), cx()).await.expect("goal");
    assert_eq!(goal.status, GoalStatus::Complete);
    let mut last = update;
    while last.status != GoalStatus::Complete {
        last = updates.next().await.expect("update");
    }
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn a_run_that_ends_in_a_provider_failure_fails_the_goal() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .host_request("goal.create", json!({ "objective": "fragile" }))
        .await
        .expect("goal.create succeeds");
    // The faux provider replays the message's build-time timestamp; a real
    // provider stamps it at request time, after the goal's write. Stamp it
    // so: in the same millisecond as goal.create, the failure would read
    // as settled before the goal's last write and fail nothing.
    let created_at = stored_goal(&harness, &root)
        .await
        .updated_at
        .expect("goal stamped");
    let mut failure: AssistantMessage = faux_assistant_message(
        "",
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Error),
            timestamp: Some(created_at + 1),
            ..FauxAssistantMessageOptions::default()
        },
    );
    failure.error_message = Some("provider exploded".to_owned());
    setup
        .faux
        .set_responses(vec![failure.into(), answer("recovered"), answer("unused")]);

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");
    // The failed run never reached a final answer: no continuation.
    assert_eq!(user_texts(&entries(&root).await), vec!["work".to_owned()]);

    // The next run of the conversation settles the failed one.
    submit(&root, "again").await;
    harness.wait_for_idle(cx()).await.expect("idle");
    let goal = stored_goal(&harness, &root).await;
    assert_eq!(goal.status, GoalStatus::Error);
    assert_eq!(goal.last_error.as_deref(), Some("provider exploded"));
    assert_eq!(goal.continuations_used, 0);
    assert_eq!(
        user_texts(&entries(&root).await),
        vec!["work".to_owned(), "again".to_owned()]
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn an_eukhe_session_installs_the_goal_hooks_and_host_requests() {
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    let cwd = dir.path().join("project");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&cwd).expect("cwd");
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let mut config = crate::durable::SessionConfig::new(
        &agent_dir,
        &cwd,
        "0192a000-0000-7000-8000-0000000000aa",
        crate::durable::SessionStorage::Memory,
    );
    config.models = Some(models);
    config.model = Some(
        ModelRef {
            provider: "faux".to_owned(),
            model_id: "faux-1".to_owned(),
        }
        .into(),
    );
    let session = crate::durable::open_session(config, cx())
        .await
        .expect("the session opens");
    let create = session
        .deps()
        .host_requests
        .get("goal.create")
        .expect("goal.create is registered");
    create(HostCall {
        data: json!({ "objective": "wrap up", "token_budget": 1 }),
        cell_source_code: None,
        call: None,
    })
    .await
    .expect("goal.create succeeds");
    faux.set_responses(vec![answer("spent"), answer("wrapping up")]);

    submit(session.root(), "work").await;
    session.harness().wait_for_idle(cx()).await.expect("idle");

    let texts = user_texts(&entries(session.root()).await);
    assert_eq!(texts.len(), 2, "{texts:?}");
    assert!(texts[1].starts_with("[goal: budget-limit]"));
    let goal = goal_state(session.harness(), session.root().id(), cx())
        .await
        .expect("goal");
    assert_eq!(goal.status, GoalStatus::BudgetLimited);
    session.close(cx()).await.expect("close");
}
