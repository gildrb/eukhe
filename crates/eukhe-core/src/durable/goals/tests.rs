//! The goal extension on a real Harness with faux models: goal
//! continuation and completion, durable counters across a reopen, the
//! autonomous limits and gates, the goal failure at empty replies, the
//! goal's and the autonomous run's own limits, the session's budget, and
//! aborts.

use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_ai::typebox::{TSchema, Type};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::entries::{ASSISTANT_ENTRY, USER_ENTRY};
use eukhe_durable::env::{NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{
    AgentChange, ConversationAbortOptions, Extension, FieldChange, HarnessOptions,
    InputSubmissionDraft, ModelRef, ToolExecutionResult, ToolRegistration, WhenBusy,
};
use eukhe_durable::harness::{
    Conversation, ConversationEntryQuery, Harness, RootOptions, SubmissionHandle,
};
use eukhe_durable::storage::jsonl::{JsonlStorage, JsonlStorageOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{EntryRecord, Storage, SubmissionStatus};
use eukhe_types::pi_ai::{
    AssistantMessage, JsonObject, Message, StopReason, ToolChoice, UserContent, UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::{json, Value};
use tokio::sync::watch;

use super::docs::{read_doc, AUTONOMOUS_DOC, GOAL_DOC};
use super::{
    goal_state, goals_extension, resume_goal, set_autonomous, start_goal, watch_goal_updates,
    AutonomousChange, AutonomousStop,
};
use crate::autonomous::{
    AgentAutonomousConfig, AgentAutonomousGateConfig, ChildProcessResult, GateCommandRunner,
};
use crate::durable::budget::{wrap_models_with_budget, BudgetGate};
use crate::durable::directors::{DirectorLimits, DIRECTOR_NOTICE_CUSTOM_TYPE};
use crate::durable::entries::{CustomEntryData, CUSTOM_ENTRY};
use crate::durable::{HarnessCell, HostCall, HostRequestRegistry};
use crate::goals::{GoalContextKind, GoalState, GoalStatus};
use eukhe_types::budget::{BudgetLimits, BudgetReport};
use eukhe_types::input_origin::{AutonomousNudge, InputOrigin};

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
pub(crate) struct Setup {
    pub(crate) faux: FauxProviderHandle,
    models: Models,
    registry: Registry,
    pub(crate) cell: HarnessCell,
    requests: HostRequestRegistry,
    gates: Arc<ScriptedGates>,
    /// The Director stack's limits each step reads.
    pub(crate) limits: Arc<Mutex<DirectorLimits>>,
    /// The session's budget: every model request passes it (none until a
    /// test gives the session a budget).
    pub(crate) budget: Arc<BudgetGate>,
    /// The agent directory of the budget's ledger.
    _agent_dir: tempfile::TempDir,
}

pub(crate) fn setup() -> Setup {
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let agent_dir = tempfile::tempdir().expect("tempdir");
    let budget = BudgetGate::side(agent_dir.path(), "session");
    wrap_models_with_budget(&models, &budget);
    let registry = create_registry();
    let cell = HarnessCell::default();
    let requests = HostRequestRegistry::default();
    let gates = Arc::new(ScriptedGates::default());
    let limits = Arc::new(Mutex::new(DirectorLimits::default()));
    let read = Arc::clone(&limits);
    registry
        .install(goals_extension(
            cell.clone(),
            Arc::clone(&budget),
            Arc::clone(&gates) as Arc<dyn GateCommandRunner>,
            Arc::new(move || *read.lock().unwrap_or_else(PoisonError::into_inner)),
            &requests,
            Vec::new(),
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
        limits,
        budget,
        _agent_dir: agent_dir,
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
                    signal: None,
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
    pub(crate) async fn open(&self, storage: Arc<dyn Storage>) -> (Harness, Conversation) {
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

    pub(crate) async fn host_request(
        &self,
        request_type: &str,
        data: Value,
    ) -> anyhow::Result<Value> {
        let handler = self
            .requests
            .get(request_type)
            .expect("the request type is registered");
        handler(HostCall {
            data,
            cell_source_code: None,
            call: None,
            signal: None,
        })
        .await
    }

    /// The session budget's report.
    pub(crate) fn report(&self) -> Option<BudgetReport> {
        self.budget.report()
    }
}

pub(crate) fn answer(text: &str) -> FauxResponseStep {
    faux_assistant_message(text, FauxAssistantMessageOptions::default()).into()
}

fn answer_at(text: &str, timestamp: u64) -> FauxResponseStep {
    let mut message: AssistantMessage =
        faux_assistant_message(text, FauxAssistantMessageOptions::default());
    message.timestamp = timestamp;
    message.into()
}

pub(crate) fn finish_call() -> FauxResponseStep {
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

pub(crate) async fn submit(root: &Conversation, text: &str) {
    let handle = root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text(text.to_owned()),
                when_busy: None,
                origin: eukhe_types::input_origin::InputOrigin::User,
                entry: None,
            },
            cx(),
        )
        .await
        .expect("the input is admitted");
    handle.wait(cx()).await.expect("the input settles");
}

/// Entries oldest first.
pub(crate) async fn entries(conversation: &Conversation) -> Vec<EntryRecord> {
    let page = conversation
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .expect("entries read");
    page.items.into_iter().rev().collect()
}

/// The concatenated text blocks of user content.
fn user_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.as_str()),
                UserContentBlock::Image(_) => None,
            })
            .collect(),
    }
}

pub(crate) fn user_origins(entries: &[EntryRecord]) -> Vec<InputOrigin> {
    entries
        .iter()
        .filter_map(|entry| USER_ENTRY.narrow(entry.clone()).expect("pi.user data"))
        .map(|entry| entry.data().origin.clone())
        .collect()
}

pub(crate) fn user_texts(entries: &[EntryRecord]) -> Vec<String> {
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

pub(crate) async fn stored_goal(harness: &Harness, root: &Conversation) -> GoalState {
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
    let continuation = InputOrigin::Goal {
        context: GoalContextKind::Continuation,
    };
    assert_eq!(
        user_origins(&entries),
        vec![InputOrigin::User, continuation.clone(), continuation]
    );
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
    assert!(!goal.is_active());
    assert_eq!(goal.continuations_used, 2);
    assert_eq!(
        goal.last_reason.as_deref(),
        Some("Goal achieved (unverified: no acceptance checks)")
    );
    // The goal counts its own tokens (input and output of its responses);
    // its token budget puts nothing on the session's budget.
    assert!(goal.tokens_used > 0, "{goal:?}");
    assert_eq!(goal.token_budget, Some(1_000_000));
    assert_eq!(setup.report(), None);
    assert_eq!(setup.faux.get_pending_response_count(), 0);

    let got = setup
        .host_request("goal.get", json!({ "type": "goal.get" }))
        .await
        .expect("goal.get succeeds");
    assert_eq!(
        (
            &got["goal"]["status"],
            &got["goal"]["token_budget"],
            &got["goal"]["tokens_used"]
        ),
        (
            &json!("complete"),
            &json!(1_000_000),
            &json!(goal.tokens_used)
        )
    );
    let error = setup
        .host_request("goal.create", json!({ "objective": 3 }))
        .await
        .expect_err("a non-string objective fails");
    assert_eq!(error.to_string(), "goal.create objective must be a string");
    harness.close(cx()).await.expect("close");
}

/// Regression (audit H6): an active goal whose model only answered (no
/// tool call with a new result) got a continuation at every answer, up to
/// `directors.maxSteps` (200). Now the progress check counts the
/// continuations in a row with no new work: the model reads the count,
/// and at `directors.stallSteps` the goal pauses with the reason and a
/// display row tells the user why.
#[tokio::test]
async fn a_goal_without_progress_pauses_at_the_stall_cap() {
    let setup = setup();
    *setup.limits.lock().unwrap_or_else(PoisonError::into_inner) = DirectorLimits {
        stall_steps: 2,
        ..DirectorLimits::default()
    };
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .host_request("goal.create", json!({ "objective": "ship it" }))
        .await
        .expect("goal.create succeeds");
    setup
        .faux
        .set_responses((0..8).map(|_| answer("Waiting for the build.")).collect());

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    // The first answer starts the count, the second is 1 continuation
    // with no new work, the third reaches the cap of 2.
    assert_eq!(setup.faux.get_pending_response_count(), 5);
    let entries = entries(&root).await;
    let texts = user_texts(&entries);
    assert_eq!(texts.len(), 3, "{texts:?}");
    assert!(!texts[1].contains("[goal: no progress]"), "{}", texts[1]);
    assert!(texts[2].ends_with(
        "\n\n[goal: no progress] 1 goal continuations in a row made no tool call with a new result. Take one concrete step that changes something now. If something blocks you, say what it is and stop: after 2 continuations with no progress the goal pauses."
    ));
    let reason = "No progress: 2 goal continuations in a row made no tool call with a new result";
    let goal = stored_goal(&harness, &root).await;
    assert_eq!(
        (
            goal.status,
            goal.last_reason.clone(),
            goal.continuations_used
        ),
        (GoalStatus::Paused, Some(reason.to_owned()), 2)
    );
    let notices: Vec<CustomEntryData> = entries
        .into_iter()
        .filter_map(|entry| CUSTOM_ENTRY.narrow(entry).expect("eukhe.custom data"))
        .map(|entry| entry.data().clone())
        .filter(|data| data.custom_type == DIRECTOR_NOTICE_CUSTOM_TYPE)
        .collect();
    assert_eq!(
        notices,
        vec![CustomEntryData {
            custom_type: DIRECTOR_NOTICE_CUSTOM_TYPE.to_owned(),
            content: Some(UserContent::Text(format!(
                "The goal paused. {reason}. Change the plan or remove the blocker, then resume the goal."
            ))),
            display: true,
            details: Some(json!({ "goalId": goal.goal_id, "stalls": 2 })),
            input: false,
            origin: None,
        }]
    );
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
    // A refused goal puts nothing on the session's budget.
    let error = setup
        .host_request(
            "goal.create",
            json!({ "objective": "two", "token_budget": 5 }),
        )
        .await
        .expect_err("an active goal refuses");
    assert!(error
        .to_string()
        .starts_with("cannot create a new goal because this thread already has an active goal"));
    assert_eq!(setup.report(), None);
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

pub(crate) async fn open_jsonl(dir: &std::path::Path) -> Arc<dyn Storage> {
    let fs = Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: dir.to_string_lossy().into_owned(),
        ..NativeExecutionEnvOptions::default()
    }));
    Arc::new(
        JsonlStorage::open(
            &dir.join("session").to_string_lossy(),
            fs,
            cx(),
            JsonlStorageOptions {
                fsync: true,
                ..JsonlStorageOptions::default()
            },
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
            origin: eukhe_types::input_origin::InputOrigin::User,
            entry: None,
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
    // A crash mid-continuation: the Harness closes with the run in flight.
    harness.close(cx()).await.expect("close");
    setup.cell.clear();

    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    let reopened = stored_goal(&harness, &root).await;
    assert_eq!(reopened.goal_id, before.goal_id);
    assert_eq!(reopened.continuations_used, 1);
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
        &setup.budget,
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
            origin: eukhe_types::input_origin::InputOrigin::User,
            entry: None,
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
    assert_eq!(goal_contexts(&entries), []);
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

/// Regression: withdrawing queued goal contexts keeps the user's own words
/// even when they look like a goal context.
#[tokio::test]
async fn withdrawing_goal_contexts_keeps_user_words_shaped_like_one() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let (stuck, mut reached) = blocked();
    setup.faux.set_responses(vec![stuck]);
    let queue = |text: &str, origin: InputOrigin| InputSubmissionDraft {
        request_id: None,
        content: UserContent::Text(text.to_owned()),
        when_busy: Some(WhenBusy::FollowUp),
        origin,
        entry: None,
    };
    root.submit(queue("work", InputOrigin::User), cx())
        .await
        .expect("admitted");
    reached
        .wait_for(|reached| *reached)
        .await
        .expect("requested");
    let typed = root
        .submit(
            queue("[goal: continuation] keep going", InputOrigin::User),
            cx(),
        )
        .await
        .expect("queued");
    let nudge = root
        .submit(
            queue(
                "keep going",
                InputOrigin::Goal {
                    context: GoalContextKind::Continuation,
                },
            ),
            cx(),
        )
        .await
        .expect("queued");
    super::withdraw_queued_goal_contexts(&harness, root.id(), cx())
        .await
        .expect("withdrawn");
    let status = |handle: SubmissionHandle| async move {
        handle.status(cx()).await.expect("status").state.status()
    };
    assert_eq!(
        [status(typed).await, status(nudge).await],
        [SubmissionStatus::Queued, SubmissionStatus::Unanswered]
    );
    root.abort(ConversationAbortOptions::default(), cx())
        .await
        .expect("abort");
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn autonomous_runs_continue_until_their_continuation_limit() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let status = set_autonomous(
        &harness,
        &setup.budget,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig {
            max_continuations: Some(2),
            max_turns: Some(10),
            ..AgentAutonomousConfig::default()
        }),
        cx(),
    )
    .await
    .expect("autonomous on");
    assert!(status.enabled);
    assert_eq!(status.limits.max_continuations, 2);
    // The run's limits are its own: nothing goes on the session's budget.
    assert_eq!(status.limits.max_turns, 10);
    assert_eq!(status.budget, None);
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
    let continuation = InputOrigin::Autonomous {
        nudge: AutonomousNudge::Continuation,
    };
    assert_eq!(
        user_origins(&entries),
        vec![InputOrigin::User, continuation.clone(), continuation]
    );
    assert!(texts[1].starts_with("[autonomous-continuation]\n\nNo human input is available"));
    let state = read_doc(&harness, &AUTONOMOUS_DOC, root.id(), cx())
        .await
        .expect("read")
        .expect("exists");
    assert_eq!(state.continuations_used, 2);
    assert_eq!(state.last_stop, Some(AutonomousStop::MaxContinuations));
    // The run counted its three turns; the session has no budget.
    assert_eq!(state.turns_used, 3);
    assert!(state.tokens_used > 0, "{state:?}");
    assert_eq!(setup.report(), None);
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    // The `/autonomous` row.
    let rows: Vec<_> = entries
        .iter()
        .filter(|entry| entry.kind == CUSTOM_ENTRY.kind())
        .collect();
    assert_eq!(rows.len(), 1);
    harness.close(cx()).await.expect("close");
}

/// What the faux provider saw of a request: whether it allowed tools, and
/// the text of its last message when that is a user message.
type Saw = Arc<Mutex<Vec<(bool, String)>>>;

/// A response that records what the request looked like, then answers
/// `text`.
fn seeing(seen: &Saw, text: &str) -> FauxResponseStep {
    let seen = Arc::clone(seen);
    let text = text.to_owned();
    FauxResponseStep::factory(move |context, options, _, _| {
        let tools = options.is_none_or(|options| options.tool_choice != Some(ToolChoice::None));
        let last = match context.messages().last() {
            Some(Message::User(message)) => user_text(&message.content),
            _ => String::new(),
        };
        seen.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push((tools, last));
        Ok(faux_assistant_message(
            text.as_str(),
            FauxAssistantMessageOptions::default(),
        ))
    })
}

/// A call of a tool that does not exist: the turn goes on with its error.
fn missing_tool_call() -> FauxResponseStep {
    faux_assistant_message(
        faux_tool_call("nope", JsonObject::new(), Some("call-nope".to_owned())),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

/// `--autonomous-max-turns 1` (the ACP `autonomous_limit` capture): the
/// prompt's one answer is the run's one turn, and the run stops at
/// `maxTurns` with no continuation and no other request. No side request
/// and no budget is involved: the run counts its own turns.
#[tokio::test]
async fn autonomous_max_turns_one_answers_once_and_stops() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    set_autonomous(
        &harness,
        &setup.budget,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig {
            max_turns: Some(1),
            ..AgentAutonomousConfig::default()
        }),
        cx(),
    )
    .await
    .expect("autonomous on");
    let seen = Saw::default();
    setup
        .faux
        .set_responses(vec![seeing(&seen, "a river essay"), answer("unused")]);

    submit(&root, "Write a 100-word essay about rivers.").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    assert_eq!(user_origins(&entries(&root).await), vec![InputOrigin::User]);
    let state = read_doc(&harness, &AUTONOMOUS_DOC, root.id(), cx())
        .await
        .expect("read")
        .expect("exists");
    assert_eq!(
        (state.turns_used, state.last_stop),
        (1, Some(AutonomousStop::MaxTurns))
    );
    assert_eq!(
        *seen.lock().unwrap_or_else(PoisonError::into_inner),
        vec![(true, "Write a 100-word essay about rivers.".to_owned())]
    );
    assert_eq!(setup.report(), None);
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(cx()).await.expect("close");
}

/// `maxTurns` is soft, as in v0.10.67: the run counts each settled
/// response of the agent, and checks the limit only between
/// continuations, so a turn that makes more requests than the limit runs
/// to its own final answer (with its tools), and the run then stops at
/// `maxTurns` with no continuation.
#[tokio::test]
async fn autonomous_max_turns_lets_the_turn_that_crosses_it_finish() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    set_autonomous(
        &harness,
        &setup.budget,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig {
            max_turns: Some(2),
            ..AgentAutonomousConfig::default()
        }),
        cx(),
    )
    .await
    .expect("autonomous on");
    let seen = Saw::default();
    setup.faux.set_responses(vec![
        missing_tool_call(),
        missing_tool_call(),
        seeing(&seen, "what is done"),
        answer("unused"),
    ]);

    submit(&root, "go").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    assert_eq!(user_origins(&entries(&root).await), vec![InputOrigin::User]);
    let state = read_doc(&harness, &AUTONOMOUS_DOC, root.id(), cx())
        .await
        .expect("read")
        .expect("exists");
    assert_eq!(
        (state.turns_used, state.last_stop),
        (3, Some(AutonomousStop::MaxTurns))
    );
    // The third request is the turn's own, with its tools and no notice.
    assert_eq!(
        *seen.lock().unwrap_or_else(PoisonError::into_inner),
        vec![(true, String::new())]
    );
    assert_eq!(setup.report(), None);
    assert_eq!(setup.faux.get_pending_response_count(), 1);
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
        &setup.budget,
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

/// An empty reply is no answer (LAWS.bend H4.7): the `EmptyStop` Director
/// retries it with a harness note under its cap (3 empty notes in a row,
/// law `stop_empty_three_notes_then_fails`: the first request and 3 noted retries) and
/// then fails the run with the model error, which fails the goal; it
/// never reaches the goal's continuation mint.
#[tokio::test(start_paused = true)]
async fn empty_replies_are_retried_and_then_fail_the_goal() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .host_request("goal.create", json!({ "objective": "make progress" }))
        .await
        .expect("goal.create succeeds");
    // Stamped after the goal's write, as a real provider stamps a reply.
    let updated_at = stored_goal(&harness, &root)
        .await
        .updated_at
        .expect("goal stamped");
    // Every request of the run gives no answer, so the run fails at its
    // last note; a run that answered would mint a goal continuation.
    let mut responses: Vec<FauxResponseStep> = (1..=4)
        .map(|request| answer_at("", updated_at + request * 1_000))
        .collect();
    responses.extend([answer("recovered"), answer("unused")]);
    setup.faux.set_responses(responses);

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");
    // The failed run never reached a final answer: no continuation.
    assert_eq!(user_texts(&entries(&root).await), vec!["work".to_owned()]);

    // The next run of the conversation settles the failed one.
    submit(&root, "again").await;
    harness.wait_for_idle(cx()).await.expect("idle");
    let goal = stored_goal(&harness, &root).await;
    assert_eq!(
        (
            goal.status,
            goal.last_error.as_deref(),
            goal.continuations_used
        ),
        (
            GoalStatus::Error,
            Some(
                "The model gave no answer: its reply (stop reason stop) has no text and no tool \
                 call, again after every empty note the harness sends in a row"
            ),
            0
        )
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(cx()).await.expect("close");
}

/// The goal's token budget is its own and soft (as v0.10.67): a final
/// answer that crosses it turns the goal `budget_limited` and steers the
/// run with the budget-limit context, which the model answers; then the
/// run ends (a budget-limited goal mints no continuation).
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

/// A goal that crosses its token budget in the middle of a turn (a
/// response with a tool call) is nudged, not cut: the budget-limit context
/// is steered into the run's next request, which keeps its tools, and the
/// run goes on to the model's own final answer. The goal's budget puts no
/// limit on the session's budget; a later run works as usual and
/// `/goal resume` keeps the goal limited.
#[tokio::test]
async fn a_goal_crossing_its_token_budget_mid_turn_is_nudged_and_the_run_goes_on() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .host_request(
            "goal.create",
            json!({ "objective": "small", "token_budget": 1 }),
        )
        .await
        .expect("goal.create succeeds");
    assert_eq!(setup.report(), None);
    let seen = Saw::default();
    setup.faux.set_responses(vec![
        missing_tool_call(),
        seeing(&seen, "what is done"),
        seeing(&seen, "a later answer"),
        answer("unused"),
    ]);

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    let goal = stored_goal(&harness, &root).await;
    assert_eq!(
        (
            goal.status,
            goal.last_reason.as_deref(),
            goal.last_error.as_deref()
        ),
        (
            GoalStatus::BudgetLimited,
            Some("Reached 1 token goal budget"),
            None
        )
    );
    let first = &assistants(&entries(&root).await)[0];
    assert_eq!(goal.tokens_used, first.usage.input + first.usage.output);
    assert_eq!(
        user_origins(&entries(&root).await),
        vec![
            InputOrigin::User,
            InputOrigin::Goal {
                context: GoalContextKind::BudgetLimit
            }
        ]
    );
    submit(&root, "again").await;
    harness.wait_for_idle(cx()).await.expect("idle");
    let seen = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    assert_eq!(seen.len(), 2, "{seen:?}");
    assert!(seen[0].0, "the nudged request keeps its tools");
    assert!(
        seen[0].1.starts_with(
            "[goal: budget-limit]\n\nThe active thread goal has reached its token budget."
        ),
        "{seen:?}"
    );
    assert_eq!(seen[1], (true, "again".to_owned()));
    let texts = user_texts(&entries(&root).await);
    assert_eq!(texts.len(), 3, "{texts:?}");
    let still = resume_goal(&harness, &setup.budget, root.id(), cx())
        .await
        .expect("resume");
    assert_eq!(
        (still.status, still.last_reason.as_deref()),
        (
            GoalStatus::BudgetLimited,
            Some("Goal token budget already reached")
        )
    );
    assert_eq!(setup.report(), None);
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(cx()).await.expect("close");
}

/// An active goal whose session budget ran short at a final answer turns
/// `budget_limited` and yields; `/goal resume` keeps it there until budget
/// is added, then it continues.
#[tokio::test]
async fn a_short_budget_limits_the_goal_until_budget_is_added() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .budget
        .set(BudgetLimits {
            requests: Some(2),
            ..BudgetLimits::default()
        })
        .expect("the budget is set");
    setup
        .host_request("goal.create", json!({ "objective": "two steps" }))
        .await
        .expect("goal.create succeeds");
    // The first answer continues the goal; the second request does not fit
    // as work and is the final answer.
    setup
        .faux
        .set_responses(vec![answer("a"), answer("b"), answer("unused")]);

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    assert_eq!(
        user_origins(&entries(&root).await),
        vec![
            InputOrigin::User,
            InputOrigin::Goal {
                context: GoalContextKind::Continuation,
            },
        ]
    );
    let limited = stored_goal(&harness, &root).await;
    assert_eq!(
        (limited.status, limited.last_reason.as_deref()),
        (
            GoalStatus::BudgetLimited,
            Some("Budget exhausted (requests): add budget (/budget add), then /goal resume")
        )
    );
    let still = resume_goal(&harness, &setup.budget, root.id(), cx())
        .await
        .expect("resume");
    assert_eq!(still.status, GoalStatus::BudgetLimited);

    setup
        .budget
        .add(eukhe_types::budget::BudgetAmounts {
            requests: 2,
            ..eukhe_types::budget::BudgetAmounts::default()
        })
        .expect("budget is added");
    setup
        .faux
        .set_responses(vec![finish_call(), answer("done")]);
    let resumed = resume_goal(&harness, &setup.budget, root.id(), cx())
        .await
        .expect("resume");
    assert_eq!(resumed.status, GoalStatus::Active);
    harness.wait_for_idle(cx()).await.expect("idle");
    assert_eq!(
        stored_goal(&harness, &root).await.status,
        GoalStatus::Complete
    );
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
        signal: None,
    })
    .await
    .expect("goal.create succeeds");
    // The goal's token budget is its own: the session has no budget. Its
    // first response reaches it; the budget-limit context is steered into
    // the run's next request, which keeps its tools.
    assert_eq!(session.budget().report(), None);
    let seen = Saw::default();
    faux.set_responses(vec![
        missing_tool_call(),
        seeing(&seen, "wrapping up"),
        answer("unused"),
    ]);

    submit(session.root(), "work").await;
    session.harness().wait_for_idle(cx()).await.expect("idle");

    let goal = goal_state(session.harness(), session.root().id(), cx())
        .await
        .expect("goal");
    assert_eq!(goal.status, GoalStatus::BudgetLimited);
    let texts = user_texts(&entries(session.root()).await);
    assert_eq!(texts.len(), 2, "{texts:?}");
    assert!(texts[1].starts_with("[goal: budget-limit]"));
    let seen = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    assert_eq!(seen.len(), 1, "{seen:?}");
    assert!(seen[0].0, "the nudged request keeps its tools");
    assert_eq!(seen[0].1, texts[1]);
    assert_eq!(faux.get_pending_response_count(), 1);
    session.close(cx()).await.expect("close");
}
