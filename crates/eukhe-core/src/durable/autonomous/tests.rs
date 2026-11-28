//! The autonomous extension on a real Harness with faux models: the
//! autonomous run (its checks, the session's budget as its only limit, and
//! the progress check that steers a stalled run once and then ends it not
//! done), aborts, the session's install, and old sessions that hold the
//! removed goal's records.

use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, FauxProviderHandle,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_ai::typebox::{TSchema, Type};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::documents::{DocDefinition, RewindableConversationDoc};
use eukhe_durable::entries::{ASSISTANT_ENTRY, USER_ENTRY};
use eukhe_durable::env::{NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{
    AgentChange, ConversationAbortOptions, ConversationCreateOptions, Extension, FieldChange,
    HarnessOptions, InputSubmissionDraft, ModelRef, ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use eukhe_durable::storage::jsonl::{JsonlStorage, JsonlStorageOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{ConversationOwnership, EntryRecord, RewindableFork, Storage};
use eukhe_types::pi_ai::{Message, UserContent, UserContentBlock};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use tokio::sync::watch;

use super::docs::{open_doc, read_doc, write_doc, AUTONOMOUS_DOC};
use super::{autonomous_extension, set_autonomous, AutonomousChange};
use crate::autonomous::{AgentAutonomousConfig, AutonomousStop};
use crate::durable::acceptance::{acceptance_state, answer_judge, set_acceptance, ACCEPTANCE_DOC};
use crate::durable::budget::{wrap_models_with_budget, BudgetGate, RunStart};
use crate::durable::directors::{
    director_state, DirectorLimits, DirectorState, Layer, DIRECTOR_NOTICE_CUSTOM_TYPE,
};
use crate::durable::entries::{CustomEntryData, CUSTOM_ENTRY};
use crate::durable::{HarnessCell, HostCall, HostRequestRegistry};
use eukhe_types::acceptance::CheckSpec;
use eukhe_types::budget::{BudgetLimits, BudgetReport, RunKind, RunLimits};
use eukhe_types::input_origin::{AutonomousNudge, GoalContextKind, InputOrigin};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// Models, registry, and host services that survive a close/reopen.
pub(crate) struct Setup {
    pub(crate) faux: FauxProviderHandle,
    models: Models,
    registry: Registry,
    pub(crate) cell: HarnessCell,
    requests: HostRequestRegistry,
    /// The Director stack's limits each step reads.
    pub(crate) limits: Arc<Mutex<DirectorLimits>>,
    /// The session's budget: every model request passes it (none until a
    /// test gives the session a budget).
    pub(crate) budget: Arc<BudgetGate>,
    /// The agent directory of the budget's ledger.
    _agent_dir: tempfile::TempDir,
    /// The session's working directory (the checks run there).
    cwd: tempfile::TempDir,
}

pub(crate) fn setup() -> Setup {
    setup_with(|_| Vec::new())
}

/// What a test installs after the autonomous extension sees: the
/// session's Harness cell, budget and the Director stack's limits.
pub(crate) struct Beside<'a> {
    pub(crate) cell: &'a HarnessCell,
    pub(crate) budget: &'a Arc<BudgetGate>,
    pub(crate) limits: Arc<dyn Fn() -> DirectorLimits + Send + Sync>,
}

/// [`setup`] with `beside`'s extensions installed after the autonomous
/// extension (whose `on_yield` runs the Director stack).
pub(crate) fn setup_with(beside: impl FnOnce(Beside<'_>) -> Vec<Arc<Extension>>) -> Setup {
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let agent_dir = tempfile::tempdir().expect("tempdir");
    let budget = BudgetGate::side(agent_dir.path(), "session");
    wrap_models_with_budget(&models, &budget);
    let registry = create_registry();
    let cell = HarnessCell::default();
    let requests = HostRequestRegistry::default();
    let limits = Arc::new(Mutex::new(DirectorLimits::default()));
    let read = Arc::clone(&limits);
    let limits_of: Arc<dyn Fn() -> DirectorLimits + Send + Sync> =
        Arc::new(move || *read.lock().unwrap_or_else(PoisonError::into_inner));
    let extensions = beside(Beside {
        cell: &cell,
        budget: &budget,
        limits: Arc::clone(&limits_of),
    });
    registry
        .install(autonomous_extension(
            cell.clone(),
            Arc::clone(&budget),
            limits_of,
            // A faux model takes no judge request: no verdict.
            answer_judge(cell.clone(), models.clone()),
            &requests,
            Vec::new(),
        ))
        .expect("the autonomous extension installs");
    for extension in extensions {
        registry
            .install(extension)
            .expect("the test extension installs");
    }
    registry
        .install(finish_extension())
        .expect("the test tool installs");
    Setup {
        faux,
        models,
        registry,
        cell,
        requests,
        limits,
        budget,
        _agent_dir: agent_dir,
        cwd: tempfile::tempdir().expect("tempdir"),
    }
}

/// A `finish` tool that answers `finished` (the forced-call tests force
/// it).
fn finish_extension() -> Arc<Extension> {
    let schema: TSchema = Type::object(Vec::<(String, TSchema)>::new());
    let tool = define_tool(ToolRegistration::new(
        "finish",
        "finish tool",
        schema,
        move |_, _, _| async move {
            Ok(ToolExecutionResult {
                output: Some(vec![UserContentBlock::Text(
                    eukhe_types::pi_ai::TextContent::new("finished"),
                )]),
                ..ToolExecutionResult::default()
            })
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

    /// The session's working directory.
    pub(crate) fn cwd(&self) -> &Path {
        self.cwd.path()
    }
}

pub(crate) fn answer(text: &str) -> FauxResponseStep {
    faux_assistant_message(text, FauxAssistantMessageOptions::default()).into()
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
    submit_as(root, text, InputOrigin::User).await;
}

/// Submit `text` with `origin` and wait until it settles.
async fn submit_as(root: &Conversation, text: &str, origin: InputOrigin) {
    let handle = root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text(text.to_owned()),
                when_busy: None,
                origin,
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

/// The display rows of the Director stack's notices.
fn director_notices(entries: Vec<EntryRecord>) -> Vec<CustomEntryData> {
    entries
        .into_iter()
        .filter_map(|entry| CUSTOM_ENTRY.narrow(entry).expect("eukhe.custom data"))
        .map(|entry| entry.data().clone())
        .filter(|data| data.custom_type == DIRECTOR_NOTICE_CUSTOM_TYPE)
        .collect()
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

/// Turn the autonomous run on as its principal, then clear its checks
/// (turning it on gives it the intent check): a run without checks.
pub(crate) async fn autonomous_unchecked(
    setup: &Setup,
    harness: &Harness,
    root: &Conversation,
    config: AgentAutonomousConfig,
) {
    set_autonomous(
        harness,
        &setup.budget,
        root.id(),
        AutonomousChange::On(config),
        setup.cwd(),
        cx(),
    )
    .await
    .expect("autonomous on");
    set_acceptance(harness, root.id(), Vec::new(), None, setup.cwd(), cx())
        .await
        .expect("the checks clear");
}

#[tokio::test]
async fn no_continuation_after_an_abort() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    autonomous_unchecked(&setup, &harness, &root, AgentAutonomousConfig::default()).await;
    let (stuck, mut reached) = blocked();
    setup.faux.set_responses(vec![stuck, answer("unused")]);
    root.submit(
        InputSubmissionDraft {
            request_id: None,
            content: UserContent::Text("work".to_owned()),
            when_busy: None,
            origin: InputOrigin::User,
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
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    let autonomous = read_doc(&harness, &AUTONOMOUS_DOC, root.id(), cx())
        .await
        .expect("read")
        .expect("exists");
    assert_eq!(autonomous.continuations_used, 0);
    harness.close(cx()).await.expect("close");
}

/// AU1, AU5: turning the run on gives it the intent check, and puts no
/// limit of its own anywhere: the session's budget stays as it was.
#[tokio::test]
async fn turning_an_autonomous_run_on_gives_it_the_intent_check() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    let status = set_autonomous(
        &harness,
        &setup.budget,
        root.id(),
        AutonomousChange::On(AgentAutonomousConfig::default()),
        setup.cwd(),
        cx(),
    )
    .await
    .expect("autonomous on");
    assert!(status.enabled);
    assert_eq!((status.budget, setup.report()), (None, None));
    let checks: Vec<CheckSpec> = acceptance_state(&harness, root.id(), cx())
        .await
        .expect("the checks read")
        .checks
        .into_iter()
        .map(|check| check.spec)
        .collect();
    assert_eq!(checks, vec![CheckSpec::intent()]);
    harness.close(cx()).await.expect("close");
}

/// AU3, AU4: an autonomous run without checks is continued with its
/// prompt at each final answer while the session's budget admits work,
/// and the budget stops it: the run counts no turn, token or
/// continuation limit of its own.
#[tokio::test]
async fn an_autonomous_run_without_checks_goes_on_until_its_budget_stops_it() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    setup
        .budget
        .set(BudgetLimits {
            requests: Some(3),
            ..BudgetLimits::default()
        })
        .expect("the budget is set");
    autonomous_unchecked(&setup, &harness, &root, AgentAutonomousConfig::default()).await;
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
    assert_eq!(
        (state.enabled, state.continuations_used, state.last_stop),
        (true, 2, Some(AutonomousStop::Budget))
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    // The `/auto` row.
    let rows = entries
        .iter()
        .filter(|entry| entry.kind == CUSTOM_ENTRY.kind())
        .count();
    assert_eq!(rows, 1);
    harness.close(cx()).await.expect("close");
}

/// AU5: the removed `maxTurns` (`--autonomous-max-turns`) is the
/// model-request limit of the run the principal starts next: the budget
/// stops the run at it, with the run's final answer from the reserve, and
/// no count of its own.
#[tokio::test]
async fn the_removed_max_turns_is_the_runs_request_limit() {
    let setup = setup();
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    autonomous_unchecked(
        &setup,
        &harness,
        &root,
        AgentAutonomousConfig {
            max_turns: Some(2),
            ..AgentAutonomousConfig::default()
        },
    )
    .await;
    // The session's input path starts the run (none runs in this harness).
    let started = setup
        .budget
        .start_run(RunStart {
            kind: RunKind::Interactive,
            set: RunLimits::default(),
            presets: Vec::new(),
            standing: None,
        })
        .expect("the run starts")
        .expect("a root session's run");
    assert_eq!(started.limits.requests, Some(2));
    setup
        .faux
        .set_responses(vec![answer("a"), answer("b"), answer("unused")]);

    submit(&root, "go").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    assert_eq!(
        user_origins(&entries(&root).await),
        vec![
            InputOrigin::User,
            InputOrigin::Autonomous {
                nudge: AutonomousNudge::Continuation,
            },
        ]
    );
    let state = read_doc(&harness, &AUTONOMOUS_DOC, root.id(), cx())
        .await
        .expect("read")
        .expect("exists");
    assert_eq!(
        (state.continuations_used, state.last_stop),
        (1, Some(AutonomousStop::Budget))
    );
    assert_eq!(setup.faux.get_pending_response_count(), 1);
    harness.close(cx()).await.expect("close");
}

/// Regression (audit H6, then F2, now on the autonomous run): a run whose
/// model only answered (no tool call with a new result) got a
/// continuation at every answer, and the goal's stall later paused it
/// until the user resumed it. Now the progress check counts the
/// autonomous continuations in a row with no new work: the model reads the
/// count; at `directors.stallSteps` the harness steers it once (change
/// approach) and the run goes on; at twice the cap the run ends not done,
/// with the reason as its last stop and a display row. Nothing waits for
/// the user.
#[tokio::test]
async fn a_stalled_autonomous_run_is_steered_once_then_ends_not_done() {
    let setup = setup();
    *setup.limits.lock().unwrap_or_else(PoisonError::into_inner) = DirectorLimits {
        stall_steps: 2,
        ..DirectorLimits::default()
    };
    let (harness, root) = setup.open(Arc::new(MemoryStorage::new())).await;
    autonomous_unchecked(&setup, &harness, &root, AgentAutonomousConfig::default()).await;
    setup
        .faux
        .set_responses((0..8).map(|_| answer("Waiting for the build.")).collect());

    submit(&root, "work").await;
    harness.wait_for_idle(cx()).await.expect("idle");

    // The first answer starts the count; the second is 1 continuation with
    // no new work, the third reaches the cap of 2 (the steer), the fourth
    // is 3, the fifth reaches twice the cap and ends the run.
    assert_eq!(setup.faux.get_pending_response_count(), 3);
    let entries = entries(&root).await;
    let texts = user_texts(&entries);
    assert_eq!(texts.len(), 5, "{texts:?}");
    assert!(!texts[1].contains("[autonomous: "), "{}", texts[1]);
    assert!(texts[2].ends_with(
        "\n\n[autonomous: no progress] 1 autonomous continuations in a row made no tool call with a new result. Take one concrete step that changes something now. At 4 in a row the run ends, not done."
    ), "{}", texts[2]);
    assert!(texts[3].ends_with(
        "\n\n[autonomous: change approach] 2 autonomous continuations in a row made no tool call with a new result: the current approach is not working. Change it: try another method, use a read-only helper to investigate, or re-plan the remaining work, then keep going. At 4 continuations in a row with no progress the run ends, not done."
    ), "{}", texts[3]);
    assert!(
        texts[4].contains("[autonomous: no progress] 3 autonomous continuations"),
        "{}",
        texts[4]
    );
    let state = read_doc(&harness, &AUTONOMOUS_DOC, root.id(), cx())
        .await
        .expect("read")
        .expect("exists");
    assert_eq!(
        (state.enabled, state.continuations_used, state.last_stop),
        (true, 4, Some(AutonomousStop::NoProgress { stalls: 4 }))
    );
    assert_eq!(
        AutonomousStop::NoProgress { stalls: 4 }.describe(None),
        "no progress: 4 autonomous continuations in a row made no tool call with a new result, also after the harness asked for another approach"
    );
    assert_eq!(
        director_notices(entries),
        vec![CustomEntryData {
            custom_type: DIRECTOR_NOTICE_CUSTOM_TYPE.to_owned(),
            content: Some(UserContent::Text(
                "The autonomous run ended, not done: no progress: 4 autonomous continuations in a row made no tool call with a new result, also after the harness asked for another approach."
                    .to_owned()
            )),
            display: true,
            details: Some(json!({ "stop": "noProgress", "stalls": 4 })),
            input: false,
            origin: None,
        }]
    );
    harness.close(cx()).await.expect("close");
}

#[tokio::test]
async fn an_eukhe_session_installs_the_autonomous_hooks_and_host_requests() {
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
    let requests = &session.deps().host_requests;
    // The removed goal's requests are gone.
    for removed in ["goal.get", "goal.create", "goal.complete", "goal.remaining"] {
        assert!(requests.get(removed).is_none(), "{removed} is registered");
    }
    let push = requests
        .get("directors.push")
        .expect("directors.push is registered");
    push(HostCall {
        data: json!({ "layer": "reminder", "text": "Run the tests first." }),
        cell_source_code: None,
        call: None,
        signal: None,
    })
    .await
    .expect("directors.push succeeds");
    assert_eq!(
        director_state(session.harness(), session.root().id(), cx())
            .await
            .expect("read")
            .stack,
        vec![Layer::reminder("Run the tests first.".to_owned())]
    );
    // An autonomous run of the session continues with the reminder first.
    set_autonomous(
        session.harness(),
        &session.deps().budget,
        session.root().id(),
        AutonomousChange::On(AgentAutonomousConfig::default()),
        &cwd,
        cx(),
    )
    .await
    .expect("autonomous on");
    set_acceptance(
        session.harness(),
        session.root().id(),
        Vec::new(),
        None,
        &cwd,
        cx(),
    )
    .await
    .expect("the checks clear");
    session
        .budget()
        .set(BudgetLimits {
            requests: Some(2),
            ..BudgetLimits::default()
        })
        .expect("the budget is set");
    faux.set_responses(vec![answer("a"), answer("b"), answer("unused")]);

    submit(session.root(), "work").await;
    session.harness().wait_for_idle(cx()).await.expect("idle");

    let texts = user_texts(&entries(session.root()).await);
    assert_eq!(texts.len(), 2, "{texts:?}");
    assert!(
        texts[1].starts_with("Run the tests first.\n\n[autonomous-continuation]"),
        "{texts:?}"
    );
    session.close(cx()).await.expect("close");
}

/// The removed goal's own document as old sessions hold it.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct OldGoal {
    status: String,
    objective: String,
}

static OLD_GOAL_DOC: RewindableConversationDoc<OldGoal> = match RewindableConversationDoc::define(
    DocDefinition {
        kind: "eukhe.goal",
        version: 1,
        initial: OldGoal::default,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    RewindableFork::AsOf,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.goal has a valid version"),
};

/// The Director stack of version 1, which could hold the goal's layer.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
struct OldDirectors {
    stack: Vec<Value>,
}

static OLD_DIRECTORS_DOC: RewindableConversationDoc<OldDirectors> =
    match RewindableConversationDoc::define(
        DocDefinition {
            kind: "eukhe.directors",
            version: 1,
            initial: OldDirectors::default,
            migrate: None,
            checkpoint_when: Some(|_, _, _| true),
        },
        RewindableFork::AsOf,
    ) {
        Ok(token) => token,
        Err(_) => panic!("eukhe.directors has a valid version"),
    };

/// An old session that ran the removed goal: an `eukhe.goal` record no
/// definition reads, a Director stack of version 1 with the goal's layer,
/// an acceptance document with the goal's claim mark, and `pi.user`
/// entries with the goal's origin. It opens, its stack reads without the
/// goal's layer, its entries keep their origin, it forks, and the fork
/// runs `/auto`.
#[tokio::test]
async fn an_old_session_with_goal_records_opens_forks_and_runs_auto() {
    let dir = tempfile::tempdir().expect("tempdir");
    let setup = setup();
    let goal_origin = InputOrigin::Goal {
        context: GoalContextKind::Continuation,
    };
    {
        let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
        set_acceptance(
            &harness,
            root.id(),
            vec![CheckSpec::intent()],
            None,
            setup.cwd(),
            cx(),
        )
        .await
        .expect("the checks set");
        setup.faux.set_responses(vec![answer("on it")]);
        submit_as(&root, "[goal: continuation] ship it", goal_origin.clone()).await;
        harness.wait_for_idle(cx()).await.expect("idle");
        let id = root.id();
        root.commit(
            move |tx| async move {
                let (goal, _) = open_doc(&tx, &OLD_GOAL_DOC, id).await?;
                write_doc(
                    &goal,
                    &OldGoal {
                        status: "active".to_owned(),
                        objective: "ship it".to_owned(),
                    },
                )?;
                let (directors, _) = open_doc(&tx, &OLD_DIRECTORS_DOC, id).await?;
                write_doc(
                    &directors,
                    &OldDirectors {
                        stack: vec![json!({ "kind": { "type": "goal" }, "budget": 7 })],
                    },
                )?;
                let (acceptance, doc) = open_doc(&tx, &ACCEPTANCE_DOC, id).await?;
                let mut value = serde_json::to_value(&doc).map_err(|error| {
                    eukhe_durable::session::SessionError::error(error.to_string())
                })?;
                value["goalClaim"] = json!(true);
                write_doc(&acceptance, &value)
            },
            cx(),
        )
        .await
        .expect("the old records commit");
        harness.close(cx()).await.expect("close");
        setup.cell.clear();
    }

    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    assert_eq!(
        director_state(&harness, root.id(), cx())
            .await
            .expect("the old stack reads"),
        DirectorState::default()
    );
    assert_eq!(
        acceptance_state(&harness, root.id(), cx())
            .await
            .expect("the acceptance reads")
            .checks
            .into_iter()
            .map(|check| check.spec)
            .collect::<Vec<_>>(),
        vec![CheckSpec::intent()]
    );
    let old = entries(&root).await;
    assert_eq!(user_origins(&old), vec![goal_origin.clone()]);
    let answered = old
        .iter()
        .find(|entry| entry.kind == ASSISTANT_ENTRY.kind())
        .expect("the old answer")
        .id;
    let forked = root
        .fork(
            answered,
            ConversationCreateOptions::new(ConversationOwnership::Ownerless),
            cx(),
        )
        .await
        .expect("fork");
    assert_eq!(
        director_state(&harness, forked.id(), cx())
            .await
            .expect("the fork's stack reads"),
        DirectorState::default()
    );

    // `/auto` on the fork: one step, then the loop hands back.
    *setup.limits.lock().unwrap_or_else(PoisonError::into_inner) = DirectorLimits {
        max_steps: 1,
        ..DirectorLimits::default()
    };
    autonomous_unchecked(&setup, &harness, &forked, AgentAutonomousConfig::default()).await;
    setup
        .faux
        .set_responses(vec![answer("a"), answer("b"), answer("unused")]);
    submit(&forked, "go on").await;
    harness.wait_for_idle(cx()).await.expect("idle");
    assert_eq!(
        user_origins(&entries(&forked).await),
        vec![
            goal_origin,
            InputOrigin::User,
            InputOrigin::Autonomous {
                nudge: AutonomousNudge::Continuation,
            },
        ]
    );
    harness.close(cx()).await.expect("close");
}
