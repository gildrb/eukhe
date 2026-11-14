//! The acceptance extension on a real Harness with faux models: a claim is
//! verified only by checks that pass on the final state, a refuted claim
//! takes its evidence back to the worker and ends failed at the cap, the
//! worker cannot change its checks, a judge reads evidence and never the
//! worker's words, verdicts are recorded and watched, and a crash never
//! turns a waiting claim into success.

use std::collections::VecDeque;
use std::future::Future;
use std::path::Path;
use std::pin::Pin;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_ai::typebox::{TSchema, Type};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::{create_registry, Registry};
use eukhe_durable::harness::types::{
    AgentChange, Extension, FieldChange, HarnessOptions, InputSubmissionDraft, ModelRef,
    ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{EntryRecord, Storage};
use eukhe_types::acceptance::{
    AcceptanceCheck, AcceptanceEnd, AcceptanceLabel, AcceptanceState, CheckResult, CheckSpec,
    CheckVerdict, ProtectedFile,
};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{JsonObject, StopReason, TextContent, UserContent, UserContentBlock};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use tokio::sync::watch;

use super::docs::ACCEPTANCE_DOC;
use super::evidence::{judge_prompt, ModelJudge};
use super::{
    acceptance_exit_code, acceptance_extension, acceptance_state, set_acceptance,
    watch_acceptance_updates, Judge, JudgeQuestion, JudgeReply, JudgeRequest,
    ACCEPTANCE_CUSTOM_TYPE,
};
use crate::autonomous::{ChildProcessResult, GateCommandRunner};
use crate::durable::budget::BudgetGate;
use crate::durable::directors::DirectorLimits;
use crate::durable::entries::{CustomEntryData, CUSTOM_ENTRY};
use crate::durable::goals::tests::{open_jsonl, user_origins, user_texts};
use crate::durable::goals::{goal_state, goals_extension, read_doc};
use crate::durable::{HarnessCell, HostCall, HostRequestRegistry};
use crate::goals::GoalStatus;

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// One scripted run of a check's command.
enum Scripted {
    Ends(ChildProcessResult),
    /// The run never ends: a crash strikes mid-check.
    Hangs,
}

/// Check commands scripted in order. A run past the script cannot start.
struct ScriptedRunner {
    script: Mutex<VecDeque<Scripted>>,
    commands: Mutex<Vec<String>>,
    /// Turns true once a run hangs.
    hung: watch::Sender<bool>,
}

impl Default for ScriptedRunner {
    fn default() -> Self {
        Self {
            script: Mutex::default(),
            commands: Mutex::default(),
            hung: watch::channel(false).0,
        }
    }
}

impl ScriptedRunner {
    fn script(&self, results: Vec<ChildProcessResult>) {
        *self.script.lock().unwrap_or_else(PoisonError::into_inner) =
            results.into_iter().map(Scripted::Ends).collect();
    }

    /// `results` in order, then a run that never ends.
    fn script_then_hang(&self, results: Vec<ChildProcessResult>) {
        self.script(results);
        self.script
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push_back(Scripted::Hangs);
    }

    fn commands(&self) -> Vec<String> {
        self.commands
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    /// Resolves once a run hangs.
    async fn hung(&self) {
        self.hung
            .subscribe()
            .wait_for(|hung| *hung)
            .await
            .expect("the runner lives");
    }
}

impl GateCommandRunner for ScriptedRunner {
    fn run_gate(
        &self,
        command: &str,
        _timeout_ms: u64,
    ) -> Pin<Box<dyn Future<Output = anyhow::Result<ChildProcessResult>> + Send + '_>> {
        self.commands
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(command.to_owned());
        let next = self
            .script
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .pop_front();
        Box::pin(async move {
            match next {
                None => Err(anyhow::anyhow!("no scripted check result")),
                Some(Scripted::Ends(result)) => Ok(result),
                Some(Scripted::Hangs) => {
                    self.hung.send_replace(true);
                    futures::future::pending().await
                }
            }
        })
    }
}

/// A judge whose replies are scripted in order; it records what it is
/// asked. A request past the script gets no answer.
#[derive(Default)]
struct ScriptedJudge {
    replies: Mutex<VecDeque<JudgeReply>>,
    requests: Mutex<Vec<JudgeRequest>>,
}

impl Judge for ScriptedJudge {
    fn judge(&self, request: JudgeRequest, _cx: &Context) -> BoxFuture<'_, JudgeReply> {
        self.requests
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(request);
        let reply = self
            .replies
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .pop_front()
            .unwrap_or_else(|| JudgeReply::Unavailable("no scripted reply".to_owned()));
        async move { reply }.boxed()
    }
}

/// Models, registry and services that survive a close and reopen.
struct Setup {
    faux: FauxProviderHandle,
    models: Models,
    registry: Registry,
    cell: HarnessCell,
    requests: HostRequestRegistry,
    runner: Arc<ScriptedRunner>,
    judge: Arc<ScriptedJudge>,
    /// The session cwd: protected files live here.
    dir: tempfile::TempDir,
}

/// A tool that runs the kernel's host request `request` with `data`.
fn host_tool(
    name: &'static str,
    request: &'static str,
    requests: HostRequestRegistry,
) -> Arc<ToolRegistration> {
    let schema: TSchema = Type::object(Vec::<(String, TSchema)>::new());
    define_tool(ToolRegistration::new(
        name,
        "test tool",
        schema,
        move |_, api, _| {
            let handler = requests.get(request).expect("the request is registered");
            async move {
                let text = match handler(HostCall {
                    data: json!({ "type": request, "checks": [] }),
                    cell_source_code: None,
                    call: Some(api),
                    signal: None,
                })
                .await
                {
                    Ok(response) => response.to_string(),
                    Err(error) => format!("error: {error}"),
                };
                Ok(ToolExecutionResult {
                    output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
                    ..ToolExecutionResult::default()
                })
            }
        },
    ))
}

/// `work`: a tool with an effect and no host request.
fn work_tool() -> Arc<ToolRegistration> {
    let schema: TSchema = Type::object(Vec::<(String, TSchema)>::new());
    define_tool(ToolRegistration::new(
        "work",
        "test tool",
        schema,
        move |_, _, _| async move {
            Ok(ToolExecutionResult {
                output: Some(vec![UserContentBlock::Text(TextContent::new("worked"))]),
                ..ToolExecutionResult::default()
            })
        },
    ))
}

fn setup() -> Setup {
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let registry = create_registry();
    let cell = HarnessCell::default();
    let requests = HostRequestRegistry::default();
    let runner = Arc::new(ScriptedRunner::default());
    let judge = Arc::new(ScriptedJudge::default());
    let dir = tempfile::tempdir().expect("tempdir");
    // The product order: the verifier's hooks before the goal's.
    registry
        .install(acceptance_extension(
            cell.clone(),
            Arc::clone(&runner) as Arc<dyn GateCommandRunner>,
            Arc::clone(&judge) as Arc<dyn Judge>,
            dir.path().to_path_buf(),
            &requests,
            None,
        ))
        .expect("the acceptance extension installs");
    registry
        .install(goals_extension(
            cell.clone(),
            BudgetGate::side(dir.path(), "session"),
            Arc::clone(&runner) as Arc<dyn GateCommandRunner>,
            Arc::new(DirectorLimits::default),
            &requests,
            Vec::new(),
        ))
        .expect("the goal extension installs");
    registry
        .install(define_extension(Extension {
            name: "test.tools".to_owned(),
            tools: vec![
                host_tool("finish", "goal.complete", requests.clone()),
                host_tool("drop_checks", "acceptance.set", requests.clone()),
                work_tool(),
            ],
            ..Extension::default()
        }))
        .expect("the test tools install");
    Setup {
        faux,
        models,
        registry,
        cell,
        requests,
        runner,
        judge,
        dir,
    }
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

    async fn memory(&self) -> (Harness, Conversation) {
        self.open(Arc::new(MemoryStorage::new())).await
    }

    fn cwd(&self) -> &Path {
        self.dir.path()
    }

    /// Set the checks as the owner.
    async fn accept(
        &self,
        harness: &Harness,
        root: &Conversation,
        specs: Vec<CheckSpec>,
        max_returns: Option<u64>,
    ) -> AcceptanceState {
        set_acceptance(harness, root.id(), specs, max_returns, self.cwd(), cx())
            .await
            .expect("the owner sets the checks")
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
            signal: None,
        })
        .await
    }
}

fn answer(text: &str) -> FauxResponseStep {
    faux_assistant_message(text, FauxAssistantMessageOptions::default()).into()
}

/// A response that calls the tool `name`.
fn call(name: &str, id: &str) -> FauxResponseStep {
    faux_assistant_message(
        faux_tool_call(name, JsonObject::new(), Some(id.to_owned())),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

async fn submit(root: &Conversation, text: &str) {
    let handle = root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text(text.to_owned()),
                when_busy: None,
                origin: InputOrigin::User,
                entry: None,
            },
            cx(),
        )
        .await
        .expect("the input is admitted");
    handle.wait(cx()).await.expect("the input settles");
}

/// A whole run: the input, then idle.
async fn run(harness: &Harness, root: &Conversation, text: &str) {
    submit(root, text).await;
    harness.wait_for_idle(cx()).await.expect("idle");
}

/// Entries oldest first.
async fn entries(conversation: &Conversation) -> Vec<EntryRecord> {
    let page = conversation
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .expect("entries read");
    page.items.into_iter().rev().collect()
}

/// The verdict rows, oldest first: their text, whether the model sees
/// them, and their details.
fn verdict_rows(entries: &[EntryRecord]) -> Vec<(String, bool, Value)> {
    entries
        .iter()
        .filter(|entry| entry.kind == CUSTOM_ENTRY.kind())
        .filter_map(|entry| {
            let data: CustomEntryData =
                serde_json::from_value(serde_json::to_value(entry.data.as_ref()?).ok()?).ok()?;
            if data.custom_type != ACCEPTANCE_CUSTOM_TYPE {
                return None;
            }
            let text = match data.content? {
                UserContent::Text(text) => text,
                UserContent::Blocks(_) => return None,
            };
            Some((text, entry.model.is_some(), data.details?))
        })
        .collect()
}

fn command(text: &str) -> CheckSpec {
    CheckSpec::Command {
        command: text.to_owned(),
        expect: 0,
        timeout_ms: None,
        protect: Vec::new(),
    }
}

fn exited(code: i32, output: &str) -> ChildProcessResult {
    ChildProcessResult {
        status: Some(code),
        stdout: output.to_owned(),
        ..ChildProcessResult::default()
    }
}

async fn state(harness: &Harness, root: &Conversation) -> AcceptanceState {
    acceptance_state(harness, root.id(), cx())
        .await
        .expect("the acceptance reads")
}

/// A state with its clock fields zeroed, for whole-value comparison.
fn timeless(mut state: AcceptanceState) -> AcceptanceState {
    for check in &mut state.checks {
        if let Some(result) = &mut check.result {
            result.judged_at = 0;
        }
    }
    if let Some(end) = &mut state.last_end {
        end.ended_at = 0;
    }
    state
}

fn judged(
    spec: CheckSpec,
    verdict: CheckVerdict,
    at: u64,
    summary: &str,
    evidence: &str,
) -> AcceptanceCheck {
    AcceptanceCheck {
        spec,
        protected: Vec::new(),
        result: Some(CheckResult {
            verdict,
            at,
            summary: summary.to_owned(),
            evidence: evidence.to_owned(),
            judged_at: 0,
        }),
    }
}

/// V3, V4: a final answer is a claim; with every check confirmed on the
/// final state the result is verified, and nothing goes back to the
/// worker.
#[tokio::test]
async fn a_claim_whose_checks_pass_on_the_final_state_is_verified() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![command("cargo test")], None)
        .await;
    setup.runner.script(vec![exited(0, "3 passed")]);
    setup
        .faux
        .set_responses(vec![call("work", "w1"), answer("done")]);

    run(&harness, &root, "do it").await;

    let got = state(&harness, &root).await;
    let at = got.state;
    assert!(at > 0, "the work tool's result is the final state");
    assert_eq!(
        timeless(got),
        AcceptanceState {
            label: AcceptanceLabel::ChecksPassedUnconfined,
            state: at,
            revision: 1,
            checks: vec![judged(
                command("cargo test"),
                CheckVerdict::Confirmed,
                at,
                "exited with code 0",
                "3 passed"
            )],
            claimed: false,
            tries: 0,
            max_returns: 3,
            last_end: Some(AcceptanceEnd {
                label: AcceptanceLabel::ChecksPassedUnconfined,
                at,
                ended_at: 0,
            }),
        }
    );
    let entries = entries(&root).await;
    assert_eq!(user_texts(&entries), vec!["do it".to_owned()]);
    let rows = verdict_rows(&entries);
    assert_eq!(rows.len(), 1);
    assert_eq!(
        (rows[0].0.as_str(), rows[0].1, &rows[0].2["outcome"]),
        (
            "Acceptance checks passed, unconfined: 1 acceptance check confirmed.",
            false,
            &json!("checks_passed_unconfined")
        )
    );
    assert_eq!(setup.runner.commands(), vec!["cargo test".to_owned()]);
    assert_eq!(
        acceptance_exit_code(&harness, root.id(), 0, cx())
            .await
            .expect("exit"),
        0
    );
    harness.close(cx()).await.expect("close");
}

/// V7, V10: a refuted claim takes its evidence back to the worker while
/// returns remain, then ends failed; the run never ends as success. A
/// check that judged the state is not run again while the state stands.
#[tokio::test]
async fn a_refuted_claim_returns_its_evidence_then_ends_failed() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![command("cargo test")], Some(2))
        .await;
    setup.runner.script(vec![exited(1, "2 tests failed")]);
    setup.faux.set_responses(vec![
        answer("done"),
        answer("it is done, really"),
        answer("nothing to fix"),
    ]);

    run(&harness, &root, "do it").await;

    let entries = entries(&root).await;
    let texts = user_texts(&entries);
    assert_eq!(texts.len(), 3, "{texts:?}");
    assert_eq!(
        texts[1],
        "[acceptance: not verified] The harness checked your claim that the task is done: an acceptance check failed or could not judge the current state (return 1 of 2).\n\n1. command `cargo test` (expect exit 0): refuted: exited with code 1\n\n<evidence>\n2 tests failed\n</evidence>\n\nFix the work so that every check passes (a check that could not judge, e.g. a timeout, runs again too), then finish again. Every check runs again on the final state; only the task's owner sets checks."
    );
    assert!(texts[2].contains("(return 2 of 2)"), "{}", texts[2]);
    assert_eq!(
        user_origins(&entries),
        vec![
            InputOrigin::User,
            InputOrigin::Director,
            InputOrigin::Director
        ]
    );
    let rows: Vec<String> = verdict_rows(&entries)
        .into_iter()
        .map(|(text, _, _)| text)
        .collect();
    assert_eq!(
        rows,
        vec![
            "Acceptance not verified: check 1 refuted (exited with code 1). Returned to the worker (1 of 2).".to_owned(),
            "Acceptance not verified: check 1 refuted (exited with code 1). Returned to the worker (2 of 2).".to_owned(),
            "Acceptance failed: check 1 refuted (exited with code 1).".to_owned(),
        ]
    );
    let got = state(&harness, &root).await;
    assert_eq!(
        (
            got.label,
            got.claimed,
            got.tries,
            got.last_end.map(|end| end.label)
        ),
        (
            AcceptanceLabel::Failed,
            false,
            0,
            Some(AcceptanceLabel::Failed)
        )
    );
    // The state never moved: the check ran once.
    assert_eq!(setup.runner.commands(), vec!["cargo test".to_owned()]);
    assert_eq!(
        acceptance_exit_code(&harness, root.id(), 0, cx())
            .await
            .expect("exit"),
        1
    );
    // A new message of the user moves the state: the next final answer is
    // a new claim, judged again on that state.
    setup.runner.script(vec![exited(1, "2 tests failed")]);
    setup.faux.set_responses(vec![
        answer("you are welcome"),
        answer("still nothing to fix"),
        answer("still nothing to fix"),
    ]);
    run(&harness, &root, "thanks anyway").await;
    let texts = user_texts(&self::entries(&root).await);
    assert_eq!(texts[3], "thanks anyway");
    assert_eq!(state(&harness, &root).await.label, AcceptanceLabel::Failed);
    assert_eq!(
        setup.runner.commands(),
        vec!["cargo test".to_owned(), "cargo test".to_owned()]
    );
    harness.close(cx()).await.expect("close");
}

/// V3, V7: after the worker's fix (a new effect) every check runs again on
/// the new state; passing there, the claim is verified.
#[tokio::test]
async fn a_returned_claim_is_verified_once_the_fix_passes_on_the_new_state() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(
            &harness,
            &root,
            vec![command("cargo test"), command("cargo clippy")],
            None,
        )
        .await;
    setup.runner.script(vec![
        exited(0, "ok"),
        exited(101, "warning: unused"),
        exited(0, "ok"),
        exited(0, "clean"),
    ]);
    setup
        .faux
        .set_responses(vec![answer("done"), call("work", "w1"), answer("fixed")]);

    run(&harness, &root, "do it").await;

    let got = state(&harness, &root).await;
    assert_eq!(got.label, AcceptanceLabel::ChecksPassedUnconfined);
    assert_eq!(got.tries, 0);
    assert!(got.checks.iter().all(|check| check
        .result
        .as_ref()
        .is_some_and(|result| result.at == got.state)));
    // Both checks ran on the first state and again on the fixed one.
    assert_eq!(
        setup.runner.commands(),
        vec!["cargo test", "cargo clippy", "cargo test", "cargo clippy"]
    );
    let entries = entries(&root).await;
    let texts = user_texts(&entries);
    assert_eq!(texts.len(), 2, "{texts:?}");
    assert!(texts[1].contains("1. command `cargo test` (expect exit 0): confirmed"));
    assert!(texts[1].contains(
        "2. command `cargo clippy` (expect exit 0): refuted: exited with code 101\n\n<evidence>\nwarning: unused\n</evidence>"
    ));
    harness.close(cx()).await.expect("close");
}

/// V4: with no checks the result is unverified, nothing is written and
/// nothing runs; a goal completed without checks says so.
#[tokio::test]
async fn no_checks_is_unverified_and_a_goal_completed_without_them_says_so() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .host_request("goal.create", json!({ "objective": "ship it" }))
        .await
        .expect("goal.create succeeds");
    setup
        .faux
        .set_responses(vec![call("finish", "f1"), answer("done")]);

    run(&harness, &root, "work").await;

    let got = state(&harness, &root).await;
    assert_eq!(
        got,
        AcceptanceState {
            state: got.state,
            ..AcceptanceState::default()
        }
    );
    assert_eq!(
        read_doc(&harness, &ACCEPTANCE_DOC, root.id(), cx())
            .await
            .expect("read"),
        None
    );
    let goal = goal_state(&harness, root.id(), cx()).await.expect("goal");
    assert_eq!(
        (goal.status, goal.last_reason.as_deref()),
        (
            GoalStatus::Complete,
            Some("unverified (no acceptance checks)")
        )
    );
    assert!(setup.runner.commands().is_empty());
    assert!(verdict_rows(&entries(&root).await).is_empty());
    harness.close(cx()).await.expect("close");
}

/// V3, V5: under an active goal `goal.complete()` is only a claim: the
/// goal completes when the checks pass on the final state.
#[tokio::test]
async fn a_goal_completes_only_when_its_checks_pass() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .host_request("goal.create", json!({ "objective": "ship it" }))
        .await
        .expect("goal.create succeeds");
    setup
        .accept(&harness, &root, vec![command("cargo test")], None)
        .await;
    setup.runner.script(vec![exited(0, "ok")]);
    setup.faux.set_responses(vec![
        answer("step one"),
        call("finish", "f1"),
        answer("done"),
    ]);

    run(&harness, &root, "work").await;

    let entries = entries(&root).await;
    // The first final answer was no claim: the goal went on.
    let texts = user_texts(&entries);
    assert_eq!(texts.len(), 2, "{texts:?}");
    assert!(texts[1].starts_with("[goal: continuation]"));
    // The claim left the goal active until the verdict.
    let claim = serde_json::to_string(&entries).expect("entries encode");
    assert!(claim.contains(r#"\"status\":\"active\""#), "{claim}");
    assert!(claim.contains(r#"\"status\":\"pending\""#), "{claim}");
    assert!(claim.contains(r#"\"checks\":1"#), "{claim}");
    let goal = goal_state(&harness, root.id(), cx()).await.expect("goal");
    assert_eq!(
        (goal.status, goal.last_reason.as_deref()),
        (
            GoalStatus::Complete,
            Some("checks passed, unconfined (1 acceptance check confirmed)")
        )
    );
    assert_eq!(
        state(&harness, &root).await.label,
        AcceptanceLabel::ChecksPassedUnconfined
    );
    assert_eq!(setup.runner.commands(), vec!["cargo test".to_owned()]);
    harness.close(cx()).await.expect("close");
}

/// V7: a goal whose claim is refuted gets the evidence back, goes on, and
/// at the cap pauses failed: it never completes.
#[tokio::test]
async fn a_goal_whose_claim_stays_refuted_pauses_and_never_completes() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .host_request("goal.create", json!({ "objective": "ship it" }))
        .await
        .expect("goal.create succeeds");
    setup
        .accept(&harness, &root, vec![command("cargo test")], Some(1))
        .await;
    setup
        .runner
        .script(vec![exited(1, "1 failed"), exited(1, "1 failed")]);
    setup.faux.set_responses(vec![
        call("finish", "f1"),
        answer("done"),
        call("finish", "f2"),
        answer("done again"),
    ]);

    run(&harness, &root, "work").await;

    let goal = goal_state(&harness, root.id(), cx()).await.expect("goal");
    assert_eq!(
        (goal.status, goal.last_reason.as_deref()),
        (
            GoalStatus::Paused,
            Some("Acceptance failed: check 1 refuted (exited with code 1)")
        )
    );
    let got = state(&harness, &root).await;
    assert_eq!(
        (got.label, got.last_end.map(|end| end.label)),
        (AcceptanceLabel::Failed, Some(AcceptanceLabel::Failed))
    );
    let entries = entries(&root).await;
    let texts = user_texts(&entries);
    assert_eq!(texts.len(), 2, "{texts:?}");
    assert!(texts[1].starts_with("[acceptance: not verified]"));
    assert_eq!(setup.faux.get_pending_response_count(), 0);
    harness.close(cx()).await.expect("close");
}

/// V5: the worker reads its checks and cannot set, drop or skip them: the
/// compiled core refuses the worker's Assign and nothing changes.
#[tokio::test]
async fn the_worker_cannot_change_or_skip_its_checks() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    let set = setup
        .accept(&harness, &root, vec![command("cargo test")], Some(0))
        .await;
    setup.runner.script(vec![exited(1, "1 failed")]);
    setup
        .faux
        .set_responses(vec![call("drop_checks", "d1"), answer("done")]);
    let read = setup
        .host_request("acceptance.get", json!({}))
        .await
        .expect("acceptance.get succeeds");
    assert_eq!(read, serde_json::to_value(&set).expect("encode"));

    run(&harness, &root, "do it").await;

    let entries = entries(&root).await;
    let refused = serde_json::to_string(&entries).expect("entries encode");
    assert!(
        refused.contains(
            "error: only the task's owner sets its acceptance checks: this change was refused"
        ),
        "{refused}"
    );
    let got = state(&harness, &root).await;
    assert_eq!(
        (got.revision, got.checks.len(), got.label),
        (1, 1, AcceptanceLabel::Failed)
    );
    // The check still ran, on the state after the refused act.
    assert_eq!(setup.runner.commands(), vec!["cargo test".to_owned()]);
    harness.close(cx()).await.expect("close");
}

/// V5: a check whose protected file the worker changed is refuted even
/// though its command passes.
#[tokio::test]
async fn a_check_whose_protected_file_changed_fails() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    std::fs::write(setup.cwd().join("test_x.py"), "assert add(2, 2) == 4\n").expect("write");
    let spec = CheckSpec::Command {
        command: "pytest test_x.py".to_owned(),
        expect: 0,
        timeout_ms: None,
        protect: vec!["test_x.py".to_owned()],
    };
    let set = setup.accept(&harness, &root, vec![spec], Some(0)).await;
    assert_eq!(
        set.checks[0].protected,
        vec![ProtectedFile {
            path: "test_x.py".to_owned(),
            sha256: Some(format!("{:x}", Sha256::digest(b"assert add(2, 2) == 4\n"))),
        }],
        "the file is hashed as the owner left it"
    );
    // The worker weakens the test, then the command passes.
    std::fs::write(setup.cwd().join("test_x.py"), "assert True\n").expect("write");
    setup.runner.script(vec![exited(0, "1 passed")]);
    setup.faux.set_responses(vec![answer("done")]);

    run(&harness, &root, "do it").await;

    let got = state(&harness, &root).await;
    assert_eq!(got.label, AcceptanceLabel::Failed);
    let result = got.checks[0].result.as_ref().expect("judged");
    assert_eq!(
        (result.verdict, result.summary.as_str()),
        (CheckVerdict::Refuted, "protected file changed: test_x.py")
    );
    harness.close(cx()).await.expect("close");
}

/// V6: the judge's request holds the owner's condition and what the
/// harness observed; the worker's final answer never reaches it.
#[tokio::test]
async fn a_judge_reads_the_evidence_and_never_the_workers_words() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    let condition = "every test passes and no test was removed";
    setup
        .accept(
            &harness,
            &root,
            vec![
                command("cargo test"),
                CheckSpec::Judge {
                    condition: condition.to_owned(),
                    evidence: vec!["git diff --stat".to_owned()],
                    model: None,
                },
            ],
            None,
        )
        .await;
    setup.runner.script(vec![
        exited(0, "test result: ok. 3 passed"),
        exited(0, "src/lib.rs | 4 ++--"),
    ]);
    setup
        .judge
        .replies
        .lock()
        .expect("replies")
        .push_back(JudgeReply::Text(
            "PASS\nThe run shows 3 passed and the diff touches no test.".to_owned(),
        ));
    setup.faux.set_responses(vec![answer(
        "WORKER-SUMMARY: trust me, everything is perfect and every test passes",
    )]);

    run(&harness, &root, "do it").await;

    let requests = setup.judge.requests.lock().expect("requests").clone();
    let request = JudgeRequest {
        conversation_id: root.id(),
        question: JudgeQuestion::Condition(condition.to_owned()),
        evidence: "Acceptance check 1 ran `cargo test`: exited with code 0\ntest result: ok. 3 passed\n\n`git diff --stat`: exited with code 0\nsrc/lib.rs | 4 ++--".to_owned(),
        model: None,
    };
    assert_eq!(requests, vec![request.clone()]);
    assert!(!judge_prompt(&request).contains("WORKER-SUMMARY"));
    let got = state(&harness, &root).await;
    assert_eq!(got.label, AcceptanceLabel::ChecksPassedUnconfined);
    let result = got.checks[1].result.as_ref().expect("judged");
    assert_eq!(
        (
            result.verdict,
            result.summary.as_str(),
            result.evidence.as_str()
        ),
        (
            CheckVerdict::Confirmed,
            "the judge answered PASS",
            "PASS\nThe run shows 3 passed and the diff touches no test."
        )
    );
    harness.close(cx()).await.expect("close");
}

/// V6: the product judge is one request of its own: the judge's system
/// prompt, then the condition and the evidence, and nothing of the
/// conversation.
#[tokio::test]
async fn the_product_judge_sends_one_request_with_the_condition_and_the_evidence_only() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .faux
        .set_responses(vec![answer("the worker talks first")]);
    run(&harness, &root, "a private task the judge never sees").await;
    let seen: Arc<Mutex<Vec<String>>> = Arc::default();
    let record = Arc::clone(&seen);
    setup
        .faux
        .set_responses(vec![FauxResponseStep::factory(move |context, _, _, _| {
            record
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(format!("{context:?}"));
            Ok(faux_assistant_message(
                "FAIL\nThe evidence shows a failure.",
                FauxAssistantMessageOptions::default(),
            ))
        })]);
    let judge = ModelJudge {
        harness: setup.cell.clone(),
        models: setup.models.clone(),
    };

    let reply = judge
        .judge(
            JudgeRequest {
                conversation_id: root.id(),
                question: JudgeQuestion::Condition("the build is green".to_owned()),
                evidence: "make: *** [build] Error 2".to_owned(),
                model: None,
            },
            cx(),
        )
        .await;

    assert_eq!(
        reply,
        JudgeReply::Text("FAIL\nThe evidence shows a failure.".to_owned())
    );
    let seen = seen.lock().expect("seen").clone();
    assert_eq!(seen.len(), 1);
    assert!(
        seen[0].contains("You are an acceptance judge: a request separate from the worker"),
        "{}",
        seen[0]
    );
    assert!(
        seen[0].contains("<condition>\\nthe build is green\\n</condition>"),
        "{}",
        seen[0]
    );
    assert!(
        seen[0].contains("<evidence>\\nmake: *** [build] Error 2\\n</evidence>"),
        "{}",
        seen[0]
    );
    assert!(!seen[0].contains("a private task"), "{}", seen[0]);
    assert!(!seen[0].contains("the worker talks first"), "{}", seen[0]);
    harness.close(cx()).await.expect("close");
}

/// V2, V7: a check that timed out and a judge with no readable answer are
/// broken: never passed, never failed. The claim goes back to the worker
/// with that evidence and both checks run again at its next claim; at the
/// cap the claim ends unverified, and the run never exits 0.
#[tokio::test]
async fn a_broken_check_goes_back_to_the_worker_up_to_the_cap_then_ends_unverified() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(
            &harness,
            &root,
            vec![
                command("cargo test"),
                CheckSpec::Judge {
                    condition: "the docs are updated".to_owned(),
                    evidence: Vec::new(),
                    model: None,
                },
            ],
            Some(1),
        )
        .await;
    let timed_out = || ChildProcessResult {
        timed_out: true,
        ..ChildProcessResult::default()
    };
    setup.runner.script(vec![timed_out(), timed_out()]);
    {
        let mut replies = setup.judge.replies.lock().expect("replies");
        replies.push_back(JudgeReply::Text("It looks fine to me.".to_owned()));
        replies.push_back(JudgeReply::Unavailable("the provider is down".to_owned()));
    }
    setup
        .faux
        .set_responses(vec![answer("done"), answer("done, nothing to change")]);

    run(&harness, &root, "do it").await;

    let entries = entries(&root).await;
    assert_eq!(
        user_origins(&entries),
        vec![InputOrigin::User, InputOrigin::Director]
    );
    let texts = user_texts(&entries);
    assert!(texts[1].contains("(return 1 of 1)"), "{}", texts[1]);
    assert!(
        texts[1]
            .contains("1. command `cargo test` (expect exit 0): broken: timed out after 600000 ms"),
        "{}",
        texts[1]
    );
    assert!(
        texts[1].contains("2. judge: the docs are updated: broken: the judge's reply starts with neither PASS nor FAIL"),
        "{}",
        texts[1]
    );
    let rows: Vec<String> = verdict_rows(&entries)
        .into_iter()
        .map(|(text, _, _)| text)
        .collect();
    assert_eq!(
        rows,
        vec![
            "Acceptance not verified: check 1 broken (timed out after 600000 ms); check 2 broken (the judge's reply starts with neither PASS nor FAIL). Returned to the worker (1 of 1).".to_owned(),
            "Acceptance unverified: check 1 broken (timed out after 600000 ms); check 2 broken (the judge gave no answer: the provider is down).".to_owned(),
        ]
    );
    // The broken checks ran again at the second claim, on the same state.
    assert_eq!(
        setup.runner.commands(),
        vec!["cargo test".to_owned(), "cargo test".to_owned()]
    );
    assert_eq!(setup.judge.requests.lock().expect("requests").len(), 2);
    let got = state(&harness, &root).await;
    assert_eq!(
        (got.label, got.tries, got.last_end.map(|end| end.label)),
        (
            AcceptanceLabel::Unverified,
            0,
            Some(AcceptanceLabel::Unverified)
        )
    );
    assert_eq!(
        acceptance_exit_code(&harness, root.id(), 0, cx())
            .await
            .expect("exit"),
        1
    );
    harness.close(cx()).await.expect("close");
}

/// The judge requests the scripted judge got, oldest first.
fn judge_requests(setup: &Setup) -> Vec<JudgeRequest> {
    setup.judge.requests.lock().expect("requests").clone()
}

fn intent_messages(request: &JudgeRequest) -> Vec<String> {
    match &request.question {
        JudgeQuestion::Intent(messages) => messages.clone(),
        JudgeQuestion::Condition(condition) => panic!("a condition, not the intent: {condition}"),
    }
}

/// V6, V11: the intent judge reads the user's own messages and what the
/// harness observed (the round's command checks, the workspace's files),
/// never the worker's words nor a continuation the harness added.
#[tokio::test]
async fn the_intent_judge_reads_the_users_messages_and_never_the_workers() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    std::fs::write(
        setup.cwd().join("flags.txt"),
        "--verbose prints every step\n",
    )
    .expect("write");
    setup
        .accept(
            &harness,
            &root,
            vec![command("cargo test"), CheckSpec::intent()],
            None,
        )
        .await;
    setup.runner.script(vec![exited(0, "3 passed")]);
    setup
        .judge
        .replies
        .lock()
        .expect("replies")
        .push_back(JudgeReply::Text(
            "PASS\n1. a --verbose flag: flags.txt".to_owned(),
        ));
    setup.faux.set_responses(vec![
        call("work", "w1"),
        answer("WORKER-SUMMARY: I added the flag and everything is perfect"),
    ]);

    run(&harness, &root, "add a --verbose flag").await;

    let requests = judge_requests(&setup);
    assert_eq!(requests.len(), 1);
    let request = &requests[0];
    assert_eq!(
        intent_messages(request),
        vec!["add a --verbose flag".to_owned()]
    );
    assert!(
        request
            .evidence
            .contains("Acceptance check 1 ran `cargo test`: exited with code 0\n3 passed"),
        "{}",
        request.evidence
    );
    assert!(
        request
            .evidence
            .contains("--- flags.txt\n--verbose prints every step"),
        "{}",
        request.evidence
    );
    let prompt = judge_prompt(request);
    assert!(prompt.contains("<user_messages>\n<message n=\"1\">\nadd a --verbose flag\n</message>\n</user_messages>"), "{prompt}");
    assert!(!prompt.contains("WORKER-SUMMARY"), "{prompt}");
    let got = state(&harness, &root).await;
    assert_eq!(got.label, AcceptanceLabel::ChecksPassedUnconfined);
    assert_eq!(
        got.checks[1].result.as_ref().map(|result| result.verdict),
        Some(CheckVerdict::Confirmed)
    );
    harness.close(cx()).await.expect("close");
}

/// V3, V11: a requirement the user adds after the task was verified
/// extends it: the verified result stops counting at the new message, the
/// next final answer is judged on all the user's messages, and the task is
/// not reported done until the added requirement holds.
#[tokio::test]
async fn a_requirement_added_later_extends_the_task() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![CheckSpec::intent()], None)
        .await;
    {
        let mut replies = setup.judge.replies.lock().expect("replies");
        replies.push_back(JudgeReply::Text("PASS\nhello.txt exists".to_owned()));
        replies.push_back(JudgeReply::Text("FAIL\nbye.txt is missing".to_owned()));
        replies.push_back(JudgeReply::Text("PASS\nboth files exist".to_owned()));
    }
    setup
        .faux
        .set_responses(vec![call("work", "w1"), answer("hello.txt written")]);
    run(&harness, &root, "write hello.txt").await;
    let first = state(&harness, &root).await;
    assert_eq!(first.label, AcceptanceLabel::ChecksPassedUnconfined);

    // The worker answers the added requirement without doing it, then
    // does it once the evidence comes back.
    setup.faux.set_responses(vec![
        answer("sure, done"),
        call("work", "w2"),
        answer("bye.txt written"),
    ]);
    run(&harness, &root, "also write bye.txt").await;

    let requests = judge_requests(&setup);
    assert_eq!(requests.len(), 3);
    let both = vec![
        "write hello.txt".to_owned(),
        "also write bye.txt".to_owned(),
    ];
    assert_eq!(
        intent_messages(&requests[0]),
        vec!["write hello.txt".to_owned()]
    );
    assert_eq!(intent_messages(&requests[1]), both);
    assert_eq!(intent_messages(&requests[2]), both);
    let outcomes: Vec<Value> = verdict_rows(&entries(&root).await)
        .into_iter()
        .map(|(_, _, details)| details["outcome"].clone())
        .collect();
    assert_eq!(
        outcomes,
        vec![
            json!("checks_passed_unconfined"),
            json!("returned"),
            json!("checks_passed_unconfined")
        ]
    );
    let last = state(&harness, &root).await;
    assert_eq!(last.label, AcceptanceLabel::ChecksPassedUnconfined);
    assert_ne!(last.state, first.state);
    harness.close(cx()).await.expect("close");
}

/// V11: a side question asked after the task was verified is answered; it
/// adds no requirement, and the task is neither ended again nor failed:
/// nothing goes back to the worker and the result stays verified.
#[tokio::test]
async fn a_side_question_neither_ends_nor_fails_the_task() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![CheckSpec::intent()], None)
        .await;
    {
        let mut replies = setup.judge.replies.lock().expect("replies");
        replies.push_back(JudgeReply::Text("PASS\nthe parser exists".to_owned()));
        replies.push_back(JudgeReply::Text(
            "PASS\nThe second message is a side question; the parser still exists.".to_owned(),
        ));
    }
    setup
        .faux
        .set_responses(vec![call("work", "w1"), answer("parser written")]);
    run(&harness, &root, "write the parser").await;
    assert_eq!(
        state(&harness, &root).await.label,
        AcceptanceLabel::ChecksPassedUnconfined
    );

    setup
        .faux
        .set_responses(vec![answer("It reads one token at a time.")]);
    run(&harness, &root, "how does the parser read its input?").await;

    let entries = entries(&root).await;
    assert_eq!(
        user_origins(&entries),
        vec![InputOrigin::User, InputOrigin::User],
        "nothing went back to the worker"
    );
    assert_eq!(
        intent_messages(&judge_requests(&setup)[1]),
        vec![
            "write the parser".to_owned(),
            "how does the parser read its input?".to_owned()
        ]
    );
    let got = state(&harness, &root).await;
    assert_eq!(
        (got.label, got.tries, got.last_end.map(|end| end.label)),
        (
            AcceptanceLabel::ChecksPassedUnconfined,
            0,
            Some(AcceptanceLabel::ChecksPassedUnconfined)
        )
    );
    harness.close(cx()).await.expect("close");
}

/// V3: an edit made outside the session moves the state: the verified
/// result no longer counts (served unverified, the exit is nonzero) until
/// the checks pass again on the edited workspace.
#[tokio::test]
async fn an_edit_outside_the_session_makes_the_verdict_stale() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![command("cargo test")], None)
        .await;
    setup.runner.script(vec![exited(0, "ok"), exited(0, "ok")]);
    setup.faux.set_responses(vec![answer("done")]);
    run(&harness, &root, "do it").await;
    let verified = state(&harness, &root).await;
    assert_eq!(verified.label, AcceptanceLabel::ChecksPassedUnconfined);
    assert_eq!(state(&harness, &root).await.state, verified.state);

    // The user edits a file by hand: no tool result, no message.
    std::fs::write(setup.cwd().join("notes.md"), "edited outside").expect("write");

    let stale = state(&harness, &root).await;
    assert_ne!(stale.state, verified.state);
    assert_eq!(stale.label, AcceptanceLabel::Unverified);
    assert_eq!(
        acceptance_exit_code(&harness, root.id(), 0, cx())
            .await
            .expect("exit"),
        1
    );

    setup.faux.set_responses(vec![answer("checked again")]);
    run(&harness, &root, "is it still done?").await;
    assert_eq!(
        state(&harness, &root).await.label,
        AcceptanceLabel::ChecksPassedUnconfined
    );
    assert_eq!(
        setup.runner.commands(),
        vec!["cargo test".to_owned(), "cargo test".to_owned()]
    );
    harness.close(cx()).await.expect("close");
}

/// V3, V8: the worker's next effect makes a verified result unverified
/// again: the watchers hear it, and the next final answer has to earn the
/// result on the new state.
#[tokio::test]
async fn a_later_effect_of_the_worker_makes_the_result_unverified_again() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![command("cargo test")], None)
        .await;
    setup.runner.script(vec![exited(0, "ok")]);
    setup.faux.set_responses(vec![answer("done")]);
    run(&harness, &root, "do it").await;
    assert_eq!(
        state(&harness, &root).await.label,
        AcceptanceLabel::ChecksPassedUnconfined
    );

    // The next run changes something and breaks the check.
    setup
        .runner
        .script(vec![exited(1, "1 failed"), exited(1, "1 failed")]);
    let mut updates = watch_acceptance_updates(&harness, root.id(), cx()).expect("watch");
    assert_eq!(
        updates.next().await.map(|state| state.label),
        Some(AcceptanceLabel::ChecksPassedUnconfined)
    );
    setup.faux.set_responses(vec![
        call("work", "w1"),
        answer("changed it"),
        answer("cannot fix"),
        answer("cannot fix"),
        answer("cannot fix"),
    ]);
    run(&harness, &root, "one more thing").await;

    // First the effect: unverified, the old end cleared; then the verdicts.
    let stale = updates.next().await.expect("the effect is heard");
    assert_eq!(
        (
            stale.label,
            stale.last_end.clone(),
            stale.checks[0].result.is_some()
        ),
        (AcceptanceLabel::Unverified, None, true)
    );
    let mut last = stale;
    while last.last_end.is_none() {
        last = updates.next().await.expect("the verdict is heard");
    }
    assert_eq!(last.label, AcceptanceLabel::Failed);
    assert_eq!(state(&harness, &root).await.label, AcceptanceLabel::Failed);
    assert_eq!(
        setup.runner.commands(),
        vec!["cargo test".to_owned(), "cargo test".to_owned()]
    );
    harness.close(cx()).await.expect("close");
}

/// V8: the verdict, its checks and the evidence are recorded in the
/// session (the document, a transcript row) and every watcher hears each
/// change.
#[tokio::test]
async fn the_verdict_its_checks_and_evidence_are_recorded_and_watched() {
    let dir = tempfile::tempdir().expect("tempdir");
    let setup = setup();
    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    let mut updates = watch_acceptance_updates(&harness, root.id(), cx()).expect("watch");
    assert_eq!(updates.next().await, Some(AcceptanceState::default()));
    let set = setup
        .accept(&harness, &root, vec![command("cargo test")], None)
        .await;
    assert_eq!(updates.next().await, Some(set));
    setup.runner.script(vec![exited(0, "3 passed")]);
    setup.faux.set_responses(vec![answer("done")]);

    run(&harness, &root, "do it").await;

    let mut heard = Vec::new();
    loop {
        let update = updates.next().await.expect("an update");
        let ended = update.last_end.is_some();
        heard.push((update.label, update.claimed));
        if ended {
            break;
        }
    }
    assert_eq!(
        heard.last(),
        Some(&(AcceptanceLabel::ChecksPassedUnconfined, false)),
        "{heard:?}"
    );
    let verified = timeless(state(&harness, &root).await);
    let rows = verdict_rows(&entries(&root).await);
    assert_eq!(rows.len(), 1);
    let mut recorded = rows[0].2["checks"].clone();
    recorded[0]["result"]["judgedAt"] = json!(0);
    assert_eq!(
        recorded,
        serde_json::to_value(&verified.checks).expect("encode")
    );
    assert_eq!(recorded[0]["result"]["evidence"], "3 passed");
    harness.close(cx()).await.expect("close");
    setup.cell.clear();

    // The record survives the process: a reopened session reads the same.
    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    assert_eq!(timeless(state(&harness, &root).await), verified);
    harness.close(cx()).await.expect("close");
}

/// Submit `text` without waiting for its run.
async fn start(root: &Conversation, text: &str) {
    root.submit(
        InputSubmissionDraft {
            request_id: Some("work".to_owned()),
            content: UserContent::Text(text.to_owned()),
            when_busy: None,
            origin: InputOrigin::User,
            entry: None,
        },
        cx(),
    )
    .await
    .expect("admitted");
}

/// V9: a crash while a check runs leaves the claim waiting, unverified;
/// the restart invents no verdict, and the resumed run judges the check
/// again: only that verdict counts.
#[tokio::test]
async fn a_crash_before_a_verdict_is_recorded_runs_the_check_again() {
    let dir = tempfile::tempdir().expect("tempdir");
    let setup = setup();
    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    setup
        .accept(&harness, &root, vec![command("cargo test")], None)
        .await;
    setup.runner.script_then_hang(Vec::new());
    setup.faux.set_responses(vec![answer("done")]);
    start(&root, "do it").await;
    setup.runner.hung().await;
    let waiting = state(&harness, &root).await;
    assert_eq!(
        (
            waiting.label,
            waiting.claimed,
            waiting.checks[0].result.clone()
        ),
        (AcceptanceLabel::Unverified, true, None)
    );
    // A crash mid-check: the Harness closes with the verifier in flight.
    harness.close(cx()).await.expect("close");
    setup.cell.clear();

    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    let reopened = state(&harness, &root).await;
    assert_eq!(
        (
            reopened.label,
            reopened.claimed,
            reopened.checks[0].result.clone(),
            reopened.last_end.clone()
        ),
        (AcceptanceLabel::Unverified, true, None, None),
        "a restart invents no verdict"
    );
    assert_eq!(
        acceptance_exit_code(&harness, root.id(), 0, cx())
            .await
            .expect("exit"),
        1
    );
    setup.runner.script(vec![exited(0, "ok")]);
    // The resumed generation may ask the model for its answer again.
    setup.faux.set_responses(vec![answer("done")]);
    harness.resume().expect("resume");
    harness.wait_for_idle(cx()).await.expect("idle");

    let got = state(&harness, &root).await;
    assert_eq!(
        (got.label, got.claimed, got.last_end.map(|end| end.label)),
        (
            AcceptanceLabel::ChecksPassedUnconfined,
            false,
            Some(AcceptanceLabel::ChecksPassedUnconfined)
        )
    );
    assert_eq!(setup.runner.commands(), vec!["cargo test", "cargo test"]);
    harness.close(cx()).await.expect("close");
}

/// V9: a reopened session keeps its recorded verdicts and judges a
/// waiting claim again: the check whose verdict was committed is not run
/// twice, the other one is, and its refutation ends the claim failed.
#[tokio::test]
async fn a_reopened_session_keeps_its_verdicts_and_judges_a_waiting_claim_again() {
    let dir = tempfile::tempdir().expect("tempdir");
    let setup = setup();
    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    setup
        .accept(
            &harness,
            &root,
            vec![command("cargo test"), command("cargo clippy")],
            Some(0),
        )
        .await;
    // The first check passes and is recorded; the second never ends.
    setup.runner.script_then_hang(vec![exited(0, "ok")]);
    setup.faux.set_responses(vec![answer("done")]);
    start(&root, "do it").await;
    setup.runner.hung().await;
    harness.close(cx()).await.expect("close");
    setup.cell.clear();

    let (harness, root) = setup.open(open_jsonl(dir.path()).await).await;
    let reopened = state(&harness, &root).await;
    assert_eq!(
        (
            reopened.label,
            reopened.claimed,
            reopened
                .checks
                .iter()
                .map(|check| check.result.as_ref().map(|result| result.verdict))
                .collect::<Vec<_>>(),
        ),
        (
            AcceptanceLabel::Unverified,
            true,
            vec![Some(CheckVerdict::Confirmed), None],
        )
    );
    setup.runner.script(vec![exited(1, "1 warning")]);
    setup.faux.set_responses(vec![answer("done")]);
    harness.resume().expect("resume");
    harness.wait_for_idle(cx()).await.expect("idle");

    let got = state(&harness, &root).await;
    assert_eq!(
        (
            got.label,
            got.claimed,
            got.checks
                .iter()
                .map(|check| check.result.as_ref().map(|result| result.verdict))
                .collect::<Vec<_>>(),
            got.last_end.map(|end| end.label),
        ),
        (
            AcceptanceLabel::Failed,
            false,
            vec![Some(CheckVerdict::Confirmed), Some(CheckVerdict::Refuted)],
            Some(AcceptanceLabel::Failed),
        )
    );
    // `cargo test` ran once in all; `cargo clippy` ran again after the crash.
    assert_eq!(
        setup.runner.commands(),
        vec!["cargo test", "cargo clippy", "cargo clippy"]
    );
    harness.close(cx()).await.expect("close");
}

/// V1: a change of the checks discards every verdict: checks edited after
/// a pass have to pass again.
#[tokio::test]
async fn a_change_of_the_checks_discards_every_verdict() {
    let setup = setup();
    let (harness, root) = setup.memory().await;
    setup
        .accept(&harness, &root, vec![command("cargo test")], None)
        .await;
    setup.runner.script(vec![exited(0, "ok")]);
    setup.faux.set_responses(vec![answer("done")]);
    run(&harness, &root, "do it").await;
    assert_eq!(
        state(&harness, &root).await.label,
        AcceptanceLabel::ChecksPassedUnconfined
    );

    let changed = setup
        .accept(
            &harness,
            &root,
            vec![command("cargo test"), command("cargo clippy")],
            None,
        )
        .await;

    assert_eq!(
        changed,
        AcceptanceState {
            label: AcceptanceLabel::Unverified,
            state: changed.state,
            revision: 2,
            checks: vec![
                AcceptanceCheck {
                    spec: command("cargo test"),
                    protected: Vec::new(),
                    result: None,
                },
                AcceptanceCheck {
                    spec: command("cargo clippy"),
                    protected: Vec::new(),
                    result: None,
                },
            ],
            claimed: false,
            tries: 0,
            max_returns: 3,
            last_end: None,
        }
    );
    let too_many = set_acceptance(
        &harness,
        root.id(),
        vec![command("true"); 65],
        None,
        setup.cwd(),
        cx(),
    )
    .await
    .expect_err("65 checks are refused");
    assert_eq!(
        too_many.to_string(),
        "the acceptance checks were refused: a task carries at most 64 checks"
    );
    assert_eq!(state(&harness, &root).await.revision, 2);
    harness.close(cx()).await.expect("close");
}
