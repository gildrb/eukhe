//! `eukhe.rlm` on a durable Harness: the `ipython` tool streaming into the
//! live tool slot, abort, crash recovery with a revived namespace, and host
//! requests routed with the call context. These run a real Python kernel and
//! skip (with a note) on machines without one, like the kernel tests.

use std::future::Future;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, Instant};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::harness::types::{ConversationAbortOptions, InputSubmissionDraft, ModelRef};
use eukhe_durable::harness::{ConversationEntryQuery, LiveState, ToolSlot, LIVE_DOC};
use eukhe_durable::types::{
    ConversationId, DocumentReaderExt, EntryRecord, SubmissionId, SubmissionStatus,
};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{
    JsonObject, Message, StopReason, ToolResultMessage, UserContent, UserContentBlock,
};
use futures::FutureExt;
use serde_json::{json, Value};
use tempfile::TempDir;

use crate::durable::{
    open_session, EukheSession, HostCall, HostCallHandler, SessionConfig, SessionStorage,
};
use crate::kernel::state_snapshot::manifest_path_in;

/// The kernel Python with eukhe-runtime installed, handed to the sessions'
/// kernels; `None` skips the test.
fn kernel_python() -> Option<PathBuf> {
    let python = find_kernel_python()?;
    let _first_wins = super::kernels::TEST_KERNEL_PYTHON.set(python.clone());
    Some(python)
}

fn find_kernel_python() -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os("EUKHE_CORE_KERNEL_PYTHON") {
        let explicit = PathBuf::from(explicit);
        assert!(
            explicit.exists(),
            "EUKHE_CORE_KERNEL_PYTHON {} not found",
            explicit.display()
        );
        return Some(explicit);
    }
    let candidate = PathBuf::from(std::env::var("HOME").map_or_else(
        |_| "/home/ubuntu/.eukhe/kernel-venv/bin/python".to_string(),
        |home| format!("{home}/.eukhe/kernel-venv/bin/python"),
    ));
    if candidate.exists() {
        return Some(candidate);
    }
    eprintln!(
        "kernel python {} not found; skipping durable ipython test",
        candidate.display()
    );
    None
}

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// Kernel boots and cells run in real time.
const WAIT_MS: u64 = 90_000;

/// Serializes the real-kernel tests: each boots a `CPython` kernel, and
/// several boots at once starve every wait budget under a parallel test
/// run (the daemon tests' `FAUX_TEST_LOCK` pattern).
static KERNEL_TEST_LOCK: tokio::sync::Mutex<()> = tokio::sync::Mutex::const_new(());

/// Hold for the whole body of a real-kernel test.
async fn kernel_test_lock() -> tokio::sync::MutexGuard<'static, ()> {
    KERNEL_TEST_LOCK.lock().await
}

/// Directories, models, and the faux provider of one session that survive a
/// reopen, like a worker host's own objects.
struct Fixture {
    dir: TempDir,
    faux: FauxProviderHandle,
    models: Models,
}

impl Fixture {
    fn new() -> Self {
        let dir = TempDir::new().expect("temp dir");
        for sub in ["agent", "work"] {
            std::fs::create_dir_all(dir.path().join(sub)).expect("fixture dir");
        }
        let faux = faux_provider(RegisterFauxProviderOptions::default());
        let models = create_models(CreateModelsOptions::default());
        models.set_provider(faux.provider.clone());
        Self { dir, faux, models }
    }

    fn storage(&self) -> PathBuf {
        self.dir.path().join("sessions").join("session-1")
    }

    async fn open(&self) -> EukheSession {
        self.open_configured(|_| {}).await
    }

    /// Open with `configure` applied to the config last.
    async fn open_configured(&self, configure: impl FnOnce(&mut SessionConfig)) -> EukheSession {
        let mut config = SessionConfig::new(
            self.dir.path().join("agent"),
            self.dir.path().join("work"),
            "019a0000-0000-7000-8000-000000000001",
            SessionStorage::Jsonl {
                dir: self.storage(),
                fsync: false,
            },
        );
        config.models = Some(self.models.clone());
        config.model = Some(
            ModelRef {
                provider: "faux".to_owned(),
                model_id: "faux-1".to_owned(),
            }
            .into(),
        );
        configure(&mut config);
        open_session(config, cx()).await.expect("session opens")
    }

    /// The namespace snapshot manifest of `conversation`'s kernel (written
    /// after its payload).
    fn manifest_file(&self, conversation: ConversationId) -> PathBuf {
        manifest_path_in(
            self.storage()
                .join("kernels")
                .join(conversation.to_string()),
        )
    }
}

fn ipython(call_id: &str, code: &str) -> FauxResponseStep {
    let Value::Object(arguments) = json!({ "code": code }) else {
        unreachable!("an object literal");
    };
    faux_assistant_message(
        vec![faux_tool_call(
            "ipython",
            arguments.into_iter().collect::<JsonObject>(),
            Some(call_id.to_owned()),
        )],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()
}

fn text(reply: &str) -> FauxResponseStep {
    faux_assistant_message(
        vec![faux_text(reply)],
        FauxAssistantMessageOptions::default(),
    )
    .into()
}

async fn submit(session: &EukheSession, input: &str) -> SubmissionId {
    session
        .root()
        .submit(InputSubmissionDraft::new(input), cx())
        .await
        .expect("submitted")
        .id()
}

async fn settle(session: &EukheSession, id: SubmissionId) -> SubmissionStatus {
    session
        .harness()
        .submission(id, cx())
        .await
        .expect("submission read")
        .expect("the submission exists")
        .wait(cx())
        .await
        .expect("settled")
        .state
        .status()
}

async fn entries(session: &EukheSession) -> Vec<EntryRecord> {
    let page = session
        .root()
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .expect("entries");
    page.items.into_iter().rev().collect()
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

fn result_text(message: &ToolResultMessage) -> String {
    message
        .content
        .iter()
        .map(|item| match item {
            UserContentBlock::Text(text) => text.text.as_str(),
            UserContentBlock::Image(_) => "[image]",
        })
        .collect::<Vec<_>>()
        .join("|")
}

async fn first_slot(session: &EukheSession) -> Option<ToolSlot> {
    let live: LiveState = session
        .harness()
        .snapshot(&LIVE_DOC, session.root().id(), cx())
        .await
        .expect("pi.live")
        .map(|value| from_json(&JsonValue::Object(value)).expect("pi.live decodes"))
        .unwrap_or_default();
    live.tools.and_then(|tools| tools.into_iter().next())
}

async fn wait_for<F, Fut>(what: &str, mut check: F)
where
    F: FnMut() -> Fut,
    Fut: Future<Output = bool>,
{
    let deadline = Instant::now() + Duration::from_millis(WAIT_MS);
    while !check().await {
        assert!(Instant::now() <= deadline, "timed out waiting for {what}");
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
}

async fn wait_for_slot_output(session: &EukheSession, output: &str) {
    wait_for(
        "the cell's streamed output in the pi.live tool slot",
        || async {
            first_slot(session)
                .await
                .and_then(|slot| slot.output)
                .as_deref()
                == Some(output)
        },
    )
    .await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn streams_cell_output_into_the_live_tool_slot_and_answers_with_the_ipython_result() {
    if kernel_python().is_none() {
        return;
    }
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    let gate = fixture.dir.path().join("gate");
    let code = format!(
        "import os, time\nprint('streamed', flush=True)\nwhile not os.path.exists({gate:?}):\n    time.sleep(0.02)\n6 * 7",
        gate = gate.display().to_string()
    );
    fixture
        .faux
        .set_responses(vec![ipython("c1", &code), text("done")]);
    let session = fixture.open().await;
    let id = submit(&session, "go").await;

    wait_for_slot_output(&session, "streamed\n").await;
    let slot = first_slot(&session).await.expect("a running slot");
    assert_eq!(slot.name, "ipython");
    std::fs::write(&gate, "").expect("open the gate");

    assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    let all = entries(&session).await;
    let results = results(&all);
    assert_eq!(results.len(), 1);
    let result = &results[0];
    assert_eq!(result.tool_call_id, "c1");
    assert!(!result.is_error);
    assert_eq!(result_text(result), "streamed\n\n42");
    let details = result.details.clone().expect("details");
    assert_eq!(details["status"], "ok");
    assert_eq!(details["kernelRestarted"], false);
    assert_eq!(details["stdout"], "streamed\n");
    assert_eq!(details["result"], "42");
    assert!(details["durationMs"].is_number());
    session.close(cx()).await.expect("close");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn abort_interrupts_the_running_cell_and_the_kernel_stays_usable() {
    if kernel_python().is_none() {
        return;
    }
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    fixture.faux.set_responses(vec![ipython(
        "c1",
        "import time\nprint('started', flush=True)\ntime.sleep(120)",
    )]);
    let session = fixture.open().await;
    let id = submit(&session, "go").await;
    wait_for_slot_output(&session, "started\n").await;

    let aborted_at = Instant::now();
    session
        .root()
        .abort(ConversationAbortOptions::default(), cx())
        .await
        .expect("abort");
    settle(&session, id).await;
    assert!(
        aborted_at.elapsed() < Duration::from_secs(30),
        "the interrupted cell settled in {:?}",
        aborted_at.elapsed()
    );
    let first = results(&entries(&session).await);
    assert_eq!(first.len(), 1);
    assert!(first[0].is_error, "{first:?}");
    assert!(result_text(&first[0]).starts_with("started\n"), "{first:?}");

    // The interrupt left the kernel idle: the next cell runs at once.
    fixture
        .faux
        .set_responses(vec![ipython("c2", "print(20 + 22)"), text("done")]);
    let next = submit(&session, "again").await;
    assert_eq!(settle(&session, next).await, SubmissionStatus::Done);
    let all = results(&entries(&session).await);
    assert_eq!(all.len(), 2);
    assert_eq!(result_text(&all[1]), "42\n");
    assert!(!all[1].is_error);
    session.close(cx()).await.expect("close");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_crash_mid_cell_answers_interrupted_and_the_reopened_kernel_revives_its_namespace() {
    if kernel_python().is_none() {
        return;
    }
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    fixture.faux.set_responses(vec![
        ipython("c1", "import os\nx = 41\nprint(os.getpid())"),
        text("set"),
    ]);
    let session = fixture.open().await;
    let root = session.root().id();
    let first = submit(&session, "set x").await;
    assert_eq!(settle(&session, first).await, SubmissionStatus::Done);
    let pid = result_text(&results(&entries(&session).await)[0])
        .trim()
        .to_owned();
    // The debounced auto-snapshot after the successful cell. Its manifest
    // must list `x`: a fresh boot's bootstrap schedules its own debounced
    // snapshot, and when the cell's enqueue lags past that debounce (a
    // loaded machine) a skills-only payload lands first. The cell's own
    // snapshot then queues behind the blocking cell below and never
    // lands before the crash, so a bare "the file exists" check would let
    // the reopened kernel revive a namespace without `x`.
    let manifest = fixture.manifest_file(root);
    wait_for("the kernel namespace snapshot holding x", || {
        let saved_x = std::fs::read_to_string(&manifest)
            .ok()
            .and_then(|raw| serde_json::from_str::<Value>(&raw).ok())
            .and_then(|manifest| {
                manifest["savedNames"]
                    .as_array()
                    .map(|names| names.iter().any(|name| name == "x"))
            })
            .unwrap_or(false);
        async move { saved_x }
    })
    .await;

    fixture.faux.set_responses(vec![
        ipython(
            "c2",
            "import time\nprint('started', flush=True)\ntime.sleep(120)",
        ),
        ipython("c3", "print(x + 1)"),
        text("done"),
    ]);
    let second = submit(&session, "block").await;
    wait_for_slot_output(&session, "started\n").await;
    // The worker dies: nothing more commits, and its kernel child dies too.
    session.harness().close(cx()).await.expect("harness close");
    let killed = std::process::Command::new("kill")
        .args(["-9", &pid])
        .status()
        .expect("kill runs");
    if !killed.success() {
        // Under load the harness teardown reaped the child first; the
        // kernel just has to be dead from here on.
        let alive = std::process::Command::new("kill")
            .args(["-0", &pid])
            .status()
            .expect("kill runs")
            .success();
        assert!(!alive, "kernel {pid} survived the crash");
    }
    drop(session);

    let session = fixture.open().await;
    assert_eq!(settle(&session, second).await, SubmissionStatus::Done);
    let all = entries(&session).await;
    let results = results(&all);
    assert_eq!(results.len(), 3, "{results:?}");
    assert_eq!(results[1].tool_call_id, "c2");
    assert!(results[1].is_error);
    assert_eq!(
        result_text(&results[1]),
        "started\n|<harness>\n[error] Tool ipython was interrupted and may have partially run\n</harness>"
    );
    assert_eq!(results[2].tool_call_id, "c3");
    assert_eq!(result_text(&results[2]), "42\n");

    // The model learns the kernel restarted and what came back.
    let notice = all
        .iter()
        .position(|entry| {
            entry.kind == "eukhe.custom"
                && entry
                    .data
                    .as_ref()
                    .and_then(|data| data.get("customType"))
                    .and_then(JsonValue::as_str)
                    == Some("ipython_state_restored")
        })
        .expect("an ipython_state_restored row");
    let Some(Message::User(message)) = all[notice].model.as_ref().and_then(|model| model.first())
    else {
        panic!("the notice reaches the model: {:?}", all[notice]);
    };
    let UserContent::Blocks(blocks) = &message.content else {
        panic!("block content: {message:?}");
    };
    let UserContentBlock::Text(notice_text) = &blocks[0] else {
        panic!("a text block: {blocks:?}");
    };
    assert!(
        notice_text.text.starts_with("[python-state-restored]"),
        "{}",
        notice_text.text
    );
    assert!(notice_text.text.contains('x'), "{}", notice_text.text);
    // The reopen prewarms the kernel (its snapshot exists) or c3 boots it.
    // Which side of the interrupted call the notice lands on depends on
    // whether the harness teardown or the explicit kill reaped the dying
    // kernel first: the prewarmed notice may precede the recovered answer.
    // Both rows exist and reach the model either way (asserted above).
    session.close(cx()).await.expect("close");
}

/// What a probe handler saw: the call id, its conversation, the payload's
/// `n`, and whether the requesting cell's source rode along.
type SeenCall = (Option<String>, Option<ConversationId>, Value, bool);

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn host_requests_reach_their_handlers_with_the_running_tool_call() {
    if kernel_python().is_none() {
        return;
    }
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    let code = "import rlm, json\nprobe = await rlm.host_request('test.probe', {'n': 1})\ninfo = await rlm.host_request('model.info')\nprint(json.dumps([probe, info['provider'], info['id']]))";
    fixture
        .faux
        .set_responses(vec![ipython("c1", code), text("done")]);
    let session = fixture.open().await;
    let seen: Arc<Mutex<Vec<SeenCall>>> = Arc::default();
    let record = Arc::clone(&seen);
    let handler: HostCallHandler = Arc::new(move |call: HostCall| {
        record.lock().unwrap_or_else(PoisonError::into_inner).push((
            call.call.as_ref().map(|api| api.call_id().to_owned()),
            call.call.as_ref().map(|api| api.conversation_id()),
            call.data.get("n").cloned().unwrap_or(Value::Null),
            call.cell_source_code
                .as_deref()
                .is_some_and(|source| source.contains("test.probe")),
        ));
        async { Ok(json!({ "answered": true })) }.boxed()
    });
    session.deps().host_requests.register("test.probe", handler);

    let id = submit(&session, "go").await;
    assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    let all = results(&entries(&session).await);
    assert_eq!(
        result_text(&all[0]),
        "[{\"answered\": true}, \"faux\", \"faux-1\"]\n"
    );
    let seen = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    assert_eq!(
        seen,
        vec![(
            Some("c1".to_owned()),
            Some(session.root().id()),
            json!(1),
            true
        )]
    );
    session.close(cx()).await.expect("close");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn boundary_requests_schedule_and_the_requested_refinement_runs_after_the_tool_round() {
    if kernel_python().is_none() {
        return;
    }
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    let code = "import rlm, json\nstatus = await rlm.host_request('compact.status')\nrun = await rlm.host_request('compact.run')\nrefine = await rlm.host_request('refine.run', {'instructions': 'remember x'})\npending = await rlm.host_request('refine.status')\nprint(json.dumps([status['scheduled'], status['tokens'] is not None, run, refine['scheduled'], pending], sort_keys=True))";
    let proposal = json!({
        "summary": "remember x",
        "rationale": "the user asked",
        "expectedOutcome": "x is remembered",
        "edits": [{
            "action": "create",
            "kind": "memory",
            "title": "x",
            "content": "x is 41",
        }],
    })
    .to_string();
    fixture.faux.set_responses(vec![
        ipython("c1", code),
        // The refinement planner's request, made by the after_tools hook.
        text(&proposal),
        text("done"),
    ]);
    let session = fixture.open().await;
    let id = submit(&session, "go").await;
    assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    let all = entries(&session).await;
    assert_eq!(
        result_text(&results(&all)[0]),
        "[false, true, {\"reason\": \"session is too short to compact\", \"scheduled\": false}, true, {\"in_flight\": false, \"pending\": true}]\n"
    );
    let custom_type = |entry: &EntryRecord| {
        entry
            .data
            .as_ref()
            .and_then(|data| data.get("customType"))
            .and_then(JsonValue::as_str)
            .map(str::to_owned)
    };
    let rows: Vec<(String, Option<String>)> = all
        .iter()
        .filter(|entry| entry.kind.starts_with("eukhe."))
        .map(|entry| (entry.kind.clone(), custom_type(entry)))
        .collect();
    // The harness digest rows ride the cold boundaries: the first request
    // and the request after the refinement updated the harness state.
    assert_eq!(
        rows,
        vec![
            ("eukhe.custom".to_owned(), Some("harness_digest".to_owned())),
            (
                "eukhe.custom-state".to_owned(),
                Some("eukhe.refinement".to_owned())
            ),
            (
                "eukhe.custom".to_owned(),
                Some("refinement_outcome".to_owned())
            ),
            (
                "eukhe.custom".to_owned(),
                Some("refinement_notice".to_owned())
            ),
            ("eukhe.custom".to_owned(), Some("harness_digest".to_owned())),
        ]
    );
    // The rows land between the requesting round and the final answer.
    let notice = all
        .iter()
        .position(|entry| custom_type(entry).as_deref() == Some("refinement_notice"))
        .expect("the notice");
    assert!(all[notice].model.is_some(), "the notice reaches the model");
    assert_eq!(
        all.last().map(|entry| entry.kind.as_str()),
        Some("pi.assistant")
    );
    let boundary = super::boundary::boundary_state(session.harness(), session.root().id(), cx())
        .await
        .expect("boundary doc");
    assert_eq!(boundary.refine, None, "the request is consumed");
    session.close(cx()).await.expect("close");
}

/// The out-of-band kernel lanes never boot a kernel: a conversation whose
/// kernel never started answers the definitive "Kernel is not running".
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn kernel_activity_answers_not_running_without_a_booted_kernel() {
    let fixture = Fixture::new();
    let session = fixture.open().await;
    let bash = super::kernel_bash_activity(
        session.deps(),
        session.root().id(),
        super::BashActivityRequest {
            action: super::BashActivityAction::List,
            activity_id: None,
            lines: 50,
        },
    )
    .await;
    assert!(
        matches!(bash, Err(super::KernelActivityError::NotRunning)),
        "{bash:?}"
    );
    let factory = super::kernel_factory_activity(
        session.deps(),
        session.root(),
        crate::session_engine::factory_host::FactoryActivityRequest::parse(
            "graph", None, None, None,
        )
        .expect("a valid request"),
        cx(),
    )
    .await;
    let error = factory.expect_err("no kernel");
    assert_eq!(error.to_string(), "Kernel is not running");
    session.close(cx()).await.expect("close");
}

/// After a cell booted the conversation's kernel, the bash lane reaches its
/// handle registry (the catalog lists the background handle; an unknown
/// handle is the kernel's own refusal).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn kernel_bash_activity_reaches_the_booted_kernel() {
    if kernel_python().is_none() {
        return;
    }
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    fixture.faux.set_responses(vec![
        ipython("c1", "handle = bash('sleep 30')\nprint(handle.pid > 0)"),
        text("done"),
    ]);
    let session = fixture.open().await;
    let id = submit(&session, "go").await;
    assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    let request = |action, activity_id: Option<&str>| super::BashActivityRequest {
        action,
        activity_id: activity_id.map(str::to_owned),
        lines: 20,
    };
    let listed = super::kernel_bash_activity(
        session.deps(),
        session.root().id(),
        request(super::BashActivityAction::List, None),
    )
    .await
    .expect("list");
    let rows = listed["activities"].as_array().expect("activities").clone();
    assert_eq!(rows.len(), 1, "{listed}");
    assert_eq!(rows[0]["status"], "running");
    let activity_id = rows[0]["id"].as_str().expect("activity id").to_owned();
    let killed = super::kernel_bash_activity(
        session.deps(),
        session.root().id(),
        request(super::BashActivityAction::Kill, Some(&activity_id)),
    )
    .await
    .expect("kill");
    assert_eq!(killed["status"], "ok", "{killed}");
    let unknown = super::kernel_bash_activity(
        session.deps(),
        session.root().id(),
        request(super::BashActivityAction::Tail, Some("no-such-handle")),
    )
    .await;
    assert!(
        matches!(unknown, Err(super::KernelActivityError::Failed(_))),
        "{unknown:?}"
    );
    session.close(cx()).await.expect("close");
}

/// A factory `run` is preflighted before the kernel is asked: a spec whose
/// declared model resolves nowhere fails loudly even with no kernel booted;
/// a spec the host cannot read passes through to the kernel lane.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn kernel_factory_run_is_preflighted_before_the_kernel() {
    use crate::refinement::{
        empty_harness_state, save_harness_state, HarnessEntry, RefinementKind,
    };
    let fixture = Fixture::new();
    let agent_dir = fixture.dir.path().join("agent");
    let mut state = empty_harness_state();
    state.schema = 1;
    let spec = json!({ "machine": {
        "run": { "max_parallel": 1 },
        "states": [{ "id": "work", "entry": true,
                     "subagent": { "prompt": "Do it.", "model": "nowhere/missing-model" } }]
    } });
    state
        .entries
        .get_mut(&RefinementKind::Factory)
        .expect("factory entries")
        .insert(
            "doomed".to_owned(),
            HarnessEntry {
                id: "doomed".to_owned(),
                kind: RefinementKind::Factory,
                title: "doomed".to_owned(),
                content: "content".to_owned(),
                path: String::new(),
                scope: None,
                reference: serde_json::Map::new(),
                arguments: spec.as_object().cloned().expect("object"),
                metadata: serde_json::Map::new(),
                source: "test".to_owned(),
                created_at: "2026-01-01T00:00:00Z".to_owned(),
                updated_at: "2026-01-01T00:00:00Z".to_owned(),
                version: 1,
            },
        );
    save_harness_state(
        &crate::refinement::get_global_harness_state_dir(&agent_dir),
        &state,
    )
    .expect("harness state");
    let session = fixture.open().await;
    let run = |spec_id: &str| {
        crate::session_engine::factory_host::FactoryActivityRequest::parse(
            "run",
            None,
            Some(spec_id),
            None,
        )
        .expect("a valid request")
    };
    let doomed =
        super::kernel_factory_activity(session.deps(), session.root(), run("doomed"), cx()).await;
    match doomed {
        Err(super::KernelActivityError::Failed(error)) => {
            assert!(format!("{error:#}").contains("missing-model"), "{error:#}");
        }
        other => panic!("the preflight must refuse: {other:?}"),
    }
    let unknown =
        super::kernel_factory_activity(session.deps(), session.root(), run("unknown"), cx()).await;
    assert!(
        matches!(unknown, Err(super::KernelActivityError::NotRunning)),
        "{unknown:?}"
    );
    session.close(cx()).await.expect("close");
}

/// The root conversation's kernel in the session's pool, when one was
/// created (never creates one).
fn root_kernel(session: &EukheSession) -> Option<super::kernels::ConversationKernel> {
    session
        .deps()
        .rlm_kernels
        .get()
        .and_then(std::sync::Weak::upgrade)
        .and_then(|pool| pool.existing(session.root().id()))
}

async fn wait_for_prewarmed_boot(session: &EukheSession) -> i32 {
    wait_for("the prewarmed kernel boot", || {
        let running =
            root_kernel(session).is_some_and(|kernel| kernel.provisioner.has_running_kernel());
        async move { running }
    })
    .await;
    root_kernel(session)
        .and_then(|kernel| kernel.provisioner.manager())
        .and_then(|manager| manager.process_id())
        .expect("the prewarmed kernel's pid")
}

fn process_alive(pid: i32) -> bool {
    std::process::Command::new("kill")
        .args(["-0", &pid.to_string()])
        .status()
        .expect("kill runs")
        .success()
}

/// The daemon's prewarm (TS `prewarmIpythonKernel`): a top-level session
/// that asks for it boots its kernel at open with no `ipython` call, so a
/// compaction with no tool use still lands the hidden `ipython_state`
/// notice (the old engine's `kernel_prewarm` contract on the durable pool).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_prewarmed_root_boots_at_open_and_its_compaction_lands_the_state_notice() {
    if kernel_python().is_none() {
        return;
    }
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    // A tiny keep window so the short conversation still finds a cut.
    std::fs::write(
        fixture.dir.path().join("agent").join("settings.json"),
        r#"{"compaction":{"keepRecentTokens":1}}"#,
    )
    .expect("settings file");
    let session = fixture
        .open_configured(|config| config.prewarm_kernel = true)
        .await;
    wait_for_prewarmed_boot(&session).await;

    // Plain text turns (no tool use), then the summarizer's reply.
    fixture.faux.set_responses(vec![
        text("history one noted"),
        text("history two noted"),
        text("the compaction summary"),
    ]);
    for prompt in ["history turn one", "history turn two"] {
        let id = submit(&session, prompt).await;
        assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    }
    assert!(results(&entries(&session).await).is_empty(), "no tool use");
    session.root().compact(None, cx()).await.expect("compact");
    session.root().wait_for_idle(cx()).await.expect("idle");

    let notice = || async {
        entries(&session).await.into_iter().find(|entry| {
            entry.kind == "eukhe.custom"
                && entry
                    .data
                    .as_ref()
                    .and_then(|data| data.get("customType"))
                    .and_then(JsonValue::as_str)
                    == Some("ipython_state")
        })
    };
    wait_for("the post-compaction ipython_state notice", || async {
        notice().await.is_some()
    })
    .await;
    let row = notice().await.expect("the notice row");
    let Some(Message::User(message)) = row.model.as_ref().and_then(|model| model.first()) else {
        panic!("the notice reaches the model: {row:?}");
    };
    let text = match &message.content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.as_str()),
                UserContentBlock::Image(_) => None,
            })
            .collect(),
    };
    assert!(text.contains("[python-state]"), "{text}");
    assert!(
        text.contains("Your Python kernel persisted through compaction"),
        "{text}"
    );
    session.close(cx()).await.expect("close");
}

/// The TS depth gate: a subagent session keeps the lazy first-call start
/// despite the prewarm flag, and a fresh root without the flag (and
/// without a snapshot) stays lazy too. The prewarm decision is made while
/// the session opens (a firing prewarm creates the conversation's kernel
/// before `open_session` returns), so an empty pool right after open is
/// conclusive.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn subagents_and_unflagged_roots_stay_lazy() {
    let fixture = Fixture::new();
    let subagent = fixture
        .open_configured(|config| {
            config.prewarm_kernel = true;
            config.role.rlm_depth = 1;
        })
        .await;
    assert!(
        root_kernel(&subagent).is_none(),
        "a depth-1 session must not prewarm"
    );
    subagent.close(cx()).await.expect("close");

    let fixture = Fixture::new();
    let unflagged = fixture.open().await;
    assert!(
        root_kernel(&unflagged).is_none(),
        "a fresh root without the flag stays lazy"
    );
    unflagged.close(cx()).await.expect("close");
}

/// Closing a session takes its prewarmed kernel process down (the old
/// engine's `kernel_teardown` prewarm contract on the durable pool).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn closing_a_session_kills_its_prewarmed_kernel_process() {
    if kernel_python().is_none() {
        return;
    }
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    let session = fixture
        .open_configured(|config| config.prewarm_kernel = true)
        .await;
    let pid = wait_for_prewarmed_boot(&session).await;
    assert!(process_alive(pid), "the prewarmed kernel {pid} runs");
    session.close(cx()).await.expect("close");
    wait_for("the prewarmed kernel process to exit", || {
        let alive = process_alive(pid);
        async move { !alive }
    })
    .await;
}
