//! `eukhe.children` over a fake [`RlmSubagentHost`]: spawn to report,
//! exactly one report across a reopen, delete, collect, and the depth limit.

use std::collections::HashMap;
use std::future::Future;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::errors::{StorageError, StorageRejected};
use eukhe_durable::harness::define::{define_extension, define_tool};
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, Extension, FieldChange, HarnessOptions, InputSubmissionDraft, ModelRef,
    ToolExecutionResult, ToolRegistration,
};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use eukhe_durable::session::SessionError;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{
    AnyTaskRecord, ConversationId, ConversationQuery, ConversationRecord, Cursor, DocumentAddress,
    DocumentId, DocumentPoint, DocumentQuery, DocumentRecord, EntryId, EntryQuery, EntryRecord,
    Page, Seq, Storage, StorageWrite, StoredDocument, StoredEntry, SubmissionId, SubmissionQuery,
    SubmissionRecord, TaskId, TaskOutcome, TaskQuery, TaskState, ROOT_CONVERSATION_ID,
};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_tool_call, FauxAssistantMessageOptions,
    FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::typebox::{TSchema, Type};
use eukhe_types::pi_ai::{
    JsonObject, Message, StopReason, TextContent, Usage, UsageCost, UserContent, UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::{json, Value};

use super::registry::{read_children, ChildRow, ChildStatus, CHILD_USAGE_KEY};
use super::task::{report_request_id, CHILD_TASK_KIND};
use super::{
    Children, ChildrenConfig, RlmChildCancelRequest, RlmChildDeleteRequest, RlmChildListing,
    RlmChildObservation, RlmChildPromptRequest, RlmChildRunState, RlmChildSession,
    RlmChildSpawnRequest, RlmChildWaitRequest, RlmCreateSessionHandle, RlmCreateSessionRequest,
    RlmHostFuture, RlmSubagentHost,
};
use crate::durable::deps::{HarnessCell, HostCall, HostRequestRegistry};

const PARENT_SESSION_ID: &str = "parent-session";
const PROMPT: &str = "Investigate the flaky test";

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

// ---------------------------------------------------------------------------
// Fake host
// ---------------------------------------------------------------------------

#[derive(Default)]
struct FakeState {
    spawns: Vec<RlmChildSpawnRequest>,
    prompts: Vec<RlmChildPromptRequest>,
    cancels: Vec<RlmChildCancelRequest>,
    deletes: Vec<RlmChildDeleteRequest>,
    outcomes: HashMap<String, RlmChildRunState>,
    usage: HashMap<String, Usage>,
}

/// A supervisor stand-in: children settle when the test says so.
struct FakeHost {
    state: Mutex<FakeState>,
    changed: tokio::sync::watch::Sender<u64>,
}

impl FakeHost {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            state: Mutex::new(FakeState::default()),
            changed: tokio::sync::watch::Sender::new(0),
        })
    }

    fn settle(&self, session_id: &str, state: RlmChildRunState, usage: Option<Usage>) {
        {
            let mut fake = lock(&self.state);
            fake.outcomes.insert(session_id.to_owned(), state);
            if let Some(usage) = usage {
                fake.usage.insert(session_id.to_owned(), usage);
            }
        }
        self.changed.send_modify(|value| *value += 1);
    }

    fn spawn_keys(&self) -> Vec<String> {
        lock(&self.state)
            .spawns
            .iter()
            .map(|spawn| spawn.idempotency_key.clone())
            .collect()
    }

    fn prompt_keys(&self) -> Vec<String> {
        lock(&self.state)
            .prompts
            .iter()
            .map(|prompt| prompt.idempotency_key.clone())
            .collect()
    }
}

impl RlmSubagentHost for FakeHost {
    fn spawn(&self, request: RlmChildSpawnRequest) -> RlmHostFuture<'_, RlmChildSession> {
        let session = RlmChildSession {
            active_session_id: format!("active-{}", request.child.rlm_child_id),
            session_id: request.child.session_id.clone(),
            session_name: request.name.clone(),
            session_dir: format!("/children/{}", request.child.rlm_child_id),
            model: request
                .model
                .clone()
                .unwrap_or_else(|| "faux/faux-1".to_owned()),
        };
        lock(&self.state).spawns.push(request);
        Box::pin(async move { Ok(session) })
    }

    fn create_session(
        &self,
        request: RlmCreateSessionRequest,
    ) -> RlmHostFuture<'_, RlmCreateSessionHandle> {
        Box::pin(async move {
            Ok(RlmCreateSessionHandle {
                active_session_id: "resident".to_owned(),
                session_id: "resident".to_owned(),
                name: request.name.unwrap_or_else(|| "resident".to_owned()),
                session_file: String::new(),
                model: "faux/faux-1".to_owned(),
            })
        })
    }

    fn prompt(&self, request: RlmChildPromptRequest) -> RlmHostFuture<'_, ()> {
        lock(&self.state).prompts.push(request);
        Box::pin(async { Ok(()) })
    }

    fn wait_settled(&self, request: RlmChildWaitRequest) -> RlmHostFuture<'_, RlmChildObservation> {
        Box::pin(async move {
            let mut changed = self.changed.subscribe();
            let wait = async {
                loop {
                    {
                        let fake = lock(&self.state);
                        if let Some(state) = fake.outcomes.get(&request.session_id) {
                            return RlmChildObservation {
                                state: state.clone(),
                                usage: fake.usage.get(&request.session_id).copied(),
                            };
                        }
                    }
                    if changed.changed().await.is_err() {
                        std::future::pending::<()>().await;
                    }
                }
            };
            let budget = Duration::from_millis(request.timeout_ms);
            Ok(tokio::time::timeout(budget, wait)
                .await
                .unwrap_or(RlmChildObservation {
                    state: RlmChildRunState::Running,
                    usage: None,
                }))
        })
    }

    fn cancel(&self, request: RlmChildCancelRequest) -> RlmHostFuture<'_, ()> {
        lock(&self.state).cancels.push(request);
        Box::pin(async { Ok(()) })
    }

    fn delete(&self, request: RlmChildDeleteRequest) -> RlmHostFuture<'_, ()> {
        lock(&self.state).deletes.push(request);
        Box::pin(async { Ok(()) })
    }

    fn list(&self) -> RlmHostFuture<'_, Vec<RlmChildListing>> {
        Box::pin(async { Ok(Vec::new()) })
    }
}

// ---------------------------------------------------------------------------
// Storage that can refuse the child task's terminal commit
// ---------------------------------------------------------------------------

/// Delegates to `inner`; while `refuse_terminal` is set, rejects any commit
/// that ends an `eukhe.rlm.child` task (a crash between the report
/// submission and the terminal commit). `close` keeps `inner` open so a
/// second Harness can reopen the same records.
struct GatedStorage {
    inner: Arc<MemoryStorage>,
    refuse_terminal: AtomicBool,
    refused: AtomicUsize,
}

fn ends_child_task(write: &StorageWrite) -> bool {
    match write {
        StorageWrite::Task { value } => {
            value.kind == CHILD_TASK_KIND
                && matches!(
                    value.state,
                    TaskState::Completing { .. } | TaskState::Terminal { .. }
                )
        }
        _ => false,
    }
}

impl Storage for GatedStorage {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        if self.refuse_terminal.load(Ordering::SeqCst) && writes.iter().any(ends_child_task) {
            self.refused.fetch_add(1, Ordering::SeqCst);
            return futures::future::ready(Err(StorageError::Rejected(StorageRejected::new(
                "the child task's terminal commit is refused",
            ))))
            .boxed();
        }
        self.inner.commit(writes, cx)
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        self.inner.mint_id()
    }

    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>> {
        self.inner.conversation(id, cx)
    }

    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>> {
        self.inner.scan_conversations(query, limit, cursor, cx)
    }

    fn entry<'a>(
        &'a self,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.inner.entry(id, cx)
    }

    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.inner.entry_in(conversation_id, id, cx)
    }

    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>> {
        self.inner
            .find_latest_head_marker(conversation_id, at_or_before_entry_id, cx)
    }

    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>> {
        self.inner.scan_entries(query, limit, cursor, cx)
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        self.inner.task(id, cx)
    }

    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>> {
        self.inner.scan_tasks(query, limit, cursor, cx)
    }

    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.inner.submission(id, cx)
    }

    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>> {
        self.inner.scan_submissions(query, limit, cursor, cx)
    }

    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.inner
            .submission_by_request(conversation_id, request_id, cx)
    }

    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>> {
        self.inner.find_document(address, at, cx)
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
        self.inner.document(id, at, cx)
    }

    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>> {
        self.inner.scan_documents(query, limit, cursor, cx)
    }

    fn close<'a>(&'a self, _cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        futures::future::ready(Ok(())).boxed()
    }
}

// ---------------------------------------------------------------------------
// Session fixture
// ---------------------------------------------------------------------------

/// Models and faux provider that outlive a reopen (the host process's).
struct Setup {
    faux: FauxProviderHandle,
    models: Models,
    reports: Arc<Mutex<Vec<SessionError>>>,
}

fn setup() -> Setup {
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    Setup {
        faux,
        models,
        reports: Arc::new(Mutex::new(Vec::new())),
    }
}

struct Opened {
    harness: Harness,
    root: Conversation,
    requests: HostRequestRegistry,
}

/// A tool whose call runs the kernel's `rlm.spawn` host request.
fn spawn_tool(requests: HostRequestRegistry) -> Arc<Extension> {
    let parameters: TSchema = Type::object(Vec::<(String, TSchema)>::new());
    let tool = define_tool(ToolRegistration::new(
        "spawn",
        "Spawn one RLM child",
        parameters,
        move |_args, api, _cx| {
            let handler = requests.get("rlm.run").expect("rlm.run is registered");
            async move {
                let reply = handler(HostCall {
                    data: json!({ "prompt": PROMPT }),
                    cell_source_code: None,
                    call: Some(api),
                })
                .await;
                let text = match reply {
                    Ok(value) => value.to_string(),
                    Err(error) => format!("error: {error:#}"),
                };
                Ok(ToolExecutionResult {
                    content: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
                    ..ToolExecutionResult::default()
                })
            }
        },
    ));
    define_extension(Extension {
        tools: vec![tool],
        ..Extension::named("test.spawn")
    })
}

async fn open(storage: Arc<dyn Storage>, setup: &Setup, host: Arc<FakeHost>) -> Opened {
    let cell = HarnessCell::default();
    let requests = HostRequestRegistry::default();
    let children = Children::new(ChildrenConfig {
        host: Some(host),
        parent_session_id: PARENT_SESSION_ID.to_owned(),
        rlm_depth: 0,
        rlm_max_depth: 2,
        harness: cell.clone(),
        models: setup.models.clone(),
    });
    let registry = create_registry();
    registry.install(children.install(&requests)).unwrap();
    registry.install(spawn_tool(requests.clone())).unwrap();
    let mut options = HarnessOptions::new(setup.models.clone(), Arc::new(registry));
    let reports = Arc::clone(&setup.reports);
    options.on_report = Some(Arc::new(move |error| lock(&reports).push(error)));
    let harness = Harness::open(storage, options, cx()).await.unwrap();
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
        .unwrap();
    cell.set(harness.clone(), root.clone());
    harness.resume().unwrap();
    Opened {
        harness,
        root,
        requests,
    }
}

fn answer(text: &str) -> FauxResponseStep {
    FauxResponseStep::Message(Box::new(faux_assistant_message(
        text,
        FauxAssistantMessageOptions::default(),
    )))
}

fn call_spawn() -> FauxResponseStep {
    FauxResponseStep::Message(Box::new(faux_assistant_message(
        faux_tool_call("spawn", JsonObject::new(), None),
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )))
}

/// Run one parent turn that spawns a child; returns its registry row.
async fn spawn_child(opened: &Opened, setup: &Setup) -> ChildRow {
    setup
        .faux
        .append_responses(vec![call_spawn(), answer("spawned")]);
    let submission = opened
        .root
        .submit(
            InputSubmissionDraft {
                request_id: None,
                content: UserContent::Text("go".to_owned()),
                when_busy: None,
            },
            cx(),
        )
        .await
        .unwrap();
    submission.wait(cx()).await.unwrap();
    let state = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap();
    state
        .children
        .values()
        .last()
        .cloned()
        .expect("the spawn admitted a child")
}

async fn eventually<F, Fut>(mut check: F)
where
    F: FnMut() -> Fut,
    Fut: Future<Output = bool>,
{
    let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
    while !check().await {
        assert!(
            tokio::time::Instant::now() < deadline,
            "condition was not reached"
        );
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
}

async fn row_of(harness: &Harness, task_id: u64) -> Option<ChildRow> {
    read_children(harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .get(&task_id.to_string())
        .cloned()
}

/// User texts of the root conversation that start with `prefix`.
async fn user_texts(root: &Conversation, prefix: &str) -> Vec<String> {
    let page = root
        .entries(ConversationEntryQuery::default(), 1000, None, cx())
        .await
        .unwrap();
    page.items
        .iter()
        .filter_map(|entry| entry.model.as_ref())
        .flatten()
        .filter_map(|message| match message {
            Message::User(user) => match &user.content {
                UserContent::Text(text) => Some(text.clone()),
                UserContent::Blocks(blocks) => blocks.iter().find_map(|block| match block {
                    UserContentBlock::Text(text) => Some(text.text.clone()),
                    UserContentBlock::Image(_) => None,
                }),
            },
            _ => None,
        })
        .filter(|text| text.starts_with(prefix))
        .collect()
}

async fn handle(opened: &Opened, request_type: &str, data: Value) -> anyhow::Result<Value> {
    let handler = opened
        .requests
        .get(request_type)
        .expect("the handler is registered");
    handler(HostCall {
        data,
        cell_source_code: None,
        call: None,
    })
    .await
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn spawn_reports_once_across_a_reopen_between_submit_and_terminal() {
    let setup = setup();
    let host = FakeHost::new();
    let storage = Arc::new(GatedStorage {
        inner: Arc::new(MemoryStorage::new()),
        refuse_terminal: AtomicBool::new(false),
        refused: AtomicUsize::new(0),
    });
    let first = open(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &setup,
        Arc::clone(&host),
    )
    .await;
    let row = spawn_child(&first, &setup).await;
    let task_id = row.task_id;
    assert_eq!(host.spawn_keys(), [format!("rlm:{task_id}:spawn")]);
    assert_eq!(row.status, ChildStatus::Running);
    assert_eq!(
        row.session_dir.as_deref(),
        Some(&*format!("/children/{}", row.rlm_child_id))
    );
    let spawn = lock(&host.state).spawns[0].clone();
    assert_eq!(spawn.child.session_id, row.session_id);
    assert_eq!(spawn.prompt, PROMPT);
    assert_eq!(spawn.depth, 1);
    eventually(|| async { host.prompt_keys() == [format!("rlm:{task_id}:prompt")] }).await;

    // The child settles; the report lands, but its terminal commit is lost.
    storage.refuse_terminal.store(true, Ordering::SeqCst);
    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(
        &row.session_id,
        RlmChildRunState::Settled {
            answer_preview: Some("the flake is a race".to_owned()),
            replied_since_task: false,
        },
        None,
    );
    let request_id = report_request_id(TaskId::from_number(task_id));
    eventually(|| async { storage.refused.load(Ordering::SeqCst) > 0 }).await;
    assert!(storage
        .inner
        .submission_by_request(ROOT_CONVERSATION_ID, &request_id, cx())
        .await
        .unwrap()
        .is_some());
    first.root.wait_for_idle(cx()).await.unwrap();
    let report = format!(
        "[child-exited: no-reply child:{}]\n\nLast assistant text: the flake is a race",
        row.session_name
    );
    assert_eq!(
        user_texts(&first.root, "[child-exited").await,
        std::slice::from_ref(&report)
    );
    first.harness.close(cx()).await.unwrap();
    // The only failures are the refused terminal commits (each rerun of the
    // report phase found its submission by request id).
    let reports = lock(&setup.reports).clone();
    assert!(!reports.is_empty());
    assert!(reports.iter().all(|error| error
        .to_string()
        .contains("the child task's terminal commit is refused")));
    lock(&setup.reports).clear();
    let stored = storage
        .inner
        .task(TaskId::from_number(task_id), cx())
        .await
        .unwrap()
        .expect("the child task is stored");
    assert_eq!(
        stored.state.status(),
        eukhe_durable::types::TaskStatus::Running
    );
    assert_eq!(
        stored
            .state
            .checkpoint()
            .and_then(|checkpoint| checkpoint.get("phase")),
        Some(&eukhe_chord::json::JsonValue::from("report"))
    );

    // The reopened parent reruns the report phase: one report, then terminal.
    storage.refuse_terminal.store(false, Ordering::SeqCst);
    let second = open(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &setup,
        Arc::clone(&host),
    )
    .await;
    let settled = second
        .harness
        .wait_for_task(TaskId::<Value>::from_number(task_id), cx())
        .await
        .unwrap();
    assert_eq!(
        settled.outcome,
        TaskOutcome::Completed {
            result: eukhe_chord::json::to_json(&ChildStatus::Done).unwrap()
        }
    );
    second.root.wait_for_idle(cx()).await.unwrap();
    assert_eq!(user_texts(&second.root, "[child-exited").await, [report]);
    let row = row_of(&second.harness, task_id).await.unwrap();
    assert!(row.settled);
    assert_eq!(row.status, ChildStatus::Done);
    assert_eq!(host.spawn_keys().len(), 1);
    assert!(lock(&setup.reports).is_empty());
    second.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn delete_aborts_the_child_task_and_reports_the_cancellation() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let row = spawn_child(&opened, &setup).await;
    let task_id = row.task_id;
    eventually(|| async { !host.prompt_keys().is_empty() }).await;
    setup.faux.append_responses(vec![answer("ok")]);

    let deleted = handle(
        &opened,
        "rlm.delete_subagent",
        json!({ "target": row.rlm_child_id }),
    )
    .await
    .unwrap();
    assert_eq!(deleted["outcome"], "deleted");
    assert_eq!(deleted["subagent"]["rlm_child_id"], json!(row.rlm_child_id));
    assert_eq!(deleted["subagent"]["status"], "cancelled");
    let settled = opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(task_id), cx())
        .await
        .unwrap();
    assert!(matches!(
        settled.outcome,
        TaskOutcome::Aborted { ref reason, .. }
            if reason.as_deref() == Some("Deleted by parent orchestrator")
    ));
    {
        let fake = lock(&host.state);
        assert_eq!(
            fake.deletes
                .iter()
                .map(|delete| delete.idempotency_key.clone())
                .collect::<Vec<_>>(),
            [format!("rlm:{task_id}:delete")]
        );
        assert!(
            fake.cancels.is_empty(),
            "a delete tears the child down itself"
        );
    }
    opened.root.wait_for_idle(cx()).await.unwrap();
    assert_eq!(
        user_texts(&opened.root, "[child-exited").await,
        [format!(
            "[child-exited: cancelled child:{}]\n\nDeleted by parent orchestrator",
            row.session_name
        )]
    );

    let listed = handle(&opened, "rlm.list_subagents", json!({}))
        .await
        .unwrap();
    assert_eq!(listed, json!({ "subagents": [] }));
    let collected = handle(
        &opened,
        "rlm.collect",
        json!({ "targets": [row.rlm_child_id] }),
    )
    .await
    .unwrap();
    let result = &collected["results"][0];
    assert_eq!(result["status"], "cancelled");
    assert_eq!(result["settled"], true);
    assert_eq!(result["error"], "Deleted by parent orchestrator");
    let missing = handle(
        &opened,
        "rlm.delete_subagent",
        json!({ "target": row.rlm_child_id }),
    )
    .await
    .unwrap_err();
    assert_eq!(
        missing.to_string(),
        format!(
            "No direct RLM subagent matches \"{}\" in the current parent session",
            row.rlm_child_id
        )
    );
    assert!(lock(&setup.reports).is_empty());
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn collect_waits_for_the_child_to_settle_and_attributes_its_usage() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let row = spawn_child(&opened, &setup).await;
    eventually(|| async { !host.prompt_keys().is_empty() }).await;

    let snapshot = handle(&opened, "rlm.collect", json!({})).await.unwrap();
    assert_eq!(snapshot["results"][0]["status"], "running");
    assert_eq!(snapshot["results"][0]["settled"], false);

    let collecting = {
        let handler = opened.requests.get("rlm.collect").unwrap();
        let target = row.session_name.clone();
        tokio::spawn(handler(HostCall {
            data: json!({ "targets": [target], "timeout_ms": 30_000 }),
            cell_source_code: None,
            call: None,
        }))
    };
    tokio::time::sleep(Duration::from_millis(50)).await;
    assert!(
        !collecting.is_finished(),
        "collect waits for the running child"
    );
    let usage = Usage {
        input: 100,
        output: 20,
        total_tokens: 120,
        cost: UsageCost {
            total: 0.5,
            ..UsageCost::default()
        },
        ..Usage::default()
    };
    setup.faux.append_responses(vec![answer("thanks")]);
    host.settle(
        &row.session_id,
        RlmChildRunState::Settled {
            answer_preview: Some("done".to_owned()),
            replied_since_task: false,
        },
        Some(usage),
    );
    let collected = collecting.await.unwrap().unwrap();
    assert_eq!(
        collected["results"][0],
        json!({
            "rlm_child_id": row.rlm_child_id,
            "session_name": row.session_name,
            "session_dir": format!("/children/{}", row.rlm_child_id),
            "status": "done",
            "settled": true,
            "answer_preview": "done",
            "duration_ms": collected["results"][0]["duration_ms"],
        })
    );
    let totals = opened.harness.usage(cx()).await.unwrap();
    assert_eq!(totals.tools.get(CHILD_USAGE_KEY), Some(&usage));
    let row = row_of(&opened.harness, row.task_id).await.unwrap();
    assert_eq!(row.usage, Some(usage));
    assert!(lock(&setup.reports).is_empty());
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test]
async fn spawn_at_the_depth_limit_errors_as_today() {
    let setup = setup();
    let requests = HostRequestRegistry::default();
    Children::new(ChildrenConfig {
        host: Some(FakeHost::new()),
        parent_session_id: PARENT_SESSION_ID.to_owned(),
        rlm_depth: 2,
        rlm_max_depth: 2,
        harness: HarnessCell::default(),
        models: setup.models.clone(),
    })
    .install(&requests);
    let handler = requests.get("rlm.run").unwrap();
    let error = handler(HostCall {
        data: json!({ "prompt": PROMPT }),
        cell_source_code: None,
        call: None,
    })
    .await
    .unwrap_err();
    assert_eq!(
        error.to_string(),
        "RLM recursion depth limit reached (RLM_DEPTH=2, RLM_MAX_DEPTH=2)"
    );

    let requests = HostRequestRegistry::default();
    Children::new(ChildrenConfig {
        host: None,
        parent_session_id: PARENT_SESSION_ID.to_owned(),
        rlm_depth: 0,
        rlm_max_depth: 2,
        harness: HarnessCell::default(),
        models: setup.models,
    })
    .install(&requests);
    let handler = requests.get("rlm.run").unwrap();
    let error = handler(HostCall {
        data: json!({ "prompt": PROMPT, "kwargs": { "colour": "red" } }),
        cell_source_code: None,
        call: None,
    })
    .await
    .unwrap_err();
    assert_eq!(error.to_string(), "Unsupported rlm.spawn kwargs: colour");
    let error = handler(HostCall {
        data: json!({ "prompt": PROMPT }),
        cell_source_code: None,
        call: None,
    })
    .await
    .unwrap_err();
    assert_eq!(
        error.to_string(),
        "rlm.spawn requires a daemon-backed session: this session has no RLM child runtime"
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cancel_child_aborts_the_run_and_lists_it_cancelled() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let row = spawn_child(&opened, &setup).await;
    let task_id = row.task_id;
    eventually(|| async { !host.prompt_keys().is_empty() }).await;

    let unknown = super::cancel_child(&opened.harness, ROOT_CONVERSATION_ID, "nobody", cx())
        .await
        .unwrap();
    assert_eq!(unknown, None);
    let cancelled =
        super::cancel_child(&opened.harness, ROOT_CONVERSATION_ID, &row.rlm_child_id, cx())
            .await
            .unwrap()
            .unwrap();
    assert_eq!(cancelled.rlm_child_id, row.rlm_child_id);
    assert_eq!(cancelled.status, "cancelled");
    assert_eq!(
        lock(&host.state)
            .cancels
            .iter()
            .map(|cancel| cancel.idempotency_key.clone())
            .collect::<Vec<_>>(),
        [format!("rlm:{task_id}:cancel")]
    );
    let again =
        super::cancel_child(&opened.harness, ROOT_CONVERSATION_ID, &row.rlm_child_id, cx())
            .await
            .unwrap();
    assert_eq!(again, None, "a settled child has no run to cancel");

    let listed = super::list_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap();
    assert_eq!(listed.len(), 1);
    assert_eq!(listed[0].entry.status, "cancelled");
    assert!(listed[0].settled);
    let found = super::find_child(&opened.harness, ROOT_CONVERSATION_ID, &row.session_name, cx())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(found, listed[0]);
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn max_depth_override_reaches_the_spawned_child() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    assert_eq!(
        super::read_max_depth_override(&opened.harness, ROOT_CONVERSATION_ID, cx())
            .await
            .unwrap(),
        None
    );
    super::set_max_depth_override(&opened.harness, ROOT_CONVERSATION_ID, Some(5), cx())
        .await
        .unwrap();
    assert_eq!(
        super::read_max_depth_override(&opened.harness, ROOT_CONVERSATION_ID, cx())
            .await
            .unwrap(),
        Some(5)
    );
    spawn_child(&opened, &setup).await;
    eventually(|| async { !host.spawn_keys().is_empty() }).await;
    assert_eq!(lock(&host.state).spawns[0].max_depth, 5);

    super::set_max_depth_override(&opened.harness, ROOT_CONVERSATION_ID, None, cx())
        .await
        .unwrap();
    assert_eq!(
        super::read_max_depth_override(&opened.harness, ROOT_CONVERSATION_ID, cx())
            .await
            .unwrap(),
        None
    );
    opened.harness.close(cx()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn delete_inactive_child_refuses_a_running_child_and_deletes_a_settled_one() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let row = spawn_child(&opened, &setup).await;
    eventually(|| async { !host.prompt_keys().is_empty() }).await;

    let missing = super::delete_inactive_child(
        &opened.harness,
        host.as_ref(),
        ROOT_CONVERSATION_ID,
        "nobody",
        cx(),
    )
    .await
    .unwrap();
    assert_eq!(missing, super::DeleteChildOutcome::NotFound);
    let running = super::delete_inactive_child(
        &opened.harness,
        host.as_ref(),
        ROOT_CONVERSATION_ID,
        &row.rlm_child_id,
        cx(),
    )
    .await
    .unwrap();
    assert_eq!(running, super::DeleteChildOutcome::Running);
    assert!(lock(&host.state).deletes.is_empty());

    setup.faux.append_responses(vec![answer("noted")]);
    host.settle(
        &row.session_id,
        RlmChildRunState::Settled {
            answer_preview: Some("done".to_owned()),
            replied_since_task: false,
        },
        None,
    );
    let task_id = row.task_id;
    eventually(|| async {
        row_of(&opened.harness, task_id)
            .await
            .is_some_and(|row| row.settled)
    })
    .await;
    let deleted = super::delete_inactive_child(
        &opened.harness,
        host.as_ref(),
        ROOT_CONVERSATION_ID,
        &row.rlm_child_id,
        cx(),
    )
    .await
    .unwrap();
    let super::DeleteChildOutcome::Deleted(entry) = deleted else {
        panic!("expected a delete, got {deleted:?}");
    };
    assert_eq!(entry.rlm_child_id, row.rlm_child_id);
    assert_eq!(
        lock(&host.state)
            .deletes
            .iter()
            .map(|delete| delete.idempotency_key.clone())
            .collect::<Vec<_>>(),
        [format!("rlm:{task_id}:delete")]
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}
