//! Port of `test/harness-lifecycle.test.ts`.
//!
//! JS-only mechanism replaced: the TS test "leaves no subscription behind a
//! watch acquisition cancelled on the line" monkey-patches
//! `harness.subscribeCommits` to count document observers' commit
//! subscriptions. Rust document observers attach to the loaded tracker and
//! never call `subscribe_commits`, and the Session exposes no observer count;
//! the port keeps the cancelled acquisitions and their rejections, and keeps
//! the view-mount half (no observer kept the mount), which is observable.

use std::future::Future;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{with_cancel, Context};
use eukhe_chord::json::JsonValue;
use eukhe_chord::DeliveryKind;
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{JsonObject as PiJsonObject, ModelThinkingLevel, StopReason};
use futures::future::BoxFuture;
use futures::FutureExt;
use tokio::task::JoinHandle;

use super::chat_support::{chat_setup, open_chat, OpenChat};
use super::support::{
    add_hooks, add_task, add_tool, context, create_models, create_registry, empty_object_schema,
    generation_task,
};
use super::task_support::{
    completed, deferred, eventually, flush, open_tasks, settled, CountingReader, Deferred,
    OpenTasksOptions, Reports,
};
use crate::documents::{DocDefinition, SessionDoc};
use crate::errors::StorageError;
use crate::harness::define::define_tool;
use crate::harness::types::{
    AgentChange, ConversationAbortOptions, ConversationCreateOptions, FieldChange, GenerationHooks,
    HarnessOptions, HookApi, HookFuture, InputSubmissionDraft, RegistryReader, RequestMessages,
    SchedulingState, TaskBlockedReason, TaskInspection, TaskInspectionState, ToolExecutionResult,
    ToolRegistration, WriteSubmissionDraft,
};
use crate::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use crate::session::tests::support::{json, ControlledStorage};
use crate::session::{ObservedValue, SessionError, SessionResult, WatchEnd, WatchListener};
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, Task, TaskDefinition};
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationOwnership, ConversationQuery, ConversationRecord,
    Cursor, DocumentAddress, DocumentId, DocumentPoint, DocumentQuery, DocumentRecord, EntryDraft,
    EntryId, EntryQuery, EntryRecord, Page, Seq, Storage, StorageWrite, StoredDocument,
    StoredEntry, SubmissionCreate, SubmissionId, SubmissionQuery, SubmissionRecord,
    SubmissionState, TaskId, TaskOptions, TaskOwnership, TaskQuery, TaskState, WriteSubmission,
};

/// `defineDoc<{ text: string }>({ kind, version: 1, scope: "session", initial: () => ({ text: "" }) })`.
macro_rules! notes_doc {
    ($kind:literal) => {
        match SessionDoc::define(DocDefinition {
            kind: $kind,
            version: 1,
            initial: || json(r#"{"text":""}"#),
            migrate: None,
            checkpoint_when: None,
        }) {
            Ok(token) => token,
            Err(_) => panic!("valid definition"),
        }
    };
}

type StepTask = Task<JsonValue, JsonValue, JsonValue, ()>;

/// The `run` callback of [`one_step_running`].
type Run = Arc<dyn Fn() -> BoxFuture<'static, ()> + Send + Sync>;

/// A one-phase task running `run` and completing with null.
fn one_step_running(name: &str, run: Run) -> StepTask {
    define_task(
        TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
            name,
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"run"}"#)),
            |_, _, _| async { Ok(()) },
        )
        .phase("run", move |_task, runtime, cx| {
            let run = Arc::clone(&run);
            async move {
                run().await;
                runtime
                    .commit(|_, _| async { Ok(Some(completed(JsonValue::Null))) }, &cx)
                    .await
            }
        }),
    )
}

/// A one-phase task completing with null at once.
fn one_step(name: &str) -> StepTask {
    one_step_running(name, Arc::new(|| async {}.boxed()))
}

fn conversation_task_options(background: Option<bool>) -> TaskOptions {
    TaskOptions {
        ownership: TaskOwnership::Conversation,
        conversation_id: None,
        background,
        abandon_on_restart: None,
    }
}

async fn start_with(conversation: &Conversation, task: &StepTask, options: TaskOptions) -> TaskId {
    let definition = task.as_definition_ref();
    conversation
        .commit(
            move |tx| async move { tx.create_task(definition, JsonValue::Null, options).await },
            context(),
        )
        .await
        .unwrap()
}

/// TS `start(conversation, task)`.
async fn start(conversation: &Conversation, task: &StepTask) -> TaskId {
    start_with(conversation, task, conversation_task_options(None)).await
}

/// TS `start(conversation, task, true)`.
async fn start_background(conversation: &Conversation, task: &StepTask) -> TaskId {
    start_with(conversation, task, conversation_task_options(Some(true))).await
}

/// Whether a raw Storage read still succeeds, as code of a joined invocation relies on.
async fn storage_open(storage: &dyn Storage) -> bool {
    storage
        .task(TaskId::from_number(1), context())
        .await
        .is_ok()
}

/// Commit a conversation with a `running` task, as a crash leaves it, so open has a reconciliation commit to fail.
async fn seed_running_task(storage: &dyn Storage) {
    let conversation_id = ConversationId::from_number(storage.mint_id().await.unwrap());
    let id: TaskId = TaskId::from_number(storage.mint_id().await.unwrap());
    let task = AnyTaskRecord {
        id,
        conversation_id,
        kind: "test.seeded".to_owned(),
        version: 1,
        input: JsonValue::Null,
        owner: None,
        background: false,
        abort_requested: false,
        state: TaskState::Running {
            checkpoint: json(r#"{"phase":"run"}"#),
        },
        memos: None,
        started_at: None,
        ended_at: None,
        abandon_on_restart: false,
        abort_reason: None,
    };
    storage
        .commit(
            &[
                StorageWrite::Conversation {
                    value: ConversationRecord {
                        id: conversation_id,
                        parent: None,
                        owner: None,
                    },
                },
                StorageWrite::Task { value: task },
            ],
            context(),
        )
        .await
        .unwrap();
}

fn error(message: &str) -> Arc<std::io::Error> {
    Arc::new(std::io::Error::other(message.to_owned()))
}

fn lock<T>(shared: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    shared.lock().unwrap_or_else(PoisonError::into_inner)
}

/// A handler that ignores its signal: it reports reaching, waits for the
/// gate, then records whether Storage is still open.
#[derive(Clone)]
struct Stubborn {
    reached: Deferred,
    gate: Deferred,
    read_after_release: Arc<Mutex<Option<bool>>>,
    storage: Arc<dyn Storage>,
}

impl Stubborn {
    fn new(storage: Arc<dyn Storage>) -> Self {
        Self {
            reached: deferred(),
            gate: deferred(),
            read_after_release: Arc::default(),
            storage,
        }
    }

    async fn run(&self) {
        self.reached.resolve(());
        self.gate.wait().await;
        let open = storage_open(&*self.storage).await;
        *lock(&self.read_after_release) = Some(open);
    }

    fn read_after_release(&self) -> Option<bool> {
        *lock(&self.read_after_release)
    }
}

/// `ControlledStorage` whose close fails after the inner close.
struct FailingClose {
    inner: Arc<ControlledStorage>,
}

impl Storage for FailingClose {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
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

    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        async move {
            self.inner.close(cx).await?;
            Err(StorageError::failed(std::io::Error::other("close failed")))
        }
        .boxed()
    }
}

// describe("Harness open")

#[tokio::test]
async fn closes_without_a_cancelled_caller_context_and_rethrows_the_original_error_when_open_fails()
{
    let storage = ControlledStorage::new();
    seed_running_task(&*storage).await;
    let reader = Arc::new(CountingReader::new(create_registry()));
    let held = storage.hold_commits();
    storage.fail_next_commit(StorageError::failed(std::io::Error::other("disk full")));
    let (cancellable, cancel) = with_cancel(context());
    let options = HarnessOptions::new(
        create_models(),
        Arc::clone(&reader) as Arc<dyn RegistryReader>,
    );
    let opening = {
        let storage = Arc::clone(&storage) as Arc<dyn Storage>;
        tokio::spawn(async move { Harness::open(storage, options, &cancellable).await })
    };
    held.entered().await;
    cancel.cancel(Some(error("caller gave up")));
    held.release();
    let open_error = opening.await.unwrap().unwrap_err();
    assert!(open_error.to_string().contains("disk full"), "{open_error}");
    assert_eq!(reader.subscriptions(), 0);
    assert!(!storage_open(&*storage).await);
}

#[tokio::test]
async fn rethrows_the_open_error_and_reports_it_once_though_closing_then_fails_too() {
    let inner = ControlledStorage::new();
    let storage = Arc::new(FailingClose {
        inner: Arc::clone(&inner),
    });
    seed_running_task(&*storage).await;
    inner.fail_next_commit(StorageError::failed(std::io::Error::other("disk full")));
    let reports = Reports::default();
    let mut options = HarnessOptions::new(create_models(), Arc::new(create_registry()));
    options.on_report = Some(reports.sink());
    let open_error = Harness::open(storage, options, context())
        .await
        .unwrap_err();
    assert!(open_error.to_string().contains("disk full"), "{open_error}");
    // The storage failure that failed open is the cause; the close that fails after it adds no report.
    let reported: Vec<String> = reports.all().iter().map(ToString::to_string).collect();
    assert_eq!(reported, ["disk full"]);
}

// describe("Harness close")

#[tokio::test]
async fn joins_a_task_handler_that_ignores_its_signal_before_closing_storage() {
    let storage: Arc<dyn Storage> = Arc::new(MemoryStorage::new());
    let stubborn = Stubborn::new(Arc::clone(&storage));
    let run_stubborn = stubborn.clone();
    let task = one_step_running(
        "test.close-stubborn",
        Arc::new(move || {
            let stubborn = run_stubborn.clone();
            async move { stubborn.run().await }.boxed()
        }),
    );
    let harness = open_tasks(
        Arc::clone(&storage),
        &[task.erase()],
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    start(&root, &task).await;
    harness.resume().unwrap();
    stubborn.reached.wait().await;
    let closing = tokio::spawn(harness.close(context()));
    assert!(!settled(&closing).await);
    assert!(storage_open(&*storage).await);
    stubborn.gate.resolve(());
    closing.await.unwrap().unwrap();
    assert_eq!(stubborn.read_after_release(), Some(true));
    assert!(!storage_open(&*storage).await);
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Where {
    Tool,
    Hook,
}

#[tokio::test]
#[allow(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn joins_a_tool_execute_and_a_hook_that_ignore_their_signal_before_closing_storage() {
    for place in [Where::Tool, Where::Hook] {
        let setup = chat_setup(RegisterFauxProviderOptions::default());
        let storage: Arc<dyn Storage> = Arc::new(MemoryStorage::new());
        let stubborn = Stubborn::new(Arc::clone(&storage));
        let tool_stubborn = stubborn.clone();
        add_tool(
            &setup.registry,
            define_tool(ToolRegistration::new(
                "wait",
                "wait",
                empty_object_schema(),
                move |_, _, _| {
                    let stubborn = tool_stubborn.clone();
                    async move {
                        if place == Where::Tool {
                            stubborn.run().await;
                        }
                        Ok(ToolExecutionResult {
                            output: Some(Vec::new()),
                            ..ToolExecutionResult::default()
                        })
                    }
                },
            )),
            None,
        )
        .unwrap();
        let hook_stubborn = stubborn.clone();
        add_hooks(
            &setup.registry,
            generation_task(),
            GenerationHooks {
                before_request: Some(Arc::new(
                    move |_: &RequestMessages,
                          _: &HookApi,
                          _: &Context|
                          -> HookFuture<RequestMessages> {
                        let stubborn = hook_stubborn.clone();
                        async move {
                            if place == Where::Hook {
                                stubborn.run().await;
                            }
                            Ok(None)
                        }
                        .boxed()
                    },
                )),
                ..GenerationHooks::default()
            },
            None,
        )
        .unwrap();
        setup.faux.set_responses(vec![
            faux_assistant_message(
                vec![faux_tool_call(
                    "wait",
                    PiJsonObject::new(),
                    Some("c1".to_owned()),
                )],
                FauxAssistantMessageOptions {
                    stop_reason: Some(StopReason::ToolUse),
                    ..FauxAssistantMessageOptions::default()
                },
            )
            .into(),
            faux_assistant_message(
                vec![faux_text("done")],
                FauxAssistantMessageOptions::default(),
            )
            .into(),
        ]);
        let OpenChat { harness, root } =
            open_chat(Arc::clone(&storage), &setup, None).await.unwrap();
        root.submit(InputSubmissionDraft::new("go"), context())
            .await
            .unwrap();
        stubborn.reached.wait().await;
        let closing = tokio::spawn(harness.close(context()));
        assert!(!settled(&closing).await, "{place:?}");
        assert!(storage_open(&*storage).await, "{place:?}");
        stubborn.gate.resolve(());
        closing.await.unwrap().unwrap();
        assert_eq!(stubborn.read_after_release(), Some(true), "{place:?}");
        assert!(!storage_open(&*storage).await, "{place:?}");
    }
}

#[tokio::test]
async fn lets_a_new_harness_open_the_same_storage_once_close_resolved_no_old_invocation_code_runs()
{
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("session.sqlite");
    let sqlite = || async {
        Arc::new(
            open_native_sqlite_storage(&path, NativeSqliteStorageOptions::default())
                .await
                .unwrap(),
        ) as Arc<dyn Storage>
    };
    let log: Arc<Mutex<Vec<String>>> = Arc::default();
    let gate: Deferred = deferred();
    let generation = Arc::new(AtomicU64::new(1));
    let task = {
        let (log, gate, generation) = (Arc::clone(&log), gate.clone(), Arc::clone(&generation));
        one_step_running(
            "test.generations",
            Arc::new(move || {
                let (log, gate, generation) =
                    (Arc::clone(&log), gate.clone(), Arc::clone(&generation));
                async move {
                    let mine = generation.load(Ordering::SeqCst);
                    lock(&log).push(format!("start {mine}"));
                    if mine == 1 {
                        gate.wait().await;
                    }
                    lock(&log).push(format!("end {mine}"));
                }
                .boxed()
            }),
        )
    };
    let first = open_tasks(sqlite().await, &[task.erase()], OpenTasksOptions::default()).await;
    let first_root = first
        .harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let id = start(&first_root, &task).await;
    first.harness.resume().unwrap();
    eventually(|| {
        let reached = lock(&log).len() == 1;
        async move { reached }
    })
    .await;
    let closing = {
        let close = first.harness.close(context());
        let log = Arc::clone(&log);
        tokio::spawn(async move {
            let closed = close.await;
            lock(&log).push("closed".to_owned());
            closed
        })
    };
    assert!(!settled(&closing).await);
    gate.resolve(());
    closing.await.unwrap().unwrap();
    assert_eq!(*lock(&log), ["start 1", "end 1", "closed"]);
    generation.store(2, Ordering::SeqCst);
    let second = open_tasks(sqlite().await, &[task.erase()], OpenTasksOptions::default()).await;
    second.harness.resume().unwrap();
    second.harness.wait_for_task(id, context()).await.unwrap();
    assert_eq!(
        *lock(&log),
        ["start 1", "end 1", "closed", "start 2", "end 2"]
    );
    second.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_shutting_down_after_a_cancelled_close_and_a_second_close_awaits_the_same_shutdown() {
    let storage: Arc<dyn Storage> = Arc::new(MemoryStorage::new());
    let reached: Deferred = deferred();
    let gate: Deferred = deferred();
    let task = {
        let (reached, gate) = (reached.clone(), gate.clone());
        one_step_running(
            "test.close-cancelled",
            Arc::new(move || {
                let (reached, gate) = (reached.clone(), gate.clone());
                async move {
                    reached.resolve(());
                    gate.wait().await;
                }
                .boxed()
            }),
        )
    };
    let harness = open_tasks(
        Arc::clone(&storage),
        &[task.erase()],
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    start(&root, &task).await;
    harness.resume().unwrap();
    reached.wait().await;
    let (cancellable, cancel) = with_cancel(context());
    let cancelled = tokio::spawn(harness.close(&cancellable));
    cancel.cancel(Some(error("stop waiting")));
    let close_error = cancelled.await.unwrap().unwrap_err();
    assert!(
        close_error.to_string().contains("stop waiting"),
        "{close_error}"
    );
    // Admission stays sealed and the invocation still holds Storage open.
    let commit_error = harness
        .commit(|_| async { Ok(()) }, context())
        .await
        .unwrap_err();
    assert!(
        commit_error.to_string().contains("closed"),
        "{commit_error}"
    );
    assert!(storage_open(&*storage).await);
    let second = tokio::spawn(harness.close(context()));
    assert!(!settled(&second).await);
    gate.resolve(());
    second.await.unwrap().unwrap();
    assert!(!storage_open(&*storage).await);
}

#[tokio::test]
async fn settles_durably_a_commit_whose_committer_was_cancelled_while_it_was_in_storage() {
    let storage = ControlledStorage::new();
    let harness = open_tasks(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &[],
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let held = storage.hold_commits();
    let (cancellable, cancel) = with_cancel(context());
    let root_id = root.id();
    let committing = tokio::spawn(root.commit(
        move |tx| async move { Ok(tx.append_entry(root_id, EntryDraft::new("note")).await?.id) },
        &cancellable,
    ));
    held.entered().await;
    cancel.cancel(Some(error("committer gave up")));
    held.release();
    let id = committing.await.unwrap().unwrap();
    let page = root
        .entries(ConversationEntryQuery::default(), 10, None, context())
        .await
        .unwrap();
    let ids: Vec<EntryId> = page.items.iter().map(|entry| entry.id).collect();
    assert_eq!(ids, [id]);
    harness.close(context()).await.unwrap();
}

type Frames = Arc<Mutex<Vec<&'static str>>>;

/// A watch listener that records `label` for every delivered frame.
fn recorder<T: ObservedValue>(frames: &Frames, label: &'static str) -> WatchListener<T> {
    let frames = Arc::clone(frames);
    Arc::new(move |_, _, _| {
        lock(&frames).push(label);
        async { Ok(()) }.boxed()
    })
}

#[tokio::test]
#[allow(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn publishes_no_frame_to_states_and_watches_from_a_commit_that_settles_during_close() {
    const NOTES: SessionDoc<JsonValue> = notes_doc!("test.close-frames");
    let storage = ControlledStorage::new();
    let harness = open_tasks(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &[],
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    harness
        .commit(
            |tx| async move {
                tx.doc(&NOTES, ()).await?.set("text", "before")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let doc_state = harness
        .document_state(&NOTES, (), context())
        .await
        .unwrap()
        .unwrap();
    let doc_watch = harness
        .watch_doc(&NOTES, (), context())
        .await
        .unwrap()
        .unwrap();
    let view_state = root.view_state(context()).await.unwrap();
    let view_watch = root.watch(context()).await.unwrap();
    let graph_state = harness.task_graph(context()).await.unwrap();
    let graph_watch = harness.watch_task_graph(context()).await.unwrap();
    let frames: Frames = Arc::default();
    let sink = Arc::clone(&frames);
    let _graph_subscription = graph_state.subscribe(move |_value, _context, delivery| {
        if delivery.kind == DeliveryKind::Update {
            lock(&sink).push("graphState");
        }
    });
    graph_watch.start(recorder(&frames, "graphWatch")).unwrap();
    let sink = Arc::clone(&frames);
    let _doc_subscription = doc_state.subscribe(move |_value, _context, delivery| {
        if delivery.kind == DeliveryKind::Update {
            lock(&sink).push("docState");
        }
    });
    let sink = Arc::clone(&frames);
    let _view_subscription = view_state.subscribe(move |_value, _context, delivery| {
        if delivery.kind == DeliveryKind::Update {
            lock(&sink).push("viewState");
        }
    });
    doc_watch.start(recorder(&frames, "docWatch")).unwrap();
    view_watch.start(recorder(&frames, "viewWatch")).unwrap();
    let doc_value = doc_state.value();
    let view_value = view_state.value();

    let held = storage.hold_commits();
    let root_id = root.id();
    let graph_task = one_step("test.close-graph").as_definition_ref();
    let committing = tokio::spawn(harness.commit(
        move |tx| async move {
            tx.doc(&NOTES, ()).await?.set("text", "during close")?;
            tx.append_entry(root_id, EntryDraft::new("note")).await?;
            tx.create_task(
                graph_task,
                JsonValue::Null,
                TaskOptions {
                    ownership: TaskOwnership::Conversation,
                    conversation_id: Some(root_id),
                    background: None,
                    abandon_on_restart: None,
                },
            )
            .await?;
            Ok(())
        },
        context(),
    ));
    held.entered().await;
    let closing = tokio::spawn(harness.close(context()));
    held.release();
    committing.await.unwrap().unwrap();
    closing.await.unwrap().unwrap();
    flush().await;
    assert!(lock(&frames).is_empty(), "{:?}", lock(&frames));
    assert!(doc_state.value().strict_equals(&doc_value));
    assert!(view_state.value().strict_equals(&view_value));
    assert_eq!(graph_state.value(), json(r#"{"tasks":{}}"#));
    assert_eq!(graph_watch.closed().await, WatchEnd::SessionClosed);
    assert_eq!(doc_watch.closed().await, WatchEnd::SessionClosed);
    assert_eq!(view_watch.closed().await, WatchEnd::SessionClosed);
    // The commit itself settled.
    assert!(storage
        .last_commit()
        .iter()
        .any(|write| matches!(write, StorageWrite::Entry { .. })));
}

#[tokio::test]
async fn leaves_no_subscription_behind_a_watch_acquisition_cancelled_on_the_line() {
    const NOTES: SessionDoc<JsonValue> = notes_doc!("test.cancelled-watch");
    let storage = ControlledStorage::new();
    let harness = open_tasks(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &[],
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    harness
        .commit(
            |tx| async move {
                tx.doc(&NOTES, ()).await?.set("text", "x")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    // Count commit subscriptions of document observers: not observable in
    // Rust (see the module docs); the cancelled acquisitions below must
    // reject, and the view mount must not be kept.

    // Cancel a document watch while its acquisition loads the document on the line.
    harness.unload_documents().await.unwrap();
    let find = storage.hold_find_document();
    let (cancellable, cancel) = with_cancel(context());
    let doc_watch = tokio::spawn(harness.watch_doc(&NOTES, (), &cancellable));
    find.entered().await;
    cancel.cancel(Some(error("cancelled")));
    find.release();
    let watch_error = doc_watch.await.unwrap().unwrap_err();
    assert!(
        watch_error.to_string().contains("cancelled"),
        "{watch_error}"
    );

    // Cancel a view watch while it builds its mount on the line.
    harness.unload_documents().await.unwrap();
    let find = storage.hold_find_document();
    let (cancellable, cancel) = with_cancel(context());
    let view_watch = tokio::spawn(root.watch(&cancellable));
    find.entered().await;
    cancel.cancel(Some(error("cancelled")));
    find.release();
    let watch_error = view_watch.await.unwrap().unwrap_err();
    assert!(
        watch_error.to_string().contains("cancelled"),
        "{watch_error}"
    );
    // No observer kept the mount: the next observer builds a new one, and the one after that another.
    let first = root.view_state(context()).await.unwrap();
    let first_value = first.value();
    first.dispose().unwrap();
    let second = root.view_state(context()).await.unwrap();
    assert!(!second.value().strict_equals(&first_value));
    second.dispose().unwrap();
    harness.close(context()).await.unwrap();
}

/// `"closed"` when the failure says so, else its message.
fn describe_failure(error: &SessionError) -> String {
    let text = error.to_string();
    if text.contains("closed") {
        "closed".to_owned()
    } else {
        text
    }
}

/// TS `operation().then(() => "resolved", (error) => /closed/.test(String(error)) ? "closed" : String(error))`.
async fn outcome<T>(operation: impl Future<Output = SessionResult<T>>) -> String {
    match operation.await {
        Ok(_) => "resolved".to_owned(),
        Err(error) => describe_failure(&error),
    }
}

#[tokio::test]
#[allow(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn rejects_conversation_and_harness_operations_once_close_begins_inspect_queued_before_reports_closing(
) {
    let storage = ControlledStorage::new();
    let harness = open_tasks(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &[],
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let root_id = root.id();
    let entry = root
        .commit(
            move |tx| async move { tx.append_entry(root_id, EntryDraft::new("note")).await },
            context(),
        )
        .await
        .unwrap();
    let submission = root
        .submit(
            WriteSubmissionDraft {
                request_id: None,
                entry: EntryDraft::new("note"),
            },
            context(),
        )
        .await
        .unwrap();

    let held = storage.hold_commits();
    let blocking = tokio::spawn(harness.commit(
        move |tx| async move {
            tx.append_entry(root_id, EntryDraft::new("blocker")).await?;
            Ok(())
        },
        context(),
    ));
    held.entered().await;
    let queued_inspect = tokio::spawn(harness.inspect(context()));
    let closing = tokio::spawn(harness.close(context()));
    let one: TaskId = TaskId::from_number(1);
    let cx = context();
    let outcomes = vec![
        (
            "submit",
            outcome(root.submit(InputSubmissionDraft::new("x"), cx)).await,
        ),
        ("agent", outcome(root.agent(cx)).await),
        (
            "configure",
            outcome(root.configure(
                AgentChange {
                    thinking_level: FieldChange::Set(ModelThinkingLevel::Low),
                    ..AgentChange::default()
                },
                cx,
            ))
            .await,
        ),
        (
            "commit",
            outcome(root.commit(|_| async { Ok(()) }, cx)).await,
        ),
        (
            "context",
            outcome(root.context(cx, crate::harness::types::ContextOptions::default())).await,
        ),
        (
            "entries",
            outcome(root.entries(ConversationEntryQuery::default(), 10, None, cx)).await,
        ),
        (
            "fork",
            outcome(root.fork(
                entry.id,
                ConversationCreateOptions::new(ConversationOwnership::Ownerless),
                cx,
            ))
            .await,
        ),
        ("compact", outcome(root.compact(None, cx)).await),
        ("reset", outcome(root.reset(None, cx)).await),
        (
            "abort",
            outcome(root.abort(ConversationAbortOptions::default(), cx)).await,
        ),
        ("conversationIdle", outcome(root.wait_for_idle(cx)).await),
        ("viewState", outcome(root.view_state(cx)).await),
        ("watch", outcome(root.watch(cx)).await),
        ("taskGraph", outcome(harness.task_graph(cx)).await),
        (
            "watchTaskGraph",
            outcome(harness.watch_task_graph(cx)).await,
        ),
        ("status", outcome(submission.status(cx)).await),
        ("wait", outcome(submission.wait(cx)).await),
        ("abortSubmission", outcome(submission.abort(cx)).await),
        (
            "root",
            outcome(harness.root(RootOptions::default(), cx)).await,
        ),
        (
            "conversation",
            outcome(harness.conversation(root_id, cx)).await,
        ),
        (
            "createConversation",
            outcome(harness.create_conversation(
                ConversationCreateOptions::new(ConversationOwnership::Ownerless),
                cx,
            ))
            .await,
        ),
        ("getTask", outcome(harness.get_task(one, cx)).await),
        ("inspect", outcome(harness.inspect(cx)).await),
        (
            "submission",
            outcome(harness.submission(submission.id(), cx)).await,
        ),
        ("abortTask", outcome(harness.abort_task(one, cx)).await),
        ("waitForTask", outcome(harness.wait_for_task(one, cx)).await),
        ("harnessIdle", outcome(harness.wait_for_idle(cx)).await),
        ("usage", outcome(harness.usage(cx)).await),
    ];
    let expected: Vec<(&str, String)> = outcomes
        .iter()
        .map(|(name, _)| (*name, "closed".to_owned()))
        .collect();
    assert_eq!(outcomes, expected);
    let resume_error = harness.resume().unwrap_err();
    assert!(
        resume_error.to_string().contains("closed"),
        "{resume_error}"
    );
    held.release();
    blocking.await.unwrap().unwrap();
    assert_eq!(
        queued_inspect.await.unwrap().unwrap().scheduling,
        SchedulingState::Closing
    );
    closing.await.unwrap().unwrap();
}

/// TS `settle(promise)` of a value that is never `undefined`, started now.
fn settle<T, F>(operation: F) -> JoinHandle<String>
where
    T: Send + 'static,
    F: Future<Output = SessionResult<T>> + Send + 'static,
{
    tokio::spawn(outcome(operation))
}

/// TS `settle(promise)` of a value that may be `undefined`, started now.
fn settle_optional<T, F>(operation: F) -> JoinHandle<String>
where
    T: Send + 'static,
    F: Future<Output = SessionResult<Option<T>>> + Send + 'static,
{
    tokio::spawn(async move {
        match operation.await {
            Ok(Some(_)) => "resolved".to_owned(),
            Ok(None) => "undefined".to_owned(),
            Err(error) => describe_failure(&error),
        }
    })
}

#[tokio::test]
#[allow(clippy::too_many_lines, reason = "one TS case, ported whole")]
async fn completes_reads_queued_at_the_seal_and_rejects_queued_waits_and_acquisitions_that_would_follow_commits(
) {
    const NOTES: SessionDoc<JsonValue> = notes_doc!("test.queued-at-seal");
    const ABSENT: SessionDoc<JsonValue> = notes_doc!("test.queued-absent");
    let pending = one_step("test.queued-pending");
    let storage = ControlledStorage::new();
    let harness = open_tasks(
        Arc::clone(&storage) as Arc<dyn Storage>,
        &[],
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    harness
        .commit(
            |tx| async move {
                tx.doc(&NOTES, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let task_id = start(&root, &pending).await;
    let write = root
        .submit(
            WriteSubmissionDraft {
                request_id: None,
                entry: EntryDraft::new("note"),
            },
            context(),
        )
        .await
        .unwrap();
    write.wait(context()).await.unwrap();

    let held = storage.hold_commits();
    let root_id = root.id();
    let blocking = tokio::spawn(harness.commit(
        move |tx| async move {
            tx.append_entry(root_id, EntryDraft::new("blocker")).await?;
            Ok(())
        },
        context(),
    ));
    held.entered().await;
    let cx = context();
    let queued = vec![
        (
            "context",
            settle(root.context(cx, crate::harness::types::ContextOptions::default())),
        ),
        (
            "snapshot",
            settle_optional(harness.snapshot(&NOTES, (), cx)),
        ),
        ("settledWait", settle(write.wait(cx))),
        (
            "absentWatch",
            settle_optional(harness.watch_doc(&ABSENT, (), cx)),
        ),
        (
            "absentState",
            settle_optional(harness.document_state(&ABSENT, (), cx)),
        ),
        ("waitForTask", settle(harness.wait_for_task(task_id, cx))),
        (
            "documentState",
            settle_optional(harness.document_state(&NOTES, (), cx)),
        ),
        (
            "watchDoc",
            settle_optional(harness.watch_doc(&NOTES, (), cx)),
        ),
        ("viewState", settle(root.view_state(cx))),
        ("watch", settle(root.watch(cx))),
        ("taskGraph", settle(harness.task_graph(cx))),
    ];
    // TS promises start at once; Rust futures start when polled, so let every
    // spawned operation reach the line before close seals it.
    flush().await;
    let closing = tokio::spawn(harness.close(context()));
    held.release();
    blocking.await.unwrap().unwrap();
    let mut outcomes = Vec::new();
    for (name, handle) in queued {
        outcomes.push((name, handle.await.unwrap()));
    }
    let expected = [
        ("context", "resolved"),
        ("snapshot", "resolved"),
        ("settledWait", "resolved"),
        ("absentWatch", "undefined"),
        ("absentState", "undefined"),
        ("waitForTask", "closed"),
        ("documentState", "closed"),
        ("watchDoc", "closed"),
        ("viewState", "closed"),
        ("watch", "closed"),
        ("taskGraph", "closed"),
    ]
    .map(|(name, outcome)| (name, outcome.to_owned()));
    assert_eq!(outcomes, expected);
    closing.await.unwrap().unwrap();
}

// describe("scheduling on a paused Harness")

/// A paused Harness with one background task pending and a queued write submission.
struct Paused {
    harness: Harness,
    root: Conversation,
    id: TaskId,
    submission_id: SubmissionId,
    ran: Arc<AtomicBool>,
}

impl Paused {
    fn ran(&self) -> bool {
        self.ran.load(Ordering::SeqCst)
    }
}

/// Open a paused Harness with one background task pending and a queued write submission.
async fn paused() -> Paused {
    let ran = Arc::new(AtomicBool::new(false));
    let marker = {
        let ran = Arc::clone(&ran);
        one_step_running(
            "test.marker",
            Arc::new(move || {
                let ran = Arc::clone(&ran);
                async move { ran.store(true, Ordering::SeqCst) }.boxed()
            }),
        )
    };
    let harness = open_tasks(
        Arc::new(MemoryStorage::new()),
        &[marker.erase()],
        OpenTasksOptions::default(),
    )
    .await
    .harness;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    // Background, so idle waits and conversation abort leave it alone.
    let id = start_background(&root, &marker).await;
    let conversation_id = root.id();
    let submission_id = harness
        .commit(
            move |tx| async move {
                Ok(tx
                    .create_submission(SubmissionCreate {
                        conversation_id,
                        request_id: None,
                        state: SubmissionState::Write(WriteSubmission::Queued),
                    })
                    .await?
                    .id)
            },
            context(),
        )
        .await
        .unwrap();
    Paused {
        harness,
        root,
        id,
        submission_id,
        ran,
    }
}

#[tokio::test]
async fn never_schedules_from_a_read_only_viewer() {
    const NOTES: SessionDoc<JsonValue> = notes_doc!("test.viewer-notes");
    let opened = paused().await;
    let Paused {
        harness,
        root,
        id,
        submission_id,
        ..
    } = &opened;
    harness
        .commit(
            |tx| async move {
                tx.doc(&NOTES, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    harness.inspect(context()).await.unwrap();
    harness.get_task(*id, context()).await.unwrap();
    harness.usage(context()).await.unwrap();
    harness.conversation(root.id(), context()).await.unwrap();
    harness.snapshot(&NOTES, (), context()).await.unwrap();
    harness
        .document_state(&NOTES, (), context())
        .await
        .unwrap()
        .unwrap()
        .dispose()
        .unwrap();
    harness
        .watch_doc(&NOTES, (), context())
        .await
        .unwrap()
        .unwrap()
        .stop()
        .await;
    let submission = harness
        .submission(*submission_id, context())
        .await
        .unwrap()
        .unwrap();
    submission.status(context()).await.unwrap();
    root.agent(context()).await.unwrap();
    root.context(context(), crate::harness::types::ContextOptions::default())
        .await
        .unwrap();
    root.entries(ConversationEntryQuery::default(), 10, None, context())
        .await
        .unwrap();
    root.view_state(context()).await.unwrap().dispose().unwrap();
    root.watch(context()).await.unwrap().stop().await;
    harness
        .task_graph(context())
        .await
        .unwrap()
        .dispose()
        .unwrap();
    harness
        .watch_task_graph(context())
        .await
        .unwrap()
        .stop()
        .await;
    flush().await;
    flush().await;
    assert!(!opened.ran());
    assert_eq!(
        harness.inspect(context()).await.unwrap().scheduling,
        SchedulingState::Paused
    );
    harness.close(context()).await.unwrap();
}

/// The progress calls that enable scheduling.
#[derive(Clone, Copy, Debug)]
enum ProgressCall {
    Submit,
    Compact,
    Abort,
    ConversationIdle,
    SubmissionWait,
    WaitForTask,
    HarnessIdle,
}

impl ProgressCall {
    const ALL: [Self; 7] = [
        Self::Submit,
        Self::Compact,
        Self::Abort,
        Self::ConversationIdle,
        Self::SubmissionWait,
        Self::WaitForTask,
        Self::HarnessIdle,
    ];

    fn name(self) -> &'static str {
        match self {
            Self::Submit => "submit",
            Self::Compact => "compact",
            Self::Abort => "abort",
            Self::ConversationIdle => "conversationIdle",
            Self::SubmissionWait => "submissionWait",
            Self::WaitForTask => "waitForTask",
            Self::HarnessIdle => "harnessIdle",
        }
    }

    /// Start the call; its outcome is ignored (TS `.catch(() => {})`): a
    /// queued write's wait settles only on placement, and close rejects it.
    fn call(self, opened: &Paused) -> BoxFuture<'static, ()> {
        let cx = context();
        match self {
            Self::Submit => {
                let submitted = opened.root.submit(
                    WriteSubmissionDraft {
                        request_id: None,
                        entry: EntryDraft::new("note"),
                    },
                    cx,
                );
                async move {
                    let _ = submitted.await;
                }
                .boxed()
            }
            Self::Compact => {
                let compacting = opened.root.compact(None, cx);
                async move {
                    let _ = compacting.await;
                }
                .boxed()
            }
            Self::Abort => {
                let aborting = opened.root.abort(ConversationAbortOptions::default(), cx);
                async move {
                    let _ = aborting.await;
                }
                .boxed()
            }
            Self::ConversationIdle => {
                let waiting = opened.root.wait_for_idle(cx);
                async move {
                    let _ = waiting.await;
                }
                .boxed()
            }
            Self::SubmissionWait => {
                let acquiring = opened.harness.submission(opened.submission_id, cx);
                async move {
                    let submission = acquiring
                        .await
                        .unwrap()
                        .expect("the queued submission exists");
                    let _ = submission.wait(context()).await;
                }
                .boxed()
            }
            Self::WaitForTask => {
                let waiting = opened.harness.wait_for_task(opened.id, cx);
                async move {
                    let _ = waiting.await;
                }
                .boxed()
            }
            Self::HarnessIdle => {
                let waiting = opened.harness.wait_for_idle(cx);
                async move {
                    let _ = waiting.await;
                }
                .boxed()
            }
        }
    }
}

#[tokio::test]
async fn schedules_from_every_progress_call() {
    for call in ProgressCall::ALL {
        let opened = paused().await;
        // A queued write's wait settles only on placement; close rejects it.
        let pending = tokio::spawn(call.call(&opened));
        let mut ran = false;
        for _ in 0..200 {
            if opened.ran() {
                ran = true;
                break;
            }
            flush().await;
        }
        assert!(ran, "{} did not enable scheduling", call.name());
        opened.harness.close(context()).await.unwrap();
        pending.await.unwrap();
    }
}

// describe("registry changes before resume")

#[tokio::test]
async fn runs_what_the_registry_holds_at_resume_a_definition_installed_or_replaced_after_open() {
    let log: Arc<Mutex<Vec<String>>> = Arc::default();
    let define = |label: &'static str| {
        let log = Arc::clone(&log);
        one_step_running(
            "test.late-definition",
            Arc::new(move || {
                let log = Arc::clone(&log);
                async move { lock(&log).push(label.to_owned()) }.boxed()
            }),
        )
    };
    let first = open_tasks(
        Arc::new(MemoryStorage::new()),
        &[],
        OpenTasksOptions::default(),
    )
    .await;
    let root = first
        .harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let missing = start(&root, &define("unused")).await;
    let tasks = first.harness.inspect(context()).await.unwrap().tasks;
    assert!(
        matches!(
            tasks.as_slice(),
            [TaskInspection {
                state: TaskInspectionState::Blocked {
                    reason: TaskBlockedReason::MissingTask,
                    ..
                },
                ..
            }]
        ),
        "{tasks:?}"
    );
    let installed = add_task(&first.registry, define("v1").erase(), None).unwrap();
    let tasks = first.harness.inspect(context()).await.unwrap().tasks;
    assert!(
        matches!(
            tasks.as_slice(),
            [TaskInspection {
                state: TaskInspectionState::Ready { .. },
                ..
            }]
        ),
        "{tasks:?}"
    );
    // The same extension name replaces the definition in place, still before resume.
    installed.dispose();
    add_task(&first.registry, define("v2").erase(), None).unwrap();
    first.harness.resume().unwrap();
    first
        .harness
        .wait_for_task(missing, context())
        .await
        .unwrap();
    assert_eq!(*lock(&log), ["v2"]);
    first.harness.close(context()).await.unwrap();
}
