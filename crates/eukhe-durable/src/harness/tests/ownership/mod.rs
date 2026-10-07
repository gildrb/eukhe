//! Port of `test/harness-ownership.test.ts`: shared helpers of the TS file
//! live here; each TS `describe` is one submodule.
//!
//! The TS module-level `gates` and `runs` maps (cleared in `afterEach`) are
//! per-test [`World`] state shared with the task handlers through `Arc`; the
//! temp directories of `afterEach` are [`tempfile::TempDir`]s dropped with
//! each test.

mod cascades;
mod owned_conversations;

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{with_cancel, Context};
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_tool_call, FauxAssistantMessageOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::typebox::Type;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, JsonValue as PiJsonValue, Message, StopReason,
    TextContent, UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::{Deserialize, Serialize};

use super::chat_support::{chat_setup, open_chat, wait_for, OpenChat};
use super::support::{add_task, add_tool, context, empty_object_schema};
use super::task_support::{
    aborted, deferred, flush, open_tasks, settled, Deferred, OpenTasksOptions, OpenedTasks, Reports,
};
use crate::documents::{ConversationDoc, DocDefinition};
use crate::errors::{StorageError, StorageRejected};
use crate::harness::agent::configure;
use crate::harness::define::define_tool;
use crate::harness::live::LIVE_DOC;
use crate::harness::types::{
    AgentChange, ConversationAbortOptions, ConversationHandle, FieldChange, InputSubmissionDraft,
    ModelRef, Submission, ToolExecutionApiExt, ToolExecutionResult, ToolRegistration, ToolReplay,
    WriteSubmissionDraft,
};
use crate::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions, TaskAbortResult};
use crate::session::{create_session, SessionError, SessionResult, Tx};
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationOwnership, ConversationQuery, ConversationRecord,
    Cursor, DocumentAddress, DocumentId, DocumentPoint, DocumentQuery, DocumentReaderExt,
    DocumentRecord, EntryDraft, EntryId, EntryQuery, EntryRecord, InputSubmission, JoinPolicy,
    LatestFork, Page, Seq, Storage, StorageWrite, StoredDocument, StoredEntry, SubmissionId,
    SubmissionQuery, SubmissionRecord, SubmissionState, SubmissionStatus, TaskId, TaskOptions,
    TaskOutcome, TaskOutcomeError, TaskOutcomeStatus, TaskOwnership, TaskQuery, TaskRecord,
    TaskState, TaskStatus,
};

/// TS `waitUntil`: 500 polls of 5 ms.
const WAIT_UNTIL_MS: u64 = 2_500;

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn memory() -> Arc<dyn Storage> {
    Arc::new(MemoryStorage::new())
}

/// A fresh directory (removed when dropped, the TS `afterEach`) and the
/// database path inside it.
fn sqlite_path(prefix: &str) -> (tempfile::TempDir, PathBuf) {
    let directory = tempfile::Builder::new()
        .prefix(prefix)
        .tempdir()
        .expect("create a temp dir");
    let path = directory.path().join("session.sqlite");
    (directory, path)
}

/// TS `openNodeSqliteStorage(path)`.
async fn sqlite(path: &Path) -> Arc<dyn Storage> {
    Arc::new(
        open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
            .await
            .expect("open the SQLite storage"),
    )
}

/// Outcome a held task commits once its gate opens.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ending {
    Completed,
    Failed,
}

/// The TS module-level `gates` and `runs` maps.
#[derive(Clone, Default)]
struct Gates {
    gates: Arc<Mutex<HashMap<String, Deferred<Ending>>>>,
    /// How often each named task started its run phase.
    runs: Arc<Mutex<HashMap<String, usize>>>,
}

impl Gates {
    fn gate(&self, name: &str) -> Deferred<Ending> {
        self.gates
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .entry(name.to_owned())
            .or_insert_with(deferred)
            .clone()
    }

    fn count_run(&self, name: &str) {
        *self
            .runs
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .entry(name.to_owned())
            .or_insert(0) += 1;
    }

    fn runs(&self, name: &str) -> Option<usize> {
        self.runs
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(name)
            .copied()
    }
}

/// Input of [`hold_task`] (TS `{ name: string; slowAbort?: boolean }`).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HoldInput {
    name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    slow_abort: Option<bool>,
}

impl HoldInput {
    fn named(name: &str) -> Self {
        Self {
            name: name.to_owned(),
            slow_abort: None,
        }
    }

    fn slow(name: &str, slow: bool) -> Self {
        Self {
            name: name.to_owned(),
            slow_abort: slow.then_some(true),
        }
    }
}

/// TS `{ phase: "hold" }`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "lowercase")]
enum HoldStep {
    Hold,
}

type HoldTask = Task<HoldInput, HoldStep, (), ()>;

/// Input of [`waiter_task`] (TS `{ on: TaskId[] }`).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
struct WaiterInput {
    on: Vec<TaskId>,
}

/// TS `{ phase: "wait" } | { phase: "done" }`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "lowercase")]
enum WaiterStep {
    Wait,
    Done,
}

type WaiterTask = Task<WaiterInput, WaiterStep, (), ()>;

fn aborted_state<S>() -> NextTaskState<S, ()> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: None,
            result: None,
        },
    }
}

/// A task that holds until its named gate opens or it is aborted. With
/// `slow_abort`, its abort handler first waits for the gate `abort.<name>`.
///
/// Unlike TS, the slow abort handler also ends when its invocation is
/// signalled (close seals the scheduler). TS reserves the abort invocation
/// on the Session line with a synchronous `node:sqlite`, so in the tests
/// that abort and then close it never starts before close; the native
/// SQLite storage answers from its own thread, so the reservation may win
/// that race, and close would then join a handler blocked on a gate the
/// test opens only after reopening. Ending on the signal writes nothing (a
/// closing scheduler ends the invocation without a write), so the durable
/// state equals the TS one either way.
fn hold_task(gates: &Gates) -> HoldTask {
    let (run_gates, abort_gates) = (gates.clone(), gates.clone());
    define_task(
        TaskDefinition::<HoldInput, HoldStep, (), ()>::new(
            "test.hold",
            1,
            |_: &HoldInput| Ok(HoldStep::Hold),
            move |task, runtime, cx| {
                let gates = abort_gates.clone();
                async move {
                    if task.input.slow_abort == Some(true) {
                        let gate = gates.gate(&format!("abort.{}", task.input.name));
                        let signal = runtime.signal();
                        tokio::select! {
                            _ = gate.wait() => {}
                            error = aborted(&signal) => return Err(error),
                        }
                    }
                    runtime
                        .commit(|_tx, _current| async { Ok(Some(aborted_state())) }, &cx)
                        .await
                }
            },
        )
        .phase("hold", move |task, runtime, cx| {
            let gates = run_gates.clone();
            async move {
                gates.count_run(&task.input.name);
                let gate = gates.gate(&task.input.name);
                let signal = runtime.signal();
                let ending = tokio::select! {
                    ending = gate.wait() => ending,
                    error = aborted(&signal) => return Err(error),
                };
                let outcome = match ending {
                    Ending::Completed => TaskOutcome::Completed { result: () },
                    Ending::Failed => TaskOutcome::Failed {
                        error: TaskOutcomeError {
                            message: "gate failed".to_owned(),
                            detail: None,
                        },
                        result: None,
                    },
                };
                runtime
                    .commit(
                        move |_tx, _current| async move {
                            Ok(Some(NextTaskState::Terminal { outcome }))
                        },
                        &cx,
                    )
                    .await
            }
        }),
    )
}

/// Waits on the tasks in its input, then completes; its abort handler ends
/// it `aborted`.
fn waiter_task() -> WaiterTask {
    define_task(
        TaskDefinition::<WaiterInput, WaiterStep, (), ()>::new(
            "test.waiter",
            1,
            |_: &WaiterInput| Ok(WaiterStep::Wait),
            |_task, runtime, cx| async move {
                runtime
                    .commit(|_tx, _current| async { Ok(Some(aborted_state())) }, &cx)
                    .await
            },
        )
        .phase("wait", |task, runtime, cx| async move {
            let on = task.input.on.clone();
            runtime
                .commit(
                    move |_tx, _current| async move {
                        Ok(Some(NextTaskState::Waiting {
                            checkpoint: WaiterStep::Done,
                            on,
                            policy: JoinPolicy::AllSettled,
                        }))
                    },
                    &cx,
                )
                .await
        })
        .phase("done", |_task, runtime, cx| async move {
            runtime
                .commit(
                    |_tx, _current| async {
                        Ok(Some(NextTaskState::Terminal {
                            outcome: TaskOutcome::Completed { result: () },
                        }))
                    },
                    &cx,
                )
                .await
        }),
    )
}

/// Never registered: aborting it can only orphan it.
fn unregistered_task() -> HoldTask {
    define_task(
        TaskDefinition::<HoldInput, HoldStep, (), ()>::new(
            "test.unregistered",
            1,
            |_: &HoldInput| Ok(HoldStep::Hold),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("hold", |_task, _runtime, _cx| async { Ok(()) }),
    )
}

/// Per-test gates and the task definitions that read them.
struct World {
    gates: Gates,
    hold: HoldTask,
    waiter: WaiterTask,
}

impl World {
    fn new() -> Self {
        let gates = Gates::default();
        let hold = hold_task(&gates);
        Self {
            gates,
            hold,
            waiter: waiter_task(),
        }
    }

    /// TS `open(name, ending)`.
    fn open(&self, name: &str, ending: Ending) {
        self.gates.gate(name).resolve(ending);
    }
}

fn options(conversation_id: Option<ConversationId>, background: Option<bool>) -> TaskOptions {
    TaskOptions {
        ownership: TaskOwnership::Conversation,
        conversation_id,
        background,
    }
}

async fn create_task_in(
    tx: &Tx,
    task: &HoldTask,
    input: &HoldInput,
    options: TaskOptions,
) -> SessionResult<TaskId> {
    tx.create_task(task.erase().as_definition_ref(), to_json(input)?, options)
        .await
}

#[derive(Clone, Copy, Debug)]
struct Tree {
    owner: TaskId,
    child: ConversationId,
    inner: TaskId,
}

/// Options of [`owned_child`].
#[derive(Clone, Copy, Default)]
struct TreeOptions {
    background: bool,
    slow_inner: bool,
    slow_owner: bool,
}

/// In `parent`, stage task `owner` and a conversation it owns holding task
/// `inner`, in one commit.
async fn owned_child(world: &World, parent: &Conversation, name: &str, tree: TreeOptions) -> Tree {
    let hold = world.hold.clone();
    let name = name.to_owned();
    parent
        .commit(
            move |tx| async move {
                let owner = create_task_in(
                    &tx,
                    &hold,
                    &HoldInput::slow(&name, tree.slow_owner),
                    options(None, Some(tree.background)),
                )
                .await?;
                let child = tx
                    .create_conversation(ConversationOwnership::Task { task_id: owner })
                    .await?;
                let inner = create_task_in(
                    &tx,
                    &hold,
                    &HoldInput::slow(&format!("{name}.inner"), tree.slow_inner),
                    options(Some(child.id), None),
                )
                .await?;
                Ok(Tree {
                    owner,
                    child: child.id,
                    inner,
                })
            },
            context(),
        )
        .await
        .expect("stage the owned child")
}

/// A faux response held until cancellation; `reached` resolves when the
/// request is sent. TS also returns `release`, which no test here calls.
struct Gated {
    step: FauxResponseStep,
    reached: Deferred,
}

fn gated(message: AssistantMessage) -> Gated {
    let reached: Deferred = deferred();
    let gate: Deferred = deferred();
    let reach = reached.clone();
    let step = FauxResponseStep::Factory(Arc::new(move |_, options, _, _| {
        reach.resolve(());
        let signal = options.and_then(|options| options.stream.request.signal.clone());
        let (gate, message) = (gate.clone(), message.clone());
        async move {
            let signal = signal.expect("the request carries a signal");
            tokio::select! {
                () = gate.wait() => Ok(message),
                reason = signal.cancelled() => Err(reason),
            }
        }
        .boxed()
    }));
    Gated { step, reached }
}

/// Mark a conversation busy with `task` standing in for its run, so
/// submissions queue.
async fn busy(conversation: &Conversation, task: TaskId) {
    let id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                tx.doc(&LIVE_DOC, id)
                    .await?
                    .set("run", json(&format!(r#"{{"taskId":{task},"inputs":[]}}"#)))?;
                Ok(())
            },
            context(),
        )
        .await
        .expect("mark the conversation busy");
}

async fn status(harness: &Harness, id: TaskId) -> TaskState {
    harness
        .get_task(id, context())
        .await
        .expect("read the task")
        .expect("the task exists")
        .state
}

async fn abort_requested(harness: &Harness, id: TaskId) -> bool {
    harness
        .get_task(id, context())
        .await
        .expect("read the task")
        .expect("the task exists")
        .abort_requested
}

/// TS `(await harness.waitForTask(id, context)).state.outcome.status`.
async fn outcome_of(harness: &Harness, id: TaskId) -> TaskOutcomeStatus {
    harness
        .wait_for_task(id, context())
        .await
        .expect("wait for the task")
        .outcome
        .status()
}

/// TS `waitUntil` over a task's status.
async fn until_status(harness: &Harness, id: TaskId, expected: TaskStatus) {
    wait_for(
        || async move { status(harness, id).await.status() == expected },
        WAIT_UNTIL_MS,
    )
    .await;
}

/// TS `waitUntil` over a task's abort mark.
async fn until_abort_requested(harness: &Harness, id: TaskId) {
    wait_for(
        || async move { abort_requested(harness, id).await },
        WAIT_UNTIL_MS,
    )
    .await;
}

async fn submission_record(harness: &Harness, id: SubmissionId) -> SubmissionRecord {
    harness
        .submission(id, context())
        .await
        .expect("reacquire the submission")
        .expect("the submission exists")
        .status(context())
        .await
        .expect("read the submission")
}

/// A Harness over the [`World`]'s tasks, its root, and its reports.
struct Opened {
    harness: Harness,
    root: Conversation,
    reports: Reports,
}

async fn open_harness(world: &World, storage: Arc<dyn Storage>) -> Opened {
    let OpenedTasks {
        harness, reports, ..
    } = open_tasks(
        storage,
        &[world.hold.erase(), world.waiter.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .expect("root conversation");
    harness.resume().expect("resume the Harness");
    Opened {
        harness,
        root,
        reports,
    }
}

/// Storage that rejects, once, a commit that marks the task in `mark` (TS
/// `Rejecting` and the patched `storage.commit`).
struct RejectMark {
    inner: Arc<dyn Storage>,
    mark: Arc<Mutex<Option<TaskId>>>,
}

impl RejectMark {
    fn marks(&self, writes: &[StorageWrite]) -> bool {
        let mut mark = self.mark.lock().unwrap_or_else(PoisonError::into_inner);
        let Some(id) = *mark else {
            return false;
        };
        let marks = writes.iter().any(|write| {
            matches!(write, StorageWrite::Task { value } if value.id == id && value.abort_requested)
        });
        if marks {
            *mark = None;
        }
        marks
    }
}

impl Storage for RejectMark {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        if self.marks(writes) {
            return futures::future::ready(Err(StorageRejected::new("rejected once").into()))
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

    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        self.inner.close(cx)
    }
}

fn is_rejection(error: &SessionError) -> bool {
    matches!(error, SessionError::Storage(storage) if storage.is_rejected())
}
