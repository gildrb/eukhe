//! Port of `test/harness-structured.test.ts`: structured concurrency of
//! tasks (ownership, waits, held outcomes, bottom-up aborts, recovery, and
//! the built-in tool rounds).
//!
//! The TS module-level `behaviors`, `gates`, and `log` maps are per-test
//! state here: every test builds its own [`Script`], whose `test.node` task
//! runs the behaviors scripted for its input name. Values the TS tests keep
//! in closure variables (`let child`, `found.ids`, `found.outcomes`) live in
//! the script's slots and lists, so behaviors reach them through the script
//! they receive instead of capturing it.

mod abort_order;
mod boundaries;
mod chat;
mod completing;
mod conversation_abort;
mod definitions;
mod ownership;
mod ownership_recovery;
mod recovery;
mod rejecting;
mod tool_round_events;
mod tool_rounds;
mod waiting;

use std::collections::HashMap;
use std::future::Future;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use eukhe_chord::context::Context;
use eukhe_chord::json::{to_json, JsonValue};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use tempfile::TempDir;

use crate::documents::{DocDefinition, TaskDoc};
use crate::harness::registry::Registry;
use crate::harness::tests::chat_support::wait_for;
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{
    aborted, deferred, open_tasks, Deferred, OpenTasksOptions, Reports,
};
use crate::harness::types::TaskInspectionState;
use crate::harness::{Conversation, Harness, RootOptions};
use crate::session::{create_session, SessionError, SessionResult, Tx};
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::storage::MemoryStorage;
use crate::tasks::{define_task, AnyTask, NextTaskState, Task, TaskDefinition, TaskRuntime};
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationOwnership, JoinPolicy, Storage, TaskId, TaskOptions,
    TaskOutcome, TaskOutcomeError, TaskOutcomeStatus, TaskOwnership, TaskState, TaskStatus,
};

// ─── A scriptable task ──────────────────────────────────────────────────────

/// Input of `test.node`: the name that selects its behavior.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct NodeInput {
    pub(super) name: String,
}

/// Checkpoint of `test.node`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
pub(super) enum NodeCheckpoint {
    Run,
    Resume { round: u64 },
}

pub(super) type NodeRuntime = TaskRuntime<NodeInput, NodeCheckpoint, String, ()>;
pub(super) type Next = NextTaskState<NodeCheckpoint, String>;

type Handler = Arc<
    dyn Fn(Arc<Script>, NodeRuntime, Context) -> BoxFuture<'static, SessionResult<()>>
        + Send
        + Sync,
>;
type ResumeHandler = Arc<
    dyn Fn(Arc<Script>, NodeRuntime, Context, u64) -> BoxFuture<'static, SessionResult<()>>
        + Send
        + Sync,
>;

/// Per-name behavior of `test.node`; unscripted parts use the defaults.
#[derive(Clone, Default)]
pub(super) struct Behavior {
    run: Option<Handler>,
    resume: Option<ResumeHandler>,
    abort: Option<Handler>,
}

impl Behavior {
    #[must_use]
    pub(super) fn run<F, Fut>(mut self, handler: F) -> Self
    where
        F: Fn(Arc<Script>, NodeRuntime, Context) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = SessionResult<()>> + Send + 'static,
    {
        self.run = Some(Arc::new(move |script, runtime, cx| {
            handler(script, runtime, cx).boxed()
        }));
        self
    }

    #[must_use]
    pub(super) fn resume<F, Fut>(mut self, handler: F) -> Self
    where
        F: Fn(Arc<Script>, NodeRuntime, Context, u64) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = SessionResult<()>> + Send + 'static,
    {
        self.resume = Some(Arc::new(move |script, runtime, cx, round| {
            handler(script, runtime, cx, round).boxed()
        }));
        self
    }

    #[must_use]
    pub(super) fn abort<F, Fut>(mut self, handler: F) -> Self
    where
        F: Fn(Arc<Script>, NodeRuntime, Context) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = SessionResult<()>> + Send + 'static,
    {
        self.abort = Some(Arc::new(move |script, runtime, cx| {
            handler(script, runtime, cx).boxed()
        }));
        self
    }

    /// An abort handler that waits for the gate `gate`, then commits
    /// `aborted`.
    #[must_use]
    pub(super) fn gated_abort(self, gate: &'static str) -> Self {
        self.abort(move |script, runtime, cx| async move {
            script.gate(gate).wait().await;
            runtime
                .commit(|_, _| async { Ok(Some(aborted_next())) }, &cx)
                .await
        })
    }
}

/// How a default run ends once its gate opens: its outcome, or a throw that
/// faults it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Ending {
    Completed,
    Failed,
    Throw,
}

/// The committed outcome of [`end`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum End {
    Completed,
    Failed,
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// One test's script: the `test.node` task, the behaviors and gates it runs
/// with, the handler log, and the values behaviors record for the test.
pub(super) struct Script {
    node: AnyTask,
    unregistered: AnyTask,
    behaviors: Mutex<HashMap<String, Behavior>>,
    gates: Mutex<HashMap<String, Deferred<Ending>>>,
    /// Handler starts and ends in order, such as `run:a`, `abort:a`.
    log: Mutex<Vec<String>>,
    slots: Mutex<HashMap<String, Deferred<TaskId>>>,
    conversations: Mutex<HashMap<String, Deferred<ConversationId>>>,
    lists: Mutex<HashMap<String, Vec<TaskId>>>,
    outcomes: Mutex<HashMap<String, Vec<TaskOutcomeStatus>>>,
    harness: Mutex<Option<Harness>>,
}

impl Script {
    pub(super) fn new() -> Arc<Self> {
        Arc::new_cyclic(|script: &Weak<Self>| Self {
            node: node_task(script.clone()).erase(),
            unregistered: unregistered_task().erase(),
            behaviors: Mutex::default(),
            gates: Mutex::default(),
            log: Mutex::default(),
            slots: Mutex::default(),
            conversations: Mutex::default(),
            lists: Mutex::default(),
            outcomes: Mutex::default(),
            harness: Mutex::default(),
        })
    }

    /// The `test.node` task (TS `Node`).
    pub(super) fn node(&self) -> &AnyTask {
        &self.node
    }

    /// Never registered: aborting it can only orphan it (TS `Unregistered`).
    pub(super) fn unregistered(&self) -> &AnyTask {
        &self.unregistered
    }

    pub(super) fn gate(&self, name: &str) -> Deferred<Ending> {
        lock(&self.gates)
            .entry(name.to_owned())
            .or_insert_with(deferred)
            .clone()
    }

    /// TS `open(name)`.
    pub(super) fn open(&self, name: &str) {
        self.open_with(name, Ending::Completed);
    }

    /// TS `open(name, ending)`.
    pub(super) fn open_with(&self, name: &str, ending: Ending) {
        self.gate(name).resolve(ending);
    }

    pub(super) fn script(&self, name: &str, behavior: Behavior) {
        lock(&self.behaviors).insert(name.to_owned(), behavior);
    }

    fn behavior(&self, name: &str) -> Behavior {
        lock(&self.behaviors).get(name).cloned().unwrap_or_default()
    }

    pub(super) fn push_log(&self, line: String) {
        lock(&self.log).push(line);
    }

    pub(super) fn log(&self) -> Vec<String> {
        lock(&self.log).clone()
    }

    /// TS `log.includes(line)`.
    pub(super) fn logged(&self, line: &str) -> bool {
        lock(&self.log).iter().any(|entry| entry == line)
    }

    /// TS `log.filter((line) => line.startsWith(prefix))`.
    pub(super) fn log_starting(&self, prefix: &str) -> Vec<String> {
        lock(&self.log)
            .iter()
            .filter(|line| line.starts_with(prefix))
            .cloned()
            .collect()
    }

    /// The recorded task ID of `key`, once recorded (TS `until(() => child
    /// !== undefined)`, then `child!`).
    pub(super) async fn id(&self, key: &str) -> TaskId {
        let slot = &self.slot(key);
        until(|| async move { slot.is_settled() }).await;
        slot.wait().await
    }

    /// The recorded conversation ID of `key`, once recorded.
    pub(super) async fn conversation_id(&self, key: &str) -> ConversationId {
        let slot = &self.conversation_slot(key);
        until(|| async move { slot.is_settled() }).await;
        slot.wait().await
    }

    /// A task ID a behavior records once (TS `let child: TaskId | undefined`).
    pub(super) fn slot(&self, key: &str) -> Deferred<TaskId> {
        lock(&self.slots)
            .entry(key.to_owned())
            .or_insert_with(deferred)
            .clone()
    }

    /// A conversation ID a behavior records once.
    pub(super) fn conversation_slot(&self, key: &str) -> Deferred<ConversationId> {
        lock(&self.conversations)
            .entry(key.to_owned())
            .or_insert_with(deferred)
            .clone()
    }

    pub(super) fn push_id(&self, list: &str, id: TaskId) {
        lock(&self.lists)
            .entry(list.to_owned())
            .or_default()
            .push(id);
    }

    pub(super) fn ids(&self, list: &str) -> Vec<TaskId> {
        lock(&self.lists).get(list).cloned().unwrap_or_default()
    }

    pub(super) fn set_ids(&self, list: &str, ids: Vec<TaskId>) {
        lock(&self.lists).insert(list.to_owned(), ids);
    }

    pub(super) fn set_outcomes(&self, key: &str, outcomes: Vec<TaskOutcomeStatus>) {
        lock(&self.outcomes).insert(key.to_owned(), outcomes);
    }

    pub(super) fn outcomes(&self, key: &str) -> Vec<TaskOutcomeStatus> {
        lock(&self.outcomes).get(key).cloned().unwrap_or_default()
    }

    /// The Harness the test opened last.
    pub(super) fn harness(&self) -> Harness {
        lock(&self.harness)
            .clone()
            .expect("the test opened a Harness")
    }

    /// Record the Harness the test opened (TS `opened = harness`).
    pub(super) fn set_harness(&self, harness: &Harness) {
        *lock(&self.harness) = Some(harness.clone());
    }

    /// A child task named `name`, owned by `owner` (TS `spawn`).
    pub(super) async fn spawn(&self, tx: &Tx, owner: TaskId, name: &str) -> SessionResult<TaskId> {
        create(tx, &self.node, name, owned(owner)).await
    }

    /// TS `start(conversation, name, options)`, rejecting.
    pub(super) async fn try_start(
        &self,
        conversation: &Conversation,
        name: &str,
        options: TaskOptions,
    ) -> SessionResult<TaskId> {
        let (node, name) = (self.node.clone(), name.to_owned());
        conversation
            .commit(
                move |tx| async move { create(&tx, &node, &name, options).await },
                context(),
            )
            .await
    }

    /// TS `start(conversation, name)`.
    pub(super) async fn start(&self, conversation: &Conversation, name: &str) -> TaskId {
        self.start_with(conversation, name, OWN_CONVERSATION).await
    }

    /// TS `start(conversation, name, options)`.
    pub(super) async fn start_with(
        &self,
        conversation: &Conversation,
        name: &str,
        options: TaskOptions,
    ) -> TaskId {
        self.try_start(conversation, name, options)
            .await
            .expect("start the task")
    }
}

/// `tx.createTask(task, { name }, options)`.
pub(super) async fn create(
    tx: &Tx,
    task: &AnyTask,
    name: &str,
    options: TaskOptions,
) -> SessionResult<TaskId> {
    let input = to_json(&NodeInput {
        name: name.to_owned(),
    })?;
    tx.create_task(task.as_definition_ref(), input, options)
        .await
}

fn alive(script: Option<Arc<Script>>) -> SessionResult<Arc<Script>> {
    script.ok_or_else(|| SessionError::error("The test script was dropped"))
}

/// Wait for the gate or the abort signal, then end as the gate says.
async fn default_run(
    script: Arc<Script>,
    runtime: NodeRuntime,
    cx: Context,
    name: String,
) -> SessionResult<()> {
    let gate = script.gate(&name).wait();
    let signal = runtime.signal();
    let ending = tokio::select! {
        biased;
        ending = gate => ending,
        error = aborted(&signal) => return Err(error),
    };
    let end_as = match ending {
        Ending::Throw => return Err(SessionError::error(format!("{name} threw"))),
        Ending::Completed => End::Completed,
        Ending::Failed => End::Failed,
    };
    runtime
        .commit(move |_, _| async move { Ok(Some(end(end_as, &name))) }, &cx)
        .await
}

/// A task that runs its name's behavior.
fn node_task(script: Weak<Script>) -> Task<NodeInput, NodeCheckpoint, String, ()> {
    let (run_script, resume_script) = (script.clone(), script.clone());
    define_task(
        TaskDefinition::new(
            "test.node",
            1,
            |_: &NodeInput| Ok(NodeCheckpoint::Run),
            move |task, runtime: NodeRuntime, cx| {
                let script = script.upgrade();
                async move {
                    let script = alive(script)?;
                    let name = task.input.name;
                    script.push_log(format!("abort:{name}"));
                    if let Some(abort) = script.behavior(&name).abort {
                        return abort(script, runtime, cx).await;
                    }
                    runtime
                        .commit(
                            move |_, _| async move {
                                Ok(Some(NextTaskState::Terminal {
                                    outcome: TaskOutcome::Aborted {
                                        reason: None,
                                        result: Some(name),
                                    },
                                }))
                            },
                            &cx,
                        )
                        .await
                }
            },
        )
        .phase("run", move |task, runtime, cx| {
            let script = run_script.upgrade();
            async move {
                let script = alive(script)?;
                let name = task.input.name;
                script.push_log(format!("run:{name}"));
                match script.behavior(&name).run {
                    Some(run) => run(script, runtime, cx).await,
                    None => default_run(script, runtime, cx, name).await,
                }
            }
        })
        .phase("resume", move |task, runtime, cx| {
            let script = resume_script.upgrade();
            async move {
                let script = alive(script)?;
                let name = task.input.name;
                script.push_log(format!("resume:{name}"));
                if let Some(resume) = script.behavior(&name).resume {
                    let NodeCheckpoint::Resume { round } = task.checkpoint else {
                        return Err(SessionError::error("The resume phase has a round"));
                    };
                    return resume(script, runtime, cx, round).await;
                }
                runtime
                    .commit(
                        move |_, _| async move { Ok(Some(end(End::Completed, &name))) },
                        &cx,
                    )
                    .await
            }
        }),
    )
}

/// Never registered: aborting it can only orphan it.
fn unregistered_task() -> Task<NodeInput, NodeCheckpoint, String, ()> {
    define_task(
        TaskDefinition::new(
            "test.unregistered",
            1,
            |_: &NodeInput| Ok(NodeCheckpoint::Run),
            |_, _: NodeRuntime, _| async { Ok(()) },
        )
        .phase("run", |_, _, _| async { Ok(()) }),
    )
}

/// The value of [`TASK_NOTES`].
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct TaskNotes {
    pub(super) text: String,
}

pub(super) static TASK_NOTES: TaskDoc<TaskNotes> = match TaskDoc::define(DocDefinition {
    kind: "test.task-notes",
    version: 1,
    initial: TaskNotes::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

// ─── Next states and options ────────────────────────────────────────────────

/// TS `end(ending, name)`.
pub(super) fn end(ending: End, name: &str) -> Next {
    NextTaskState::Terminal {
        outcome: match ending {
            End::Completed => TaskOutcome::Completed {
                result: name.to_owned(),
            },
            End::Failed => TaskOutcome::Failed {
                error: TaskOutcomeError {
                    message: format!("{name} failed"),
                    detail: None,
                },
                result: None,
            },
        },
    }
}

/// `{ status: "terminal", outcome: { status: "aborted" } }`.
pub(super) fn aborted_next() -> Next {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: None,
            result: None,
        },
    }
}

/// `{ status: "running", checkpoint: { phase: "resume", round } }`.
pub(super) fn running(round: u64) -> Next {
    NextTaskState::Running {
        checkpoint: NodeCheckpoint::Resume { round },
    }
}

/// Wait on `on`, resuming in round `round` (TS `waitOn`).
pub(super) fn wait_on(on: Vec<TaskId>, policy: JoinPolicy, round: u64) -> Next {
    NextTaskState::Waiting {
        checkpoint: NodeCheckpoint::Resume { round },
        on,
        policy,
    }
}

pub(super) const OWN_CONVERSATION: TaskOptions = TaskOptions {
    ownership: TaskOwnership::Conversation,
    conversation_id: None,
    background: None,
};

/// `{ ...OWN_CONVERSATION, conversationId }`.
pub(super) fn in_conversation(conversation_id: ConversationId) -> TaskOptions {
    TaskOptions {
        conversation_id: Some(conversation_id),
        ..OWN_CONVERSATION
    }
}

/// `{ ...OWN_CONVERSATION, background: true }`.
pub(super) const BACKGROUND: TaskOptions = TaskOptions {
    background: Some(true),
    ..OWN_CONVERSATION
};

/// TS `owned(owner)`.
pub(super) fn owned(owner: TaskId) -> TaskOptions {
    TaskOptions {
        ownership: TaskOwnership::Task { task_id: owner },
        conversation_id: None,
        background: None,
    }
}

/// `{ ownership: { kind: "task", taskId } }` of a conversation.
pub(super) fn owned_conversation(owner: TaskId) -> ConversationOwnership {
    ConversationOwnership::Task { task_id: owner }
}

/// Script `parent` to spawn `children` in one commit and wait on them with
/// `policy`; it records their IDs in the list `parent` and their outcome
/// statuses under `parent` (TS `parentOf`).
pub(super) fn parent_of(
    script: &Script,
    parent: &'static str,
    children: &'static [&'static str],
    policy: JoinPolicy,
) {
    script.script(
        parent,
        Behavior::default()
            .run(move |script, runtime, cx| async move {
                let owner = runtime.task_id().erase();
                runtime
                    .commit(
                        move |tx, _| async move {
                            for name in children {
                                let id = script.spawn(&tx, owner, name).await?;
                                script.push_id(parent, id);
                            }
                            Ok(Some(wait_on(script.ids(parent), policy, 1)))
                        },
                        &cx,
                    )
                    .await
            })
            .resume(move |script, runtime, cx, _| async move {
                let outcomes = runtime.outcomes(&script.ids(parent), &cx).await?;
                script.set_outcomes(parent, outcomes.iter().map(TaskOutcome::status).collect());
                runtime
                    .commit(
                        move |_, _| async move { Ok(Some(end(End::Completed, parent))) },
                        &cx,
                    )
                    .await
            }),
    );
}

/// Script `name` to spawn `child` and then complete, holding while the child
/// lives; the child's ID goes to the slot `name` (TS `spawnAndFinish`).
pub(super) fn spawn_and_finish(script: &Script, name: &'static str, child: &'static str) {
    script.script(
        name,
        Behavior::default().run(move |script, runtime, cx| async move {
            let owner = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        let id = script.spawn(&tx, owner, child).await?;
                        script.slot(name).resolve(id);
                        Ok(Some(running(1)))
                    },
                    &cx,
                )
                .await
        }),
    );
}

// ─── Harness helpers ────────────────────────────────────────────────────────

pub(super) struct Opened {
    pub(super) harness: Harness,
    pub(super) root: Conversation,
    pub(super) registry: Registry,
    pub(super) reports: Reports,
}

/// TS `openNodes(storage)`: a Harness running `test.node`, its root, resumed.
pub(super) async fn open_nodes(script: &Script, storage: Arc<dyn Storage>) -> Opened {
    let opened = open_tasks(
        storage,
        &[script.node().clone()],
        OpenTasksOptions::default(),
    )
    .await;
    let root = opened
        .harness
        .root(RootOptions::default(), context())
        .await
        .expect("create the root");
    opened.harness.resume().expect("resume");
    script.set_harness(&opened.harness);
    Opened {
        harness: opened.harness,
        root,
        registry: opened.registry,
        reports: opened.reports,
    }
}

/// TS `openNodes()` over a fresh `MemoryStorage`.
pub(super) async fn open_memory_nodes(script: &Script) -> Opened {
    open_nodes(script, Arc::new(MemoryStorage::new())).await
}

pub(super) async fn record(harness: &Harness, id: TaskId) -> AnyTaskRecord {
    harness
        .get_task(id, context())
        .await
        .expect("read the task")
        .expect("the task exists")
}

/// TS `state(harness, id)`.
pub(super) async fn state(harness: &Harness, id: TaskId) -> TaskState {
    record(harness, id).await.state
}

pub(super) async fn status(harness: &Harness, id: TaskId) -> TaskStatus {
    state(harness, id).await.status()
}

/// TS `outcomeOf(harness, id)`.
pub(super) async fn outcome_of(harness: &Harness, id: TaskId) -> TaskOutcomeStatus {
    settle(harness, id).await.status()
}

/// The terminal outcome of `id`, once settled.
pub(super) async fn settle(harness: &Harness, id: TaskId) -> TaskOutcome {
    harness
        .wait_for_task(id, context())
        .await
        .expect("wait for the task")
        .outcome
}

/// TS `abortRequested` of the committed record.
pub(super) async fn marked(harness: &Harness, id: TaskId) -> bool {
    record(harness, id).await.abort_requested
}

/// TS `until(check)` (`waitFor`, 5 s).
pub(super) async fn until<F, Fut>(check: F)
where
    F: FnMut() -> Fut,
    Fut: Future<Output = bool>,
{
    wait_for(check, 5000).await;
}

/// `until(async () => (await state(harness, id)).status === status)`.
pub(super) async fn until_status(harness: &Harness, id: TaskId, expected: TaskStatus) {
    until(|| async move { status(harness, id).await == expected }).await;
}

/// The inspected state of `id`, if it is live.
pub(super) async fn inspected(harness: &Harness, id: TaskId) -> Option<TaskInspectionState> {
    harness
        .inspect(context())
        .await
        .expect("inspect")
        .tasks
        .into_iter()
        .find(|task| task.record.id == id)
        .map(|task| task.state)
}

/// `expect(outcome).toMatchObject({ status: "faulted", error: { message: expect.stringContaining(text) } })`.
pub(super) fn assert_faulted(outcome: &TaskOutcome, text: &str) {
    match outcome {
        TaskOutcome::Faulted { error } => assert!(
            error.message.contains(text),
            "fault {:?} does not contain {text:?}",
            error.message
        ),
        other => panic!("expected a faulted outcome, got {other:?}"),
    }
}

/// `expect(promise).rejects.toThrow(text)`.
pub(super) fn assert_rejects<T: std::fmt::Debug>(result: SessionResult<T>, text: &str) {
    match result {
        Ok(value) => panic!("expected a rejection containing {text:?}, got {value:?}"),
        Err(error) => assert!(
            error.to_string().contains(text),
            "{error} does not contain {text:?}"
        ),
    }
}

// ─── Recovery helpers ───────────────────────────────────────────────────────

/// TS `sqlitePath()`: a fresh directory, removed when the guard drops.
pub(super) fn sqlite_path() -> (TempDir, PathBuf) {
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-structured-")
        .tempdir()
        .expect("create a temp directory");
    let path = directory.path().join("session.sqlite");
    (directory, path)
}

/// TS `openNodeSqliteStorage(path)`.
pub(super) async fn sqlite(path: &Path) -> Arc<dyn Storage> {
    Arc::new(
        open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
            .await
            .expect("open SQLite storage"),
    )
}

/// What a crash left: `parent` with its children.
pub(super) struct Seeded {
    pub(super) parent: TaskId,
    pub(super) children: Vec<TaskId>,
}

/// One internal task write of [`seed`]: replaces the named fields.
pub(super) struct Patch {
    pub(super) id: TaskId,
    pub(super) abort_requested: Option<bool>,
    pub(super) state: Option<TaskState>,
}

impl Patch {
    /// `{ state }`.
    pub(super) fn state(id: TaskId, state: TaskState) -> Self {
        Self {
            id,
            abort_requested: None,
            state: Some(state),
        }
    }
}

/// Write records a crash could leave, without a Harness: `parent` with
/// children named `children`, then `edit`'s patches replace states through
/// the internal task write, one commit each.
pub(super) async fn seed(
    script: &Script,
    path: &Path,
    children: &[&'static str],
    edit: impl FnOnce(&Seeded) -> Vec<Patch>,
) -> Seeded {
    let session = create_session(sqlite(path).await);
    let (node, children) = (script.node().clone(), children.to_vec());
    let (parent, children) = session
        .commit(
            move |tx| async move {
                let root = tx
                    .create_conversation(ConversationOwnership::Ownerless)
                    .await?;
                let parent = create(&tx, &node, "parent", in_conversation(root.id)).await?;
                let mut ids = Vec::new();
                for name in children {
                    ids.push(create(&tx, &node, name, owned(parent)).await?);
                }
                Ok((parent, ids))
            },
            context(),
        )
        .await
        .expect("seed the tasks");
    let seeded = Seeded { parent, children };
    for patch in edit(&seeded) {
        session
            .commit(
                move |tx| async move {
                    let mut record = tx.task(patch.id).await?.expect("the seeded task exists");
                    if let Some(abort_requested) = patch.abort_requested {
                        record.abort_requested = abort_requested;
                    }
                    if let Some(state) = patch.state {
                        record.state = state;
                    }
                    tx.set_task(record)
                },
                context(),
            )
            .await
            .expect("patch the seeded task");
    }
    session.close(context()).await.expect("close the session");
    seeded
}

/// A JSON value of a JSON literal.
pub(super) fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

/// `{ status: "terminal", outcome: { status: "completed", result: "done" } }`.
pub(super) fn completed_state() -> TaskState {
    TaskState::Terminal {
        outcome: TaskOutcome::Completed {
            result: json(r#""done""#),
        },
    }
}

/// `{ status: "terminal", outcome: { status: "failed", error: { message: "declined" } } }`.
pub(super) fn failed_state() -> TaskState {
    TaskState::Terminal {
        outcome: TaskOutcome::Failed {
            error: TaskOutcomeError {
                message: "declined".to_owned(),
                detail: None,
            },
            result: None,
        },
    }
}

/// `{ status: "waiting", checkpoint: { phase: "resume", round: 1 }, on, policy }`.
pub(super) fn waiting_state(on: Vec<TaskId>, policy: JoinPolicy) -> TaskState {
    TaskState::Waiting {
        checkpoint: to_json(&NodeCheckpoint::Resume { round: 1 }).expect("JSON checkpoint"),
        on,
        policy,
    }
}
