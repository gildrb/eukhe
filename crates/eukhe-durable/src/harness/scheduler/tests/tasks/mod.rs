//! Port of `test/harness-tasks.test.ts`: the file's local helpers (`oneStep`,
//! `gated`, `start`, `openRoot`, `markDurably`, `withSignal`) here, one
//! submodule per `describe`.

mod abort;
mod close;
mod phases;
mod runtime;
mod scheduling;

use std::future::Future;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::{with_abort_signal, AbortError, AbortReason, AbortSignal, Context};
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use futures::future::BoxFuture;
use serde::{Deserialize, Serialize};
use tokio::task::JoinHandle;

use crate::harness::registry::Registry;
use crate::harness::tests::support::context;
use crate::harness::tests::task_support::{
    aborted_with, completed, eventually, flush, open_tasks, Deferred, OpenTasksOptions,
    OpenedTasks, Reports,
};
use crate::harness::{Conversation, Harness, RootOptions, TaskAbortResult};
use crate::session::tests::support::Gate;
use crate::session::{SessionError, SessionResult};
use crate::storage::MemoryStorage;
use crate::tasks::{
    define_task, AnyTask, NextTaskState, RunningTask, Task, TaskDefinition, TaskRuntime, TaskValue,
};
use crate::types::{
    AnyTaskRecord, ConversationId, EntryDraft, Storage, StorageWrite, TaskId, TaskOptions,
    TaskOutcome, TaskOutcomeError, TaskOwnership,
};

/// Checkpoint of a one-phase task (TS `Step`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
pub(super) enum Step {
    Run,
}

/// A one-phase task with a `null` input.
pub(super) type StepTask<R = ()> = Task<(), Step, R, ()>;
/// Runtime of a [`StepTask`] (TS `StepRuntime<R>`).
pub(super) type StepRuntime<R = ()> = TaskRuntime<(), Step, R, ()>;
/// The running task a [`StepTask`] phase receives.
pub(super) type StepRun<R = ()> = RunningTask<(), Step, R>;

/// Value shared between a test and its task handlers.
pub(super) type Shared<T> = Arc<Mutex<T>>;

pub(super) fn shared<T>(value: T) -> Shared<T> {
    Arc::new(Mutex::new(value))
}

pub(super) fn lock<T>(value: &Mutex<T>) -> MutexGuard<'_, T> {
    value.lock().unwrap_or_else(PoisonError::into_inner)
}

/// A one-phase task whose abort handler settles `aborted` with reason
/// "test" (TS `oneStep(name, run)`).
pub(super) fn one_step<R, F, Fut>(name: &str, run: F) -> StepTask<R>
where
    R: TaskValue,
    F: Fn(StepRun<R>, StepRuntime<R>, Context) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = SessionResult<()>> + Send + 'static,
{
    one_step_with_abort(
        name,
        run,
        |runtime: StepRuntime<R>, cx: Context| async move { abort_with(&runtime, "test", &cx).await },
    )
}

/// A one-phase task with its own abort handler (TS `oneStep(name, run, abort)`).
pub(super) fn one_step_with_abort<R, F, Fut, A, AFut>(name: &str, run: F, abort: A) -> StepTask<R>
where
    R: TaskValue,
    F: Fn(StepRun<R>, StepRuntime<R>, Context) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = SessionResult<()>> + Send + 'static,
    A: Fn(StepRuntime<R>, Context) -> AFut + Send + Sync + 'static,
    AFut: Future<Output = SessionResult<()>> + Send + 'static,
{
    define_task(
        TaskDefinition::new(
            name,
            1,
            |(): &()| Ok(Step::Run),
            move |_task, runtime, cx| abort(runtime, cx),
        )
        .phase("run", run),
    )
}

/// A one-phase task that waits for `gate` and completes with `null`.
pub(super) fn gated(name: &str, gate: &Deferred) -> StepTask {
    let gate = gate.clone();
    one_step(name, move |_task, runtime: StepRuntime, cx| {
        let opened = gate.wait();
        async move {
            opened.await;
            complete(&runtime, (), &cx).await
        }
    })
}

/// Commit `completed(result)`.
pub(super) fn complete<I, S, R, H>(
    runtime: &TaskRuntime<I, S, R, H>,
    result: R,
    cx: &Context,
) -> BoxFuture<'static, SessionResult<()>>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    runtime.commit(
        move |_tx, _current| async move { Ok(Some(completed(result))) },
        cx,
    )
}

/// Commit `abortedWith(reason)`.
pub(super) fn abort_with<I, S, R, H>(
    runtime: &TaskRuntime<I, S, R, H>,
    reason: &str,
    cx: &Context,
) -> BoxFuture<'static, SessionResult<()>>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    let next = aborted_with(reason);
    runtime.commit(move |_tx, _current| async move { Ok(Some(next)) }, cx)
}

/// Commit progress to `checkpoint`.
pub(super) fn advance<I, S, R, H>(
    runtime: &TaskRuntime<I, S, R, H>,
    checkpoint: S,
    cx: &Context,
) -> BoxFuture<'static, SessionResult<()>>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    runtime.commit(
        move |_tx, _current| async move { Ok(Some(NextTaskState::Running { checkpoint })) },
        cx,
    )
}

/// Create a conversation-owned task of `task` in `conversation`.
pub(super) async fn create<I, S, R, H>(
    conversation: &Conversation,
    task: &Task<I, S, R, H>,
    input: &I,
) -> TaskId<R>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    create_with(conversation, task, input, None).await
}

async fn create_with<I, S, R, H>(
    conversation: &Conversation,
    task: &Task<I, S, R, H>,
    input: &I,
    background: Option<bool>,
) -> TaskId<R>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    let definition = task.erase().as_definition_ref();
    let input = to_json(input).expect("the input is JSON");
    let id = conversation
        .commit(
            move |tx| async move {
                tx.create_task(
                    definition,
                    input,
                    TaskOptions {
                        ownership: TaskOwnership::Conversation,
                        conversation_id: None,
                        background,
                        abandon_on_restart: None,
                    },
                )
                .await
            },
            context(),
        )
        .await
        .expect("create the task");
    TaskId::from_number(id.get())
}

/// TS `start(conversation, task)`.
pub(super) async fn start<R: TaskValue>(
    conversation: &Conversation,
    task: &StepTask<R>,
) -> TaskId<R> {
    create(conversation, task, &()).await
}

/// TS `start(conversation, task, { background: true })`.
pub(super) async fn start_background<R: TaskValue>(
    conversation: &Conversation,
    task: &StepTask<R>,
) -> TaskId<R> {
    create_with(conversation, task, &(), Some(true)).await
}

/// What [`open_root`] opened: [`open_tasks`] plus the root conversation.
pub(super) struct OpenedRoot {
    pub(super) harness: Harness,
    pub(super) registry: Registry,
    pub(super) reports: Reports,
    pub(super) root: Conversation,
}

/// TS `openRoot(tasks)` over a fresh memory storage.
pub(super) async fn open_root(tasks: &[AnyTask]) -> OpenedRoot {
    open_root_with(
        Arc::new(MemoryStorage::new()),
        tasks,
        OpenTasksOptions::default(),
    )
    .await
}

/// TS `openRoot(tasks, { storage, ...options })`.
pub(super) async fn open_root_with(
    storage: Arc<dyn Storage>,
    tasks: &[AnyTask],
    options: OpenTasksOptions,
) -> OpenedRoot {
    let OpenedTasks {
        harness,
        registry,
        reports,
    } = open_tasks(storage, tasks, options).await;
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .expect("open the root conversation");
    OpenedRoot {
        harness,
        registry,
        reports,
        root,
    }
}

/// Start `abort_task()` and return once its mark is durable, before it has
/// joined the run (TS `markDurably`).
pub(super) async fn mark_durably(
    harness: &Harness,
    id: TaskId,
) -> JoinHandle<SessionResult<TaskAbortResult>> {
    let aborting = tokio::spawn(harness.abort_task(id, context()));
    while !abort_requested(harness, id).await {
        flush().await;
    }
    aborting
}

/// Whether the committed record of `id` carries the abort mark.
pub(super) async fn abort_requested(harness: &Harness, id: TaskId) -> bool {
    harness
        .get_task(id, context())
        .await
        .expect("read the task")
        .is_some_and(|record| record.abort_requested)
}

/// The test context with `signal` (TS `withSignal`).
pub(super) fn with_signal(signal: &AbortSignal) -> Context {
    with_abort_signal(signal, context())
}

/// TS `new Error(message)` as an abort reason.
pub(super) fn reason(message: &str) -> AbortReason {
    Arc::new(SessionError::error(message))
}

/// TS `error.name`: `AbortError` for a default abort reason.
pub(super) fn error_name(error: &SessionError) -> &'static str {
    match error {
        SessionError::Aborted(reason) if reason.is::<AbortError>() => "AbortError",
        _ => "Error",
    }
}

/// TS `await expect(promise).rejects.toThrow(needle)`.
#[track_caller]
pub(super) fn assert_rejects<T: std::fmt::Debug>(result: SessionResult<T>, needle: &str) {
    let error = result.expect_err(needle);
    assert!(error.to_string().contains(needle), "{error}");
}

/// Result of a spawned operation.
pub(super) async fn joined<T>(handle: JoinHandle<T>) -> T {
    handle.await.expect("the spawned operation does not panic")
}

/// The terminal outcome of `id`.
pub(super) async fn outcome<R>(harness: &Harness, id: TaskId<R>) -> TaskOutcome {
    harness
        .wait_for_task(id, context())
        .await
        .expect("wait for the task")
        .outcome
}

pub(super) fn faulted(message: &str) -> TaskOutcome {
    TaskOutcome::Faulted {
        error: TaskOutcomeError {
            message: message.to_owned(),
            detail: None,
        },
    }
}

pub(super) fn aborted_outcome(reason: &str) -> TaskOutcome {
    TaskOutcome::Aborted {
        reason: Some(reason.to_owned()),
        result: None,
    }
}

pub(super) fn completed_outcome<R: Serialize>(result: &R) -> TaskOutcome {
    TaskOutcome::Completed {
        result: to_json(result).expect("the result is JSON"),
    }
}

pub(super) fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON")
}

/// `{ text: string }` documents of the tests.
#[derive(Debug, Default, Clone, PartialEq, Serialize, Deserialize)]
pub(super) struct Text {
    pub(super) text: String,
}

/// `value?.text` of a `{ text }` document value.
pub(super) fn text_of(value: Option<Arc<JsonObject>>) -> Option<String> {
    value.map(|value| {
        from_json::<Text>(&JsonValue::Object(value))
            .expect("a text document")
            .text
    })
}

/// Task records of `id` written by `commits`, in order.
pub(super) fn task_writes(commits: &[Vec<StorageWrite>], id: TaskId) -> Vec<AnyTaskRecord> {
    commits
        .iter()
        .flatten()
        .filter_map(|write| match write {
            StorageWrite::Task { value } if value.id == id => Some(value.clone()),
            _ => None,
        })
        .collect()
}

/// Queue an entry commit of kind `blocker` in `conversation` without waiting
/// for it (TS `void harness.commit(...)`).
pub(super) fn queue_blocker(harness: &Harness, conversation: ConversationId) {
    drop(tokio::spawn(harness.commit(
        move |tx| async move {
            tx.append_entry(conversation, EntryDraft::new("blocker"))
                .await?;
            Ok(())
        },
        context(),
    )));
}

/// Wait until a handler stored its commit gate and a commit entered it.
pub(super) async fn held_gate(held: &Shared<Option<Gate>>) {
    eventually(|| std::future::ready(lock(held).is_some())).await;
    let entered = lock(held)
        .as_ref()
        .expect("the handler held commits")
        .entered();
    entered.await;
}

/// Release the gate a handler stored.
pub(super) fn release_gate(held: &Shared<Option<Gate>>) {
    lock(held)
        .as_ref()
        .expect("the handler held commits")
        .release();
}

/// Run a test body as a spawned task: `#[tokio::test]` polls its main future
/// only after a batch of ready spawned tasks, while a TS test continuation is
/// an ordinary microtask; a spawned body gets FIFO fairness like one.
pub(super) async fn as_task(body: impl Future<Output = ()> + Send + 'static) {
    joined(tokio::spawn(body)).await;
}
