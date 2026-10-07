//! Operations of one task invocation (TS `TaskRuntime`, `RunningTask`,
//! `NextTaskState`, `HookRunner`, and the harness `SettledTask`).
//!
//! The scheduler implements the erased [`TaskRuntimeBackend`] over JSON
//! records; [`TaskRuntime`] is the typed view a phase handler receives.

use std::future::Future;
use std::marker::PhantomData;
use std::sync::Arc;

use eukhe_chord::context::{AbortSignal, Context};
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_pi_ai::models::Models;
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::de::DeserializeOwned;
use serde::Serialize;

use super::definition::TaskValue;
use crate::documents::{AnyDocDefinition, ResolvedAddress};
use crate::entries::Entry;
use crate::env::ExecutionEnv;
use crate::harness::types::{
    Agent, ContextView, ConversationHandle, HookApi, HookHandlers, RegistrySnapshot, Settings,
};
use crate::session::{DocumentWatch, SessionError, SessionResult, Tx};
use crate::types::{
    AnyTaskRecord, ConversationId, DocumentObserver, DocumentReader, EntryData, EntryId,
    EntryRecord, JoinPolicy, JsonObject, TaskId, TaskOutcome, TaskRecord, TaskState, TypedEntry,
};

/// Convert between two serde shapes of one JSON value.
pub(crate) fn recode<T: Serialize + ?Sized, U: DeserializeOwned>(value: &T) -> SessionResult<U> {
    Ok(from_json(&to_json(value)?)?)
}

fn retype<R, T>(id: TaskId<R>) -> TaskId<T> {
    TaskId::from_number(id.get())
}

/// Live task record reserved by one invocation (TS `RunningTask`: a
/// `TaskRecord` whose state is `running`, with the checkpoint lifted).
#[derive(Debug, Clone, PartialEq)]
pub struct RunningTask<I = JsonValue, S = JsonValue, R = JsonValue> {
    pub id: TaskId<R>,
    pub conversation_id: ConversationId,
    pub kind: String,
    pub version: u64,
    pub input: I,
    pub owner: Option<TaskId>,
    pub background: bool,
    pub abort_requested: bool,
    /// The running state's checkpoint.
    pub checkpoint: S,
    pub memos: Option<Arc<JsonObject>>,
}

impl RunningTask {
    /// The running task of `record`; `None` unless its state is `running`.
    #[must_use]
    pub fn from_record(record: AnyTaskRecord) -> Option<Self> {
        let TaskState::Running { checkpoint } = record.state else {
            return None;
        };
        Some(Self {
            id: record.id,
            conversation_id: record.conversation_id,
            kind: record.kind,
            version: record.version,
            input: record.input,
            owner: record.owner,
            background: record.background,
            abort_requested: record.abort_requested,
            checkpoint,
            memos: record.memos,
        })
    }

    /// The typed view of this erased task.
    ///
    /// # Errors
    ///
    /// The input or checkpoint does not decode as `I` or `S`.
    pub fn decode<I: DeserializeOwned, S: DeserializeOwned, R>(
        self,
    ) -> SessionResult<RunningTask<I, S, R>> {
        Ok(RunningTask {
            id: retype(self.id),
            conversation_id: self.conversation_id,
            kind: self.kind,
            version: self.version,
            input: from_json(&self.input)?,
            owner: self.owner,
            background: self.background,
            abort_requested: self.abort_requested,
            checkpoint: from_json(&self.checkpoint)?,
            memos: self.memos,
        })
    }
}

impl<I, S, R> RunningTask<I, S, R> {
    /// The complete record.
    #[must_use]
    pub fn into_record(self) -> TaskRecord<I, S, R> {
        TaskRecord {
            id: self.id,
            conversation_id: self.conversation_id,
            kind: self.kind,
            version: self.version,
            input: self.input,
            owner: self.owner,
            background: self.background,
            abort_requested: self.abort_requested,
            state: TaskState::Running {
                checkpoint: self.checkpoint,
            },
            memos: self.memos,
        }
    }

    /// The erased view.
    ///
    /// # Errors
    ///
    /// The input or checkpoint is not strict JSON.
    pub fn encode(&self) -> SessionResult<RunningTask>
    where
        I: Serialize,
        S: Serialize,
    {
        Ok(RunningTask {
            id: retype(self.id),
            conversation_id: self.conversation_id,
            kind: self.kind.clone(),
            version: self.version,
            input: to_json(&self.input)?,
            owner: self.owner,
            background: self.background,
            abort_requested: self.abort_requested,
            checkpoint: to_json(&self.checkpoint)?,
            memos: self.memos.clone(),
        })
    }
}

/// Next state a task commits for itself: a replacement checkpoint, a wait,
/// or its outcome (TS `NextTaskState`). A returned `Terminal` state is
/// stored as `completing` while ordinary owned work below the task is live
/// (spec §5.5).
#[derive(Debug, Clone, PartialEq)]
pub enum NextTaskState<S = JsonValue, R = JsonValue> {
    Running {
        checkpoint: S,
    },
    Waiting {
        checkpoint: S,
        on: Vec<TaskId>,
        policy: JoinPolicy,
    },
    Terminal {
        outcome: TaskOutcome<R>,
    },
}

impl<S, R> NextTaskState<S, R> {
    /// The task state this replaces the current one with.
    #[must_use]
    pub fn into_state(self) -> TaskState<S, R> {
        match self {
            Self::Running { checkpoint } => TaskState::Running { checkpoint },
            Self::Waiting {
                checkpoint,
                on,
                policy,
            } => TaskState::Waiting {
                checkpoint,
                on,
                policy,
            },
            Self::Terminal { outcome } => TaskState::Terminal { outcome },
        }
    }

    /// The erased state.
    ///
    /// # Errors
    ///
    /// The checkpoint or result is not strict JSON.
    pub fn encode(&self) -> SessionResult<NextTaskState>
    where
        S: Serialize,
        R: Serialize,
    {
        Ok(match self {
            Self::Running { checkpoint } => NextTaskState::Running {
                checkpoint: to_json(checkpoint)?,
            },
            Self::Waiting {
                checkpoint,
                on,
                policy,
            } => NextTaskState::Waiting {
                checkpoint: to_json(checkpoint)?,
                on: on.clone(),
                policy: *policy,
            },
            Self::Terminal { outcome } => NextTaskState::Terminal {
                outcome: recode(outcome)?,
            },
        })
    }
}

/// Terminal task receipt (TS `SettledTask<R>`: a `TaskRecord` whose state is
/// `terminal`, with the outcome lifted).
#[derive(Debug, Clone, PartialEq)]
pub struct SettledTask<R = JsonValue> {
    pub id: TaskId<R>,
    pub conversation_id: ConversationId,
    pub kind: String,
    pub version: u64,
    pub input: JsonValue,
    pub owner: Option<TaskId>,
    pub background: bool,
    pub abort_requested: bool,
    /// The terminal state's outcome.
    pub outcome: TaskOutcome<R>,
    pub memos: Option<Arc<JsonObject>>,
}

impl SettledTask {
    /// The settled task of `record`; `None` unless its state is `terminal`.
    #[must_use]
    pub fn from_record(record: AnyTaskRecord) -> Option<Self> {
        let TaskState::Terminal { outcome } = record.state else {
            return None;
        };
        Some(Self {
            id: record.id,
            conversation_id: record.conversation_id,
            kind: record.kind,
            version: record.version,
            input: record.input,
            owner: record.owner,
            background: record.background,
            abort_requested: record.abort_requested,
            outcome,
            memos: record.memos,
        })
    }

    /// The receipt with a typed result.
    ///
    /// # Errors
    ///
    /// The result does not decode as `R`.
    pub fn decode<R: DeserializeOwned>(self) -> SessionResult<SettledTask<R>> {
        Ok(SettledTask {
            id: retype(self.id),
            conversation_id: self.conversation_id,
            kind: self.kind,
            version: self.version,
            input: self.input,
            owner: self.owner,
            background: self.background,
            abort_requested: self.abort_requested,
            outcome: recode(&self.outcome)?,
            memos: self.memos,
        })
    }
}

impl<R> SettledTask<R> {
    /// The complete record.
    #[must_use]
    pub fn into_record(self) -> TaskRecord<JsonValue, JsonValue, R> {
        TaskRecord {
            id: self.id,
            conversation_id: self.conversation_id,
            kind: self.kind,
            version: self.version,
            input: self.input,
            owner: self.owner,
            background: self.background,
            abort_requested: self.abort_requested,
            state: TaskState::Terminal {
                outcome: self.outcome,
            },
            memos: self.memos,
        }
    }
}

/// An erased `runtime.commit()` change: `(tx, current)` to the next state,
/// `None` leaving the state unchanged.
pub type TaskCommitChange = Box<
    dyn FnOnce(Tx, RunningTask) -> BoxFuture<'static, SessionResult<Option<NextTaskState>>> + Send,
>;

/// Operations of one task invocation over erased JSON records (TS
/// `ErasedRuntime`). The scheduler implements it once per invocation.
///
/// Every operation rejects with the invocation's end error after the
/// invocation ended; document watches acquired through it stop at
/// invocation end.
pub trait TaskRuntimeBackend: DocumentReader + DocumentObserver {
    /// The invocation's task.
    fn task_id(&self) -> TaskId;
    /// The task's conversation.
    fn conversation_id(&self) -> ConversationId;
    /// Aborted when the run is signalled by `abortTask()`, the Harness
    /// closes, or the invocation ends.
    fn signal(&self) -> AbortSignal;
    /// Registry snapshot of the current phase; refreshed at every phase
    /// boundary.
    fn registry(&self) -> RegistrySnapshot;
    /// The task's conversation's agent, resolved at most once per phase, at
    /// first use, and fixed for the phase.
    fn agent(&self, cx: &Context) -> BoxFuture<'static, SessionResult<Arc<Agent>>>;
    /// `HarnessOptions.settings`, resolved at each access.
    fn settings(&self) -> Settings;
    /// pi-ai model access.
    fn models(&self) -> Models;
    /// Calls `HarnessOptions.env` for the task's conversation; rejects with
    /// its error.
    fn env(&self, cx: &Context)
        -> BoxFuture<'static, SessionResult<Option<Arc<dyn ExecutionEnv>>>>;
    /// Handler objects of this task's name from the extensions the phase's
    /// agent selects, in extension order (`agent_hooks(agent, name)` of the
    /// phase agent, resolved with the invocation's context).
    fn hook_handlers(&self) -> BoxFuture<'static, SessionResult<Vec<HookHandlers>>>;
    /// Forward a hook failure to `HarnessOptions.onReport` whether or not the
    /// invocation ended (TS `Scheduler.#report`). Never fails.
    fn report_failure(&self, error: SessionError);
    /// Commit on the Session line after rereading the task (see
    /// [`TaskRuntime::commit`]).
    fn commit(
        &self,
        change: TaskCommitChange,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>>;
    /// Read a durable memo of this task.
    fn memo(
        &self,
        name: &str,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<JsonValue>>>;
    /// Store `candidate` unless a memo already exists; return the durable
    /// winner.
    fn memo_or_store(
        &self,
        name: &str,
        candidate: JsonValue,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<JsonValue>>;
    /// Committed task record.
    fn get_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<AnyTaskRecord>>>;
    /// Resolve with the task's terminal receipt; rejects when the invocation
    /// ends.
    fn wait_for_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SettledTask>>;
    /// Outcomes of terminal tasks, in order; rejects when one is missing or
    /// not terminal.
    fn outcomes(
        &self,
        ids: Vec<TaskId>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Vec<TaskOutcome>>>;
    /// Invocation-bound handle of an existing conversation; `None` when
    /// absent.
    fn conversation(
        &self,
        id: ConversationId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ConversationHandle>>>>;
    /// Committed entry visible from the task's conversation.
    fn entry(
        &self,
        id: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<EntryRecord>>>;
    /// Committed raw active transcript and model context, optionally cut off
    /// at the visible entry `at`.
    fn context(
        &self,
        conversation_id: ConversationId,
        at: Option<EntryId>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<ContextView>>;
    /// The Harness clock.
    ///
    /// # Errors
    ///
    /// The invocation ended.
    fn now(&self) -> SessionResult<f64>;
    /// Forward a non-fatal failure to `HarnessOptions.onReport`.
    ///
    /// # Errors
    ///
    /// The invocation ended.
    fn report(&self, error: SessionError) -> SessionResult<()>;
    /// Resolve once the Harness clock reaches `until`; rejects when the
    /// invocation or `cx` is cancelled.
    fn sleep(&self, until: f64, cx: &Context) -> BoxFuture<'static, SessionResult<()>>;
}

/// The phantom type parameters of a [`TaskRuntime`].
type Types<I, S, R, H> = PhantomData<fn() -> (I, S, R, H)>;

/// Operations of one task invocation, typed by the task's input,
/// checkpoint, result, and hooks (TS `TaskRuntime<I, S, R, H>`). Every
/// operation rejects after the invocation ends.
pub struct TaskRuntime<I = JsonValue, S = JsonValue, R = JsonValue, H = ()> {
    backend: Arc<dyn TaskRuntimeBackend>,
    types: Types<I, S, R, H>,
}

impl<I, S, R, H> Clone for TaskRuntime<I, S, R, H> {
    fn clone(&self) -> Self {
        Self {
            backend: Arc::clone(&self.backend),
            types: PhantomData,
        }
    }
}

impl<I, S, R, H> std::fmt::Debug for TaskRuntime<I, S, R, H> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("TaskRuntime")
            .field("task_id", &self.backend.task_id())
            .finish_non_exhaustive()
    }
}

impl<I, S, R, H> TaskRuntime<I, S, R, H>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    /// The typed view of `backend`.
    #[must_use]
    pub fn new(backend: Arc<dyn TaskRuntimeBackend>) -> Self {
        Self {
            backend,
            types: PhantomData,
        }
    }

    /// The erased runtime.
    #[must_use]
    pub fn backend(&self) -> &Arc<dyn TaskRuntimeBackend> {
        &self.backend
    }

    /// The invocation's task.
    #[must_use]
    pub fn task_id(&self) -> TaskId<R> {
        retype(self.backend.task_id())
    }

    /// The task's conversation.
    #[must_use]
    pub fn conversation_id(&self) -> ConversationId {
        self.backend.conversation_id()
    }

    /// Aborted when the run is signalled by `abortTask()`, the Harness
    /// closes, or the invocation ends. Work still using it after the
    /// invocation ended, such as a detached wait, is cancelled.
    #[must_use]
    pub fn signal(&self) -> AbortSignal {
        self.backend.signal()
    }

    /// Registry snapshot of the current phase; refreshed at every phase
    /// boundary.
    #[must_use]
    pub fn registry(&self) -> RegistrySnapshot {
        self.backend.registry()
    }

    /// The task's conversation's agent, resolved at most once per phase, at
    /// first use, and fixed for the phase.
    #[must_use]
    pub fn agent(&self, cx: &Context) -> BoxFuture<'static, SessionResult<Arc<Agent>>> {
        self.backend.agent(cx)
    }

    /// `HarnessOptions.settings`, resolved at each access.
    #[must_use]
    pub fn settings(&self) -> Settings {
        self.backend.settings()
    }

    /// pi-ai model access.
    #[must_use]
    pub fn models(&self) -> Models {
        self.backend.models()
    }

    /// Calls `HarnessOptions.env` for the task's conversation; rejects with
    /// its error.
    #[must_use]
    pub fn env(
        &self,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ExecutionEnv>>>> {
        self.backend.env(cx)
    }

    /// Handlers of this task's name from the extensions its conversation
    /// selects, in extension order.
    #[must_use]
    pub fn hooks(&self) -> HookRunner<H> {
        HookRunner {
            backend: Arc::clone(&self.backend),
            hooks: PhantomData,
        }
    }

    /// This runtime as hooks see it.
    #[must_use]
    pub fn hook_api(&self) -> HookApi {
        HookApi::new(Arc::clone(&self.backend))
    }

    /// Commit on the Session line after rereading the task. Rejects when the
    /// task is terminal, the invocation ended, the Harness is closing, or, in
    /// a run invocation, the task carries an abort mark. A returned state
    /// replaces the task's state in the same commit; returning `None` leaves
    /// it unchanged. `tx.create_task()` defaults to the task's conversation.
    pub fn commit<F, Fut>(&self, change: F, cx: &Context) -> BoxFuture<'static, SessionResult<()>>
    where
        F: FnOnce(Tx, RunningTask<I, S, R>) -> Fut + Send + 'static,
        Fut: Future<Output = SessionResult<Option<NextTaskState<S, R>>>> + Send + 'static,
    {
        self.backend.commit(
            Box::new(move |tx, current| {
                async move {
                    let next = change(tx, current.decode()?).await?;
                    next.map(|next| next.encode()).transpose()
                }
                .boxed()
            }),
            cx,
        )
    }

    /// Read a durable memo of this task.
    #[must_use]
    pub fn memo<T: DeserializeOwned + Send + 'static>(
        &self,
        name: &str,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<T>>> {
        let memo = self.backend.memo(name, cx);
        async move { memo.await?.map(|value| Ok(from_json(&value)?)).transpose() }.boxed()
    }

    /// Store `candidate` unless a memo already exists; return the durable
    /// winner.
    pub fn memo_or<T: Serialize + DeserializeOwned + Send + 'static>(
        &self,
        name: &str,
        candidate: &T,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<T>> {
        let candidate = match to_json(candidate) {
            Ok(candidate) => candidate,
            Err(error) => return futures::future::ready(Err(error.into())).boxed(),
        };
        let memo = self.backend.memo_or_store(name, candidate, cx);
        async move { Ok(from_json(&memo.await?)?) }.boxed()
    }

    /// Committed task record.
    #[must_use]
    pub fn get_task<T: DeserializeOwned + Send + 'static>(
        &self,
        id: TaskId<T>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<TaskRecord<JsonValue, JsonValue, T>>>> {
        let task = self.backend.get_task(id.erase(), cx);
        async move { task.await?.map(|record| recode(&record)).transpose() }.boxed()
    }

    /// Resolve with the task's terminal receipt; rejects when the invocation
    /// ends.
    #[must_use]
    pub fn wait_for_task<T: DeserializeOwned + Send + 'static>(
        &self,
        id: TaskId<T>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SettledTask<T>>> {
        let settled = self.backend.wait_for_task(id.erase(), cx);
        async move { settled.await?.decode() }.boxed()
    }

    /// Outcomes of terminal tasks, in order; rejects when one is missing or
    /// not terminal. Used after a wait.
    #[must_use]
    pub fn outcomes<T: DeserializeOwned + Send + 'static>(
        &self,
        ids: &[TaskId<T>],
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Vec<TaskOutcome<T>>>> {
        let outcomes = self
            .backend
            .outcomes(ids.iter().map(|id| id.erase()).collect(), cx);
        async move { outcomes.await?.iter().map(recode).collect() }.boxed()
    }

    /// Invocation-bound handle of an existing conversation, for example one
    /// this task owns; `None` when absent. Its operations and the
    /// submissions it returns reject after the invocation ends; admitted
    /// work stays durable.
    #[must_use]
    pub fn conversation(
        &self,
        id: ConversationId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ConversationHandle>>>> {
        self.backend.conversation(id, cx)
    }

    /// Committed entry visible from the task's conversation.
    #[must_use]
    pub fn entry(
        &self,
        id: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<EntryRecord>>> {
        self.backend.entry(id, cx)
    }

    /// `None` when the entry is absent, not visible, or has another kind.
    #[must_use]
    pub fn typed_entry<D: EntryData + Send + 'static>(
        &self,
        token: &Entry<D>,
        id: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<TypedEntry<D>>>> {
        let token = *token;
        let entry = self.backend.entry(id, cx);
        async move {
            match entry.await? {
                Some(entry) if entry.kind == token.kind() => Ok(token.narrow(entry)?),
                Some(_) | None => Ok(None),
            }
        }
        .boxed()
    }

    /// Committed raw active transcript and model context, optionally cut off
    /// at the visible entry `at`.
    #[must_use]
    pub fn context(
        &self,
        conversation_id: ConversationId,
        cx: &Context,
        at: Option<EntryId>,
    ) -> BoxFuture<'static, SessionResult<ContextView>> {
        self.backend.context(conversation_id, at, cx)
    }

    /// The Harness clock.
    ///
    /// # Errors
    ///
    /// The invocation ended.
    pub fn now(&self) -> SessionResult<f64> {
        self.backend.now()
    }

    /// Forward a non-fatal failure to `HarnessOptions.onReport`.
    ///
    /// # Errors
    ///
    /// The invocation ended.
    pub fn report(&self, error: SessionError) -> SessionResult<()> {
        self.backend.report(error)
    }

    /// Resolve once the Harness clock reaches `until`; rejects when the
    /// invocation or `cx` is cancelled.
    #[must_use]
    pub fn sleep(&self, until: f64, cx: &Context) -> BoxFuture<'static, SessionResult<()>> {
        self.backend.sleep(until, cx)
    }
}

impl<I, S, R, H> DocumentReader for TaskRuntime<I, S, R, H> {
    fn snapshot_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        self.backend.snapshot_definition(definition, resolved, cx)
    }

    fn snapshot_as_of_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        at: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        self.backend
            .snapshot_as_of_definition(definition, resolved, at, cx)
    }
}

impl<I, S, R, H> DocumentObserver for TaskRuntime<I, S, R, H> {
    fn watch_doc_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>> {
        self.backend.watch_doc_definition(definition, resolved, cx)
    }
}

/// Dispatches one hook of a task to every matching registered handler, in
/// registry order of the phase snapshot (TS `HookRunner<H>`).
pub struct HookRunner<H> {
    backend: Arc<dyn TaskRuntimeBackend>,
    hooks: PhantomData<fn() -> H>,
}

impl<H> Clone for HookRunner<H> {
    fn clone(&self) -> Self {
        Self {
            backend: Arc::clone(&self.backend),
            hooks: PhantomData,
        }
    }
}

impl<H: Send + Sync + 'static> HookRunner<H> {
    /// Call `invoke` with each matching handler: `select` picks the handler
    /// (TS `name`) from every registered `H` of the task's name. An ordinary
    /// error from `invoke` is reported and the next handler runs; once the
    /// invocation is signalled, the error propagates. Composition happens
    /// inside `invoke`.
    ///
    /// # Errors
    ///
    /// Failures resolving the agent, and a failure of `invoke` after the
    /// invocation was signalled.
    #[expect(
        clippy::manual_async_fn,
        reason = "the `Send` bound of the returned future is part of the contract"
    )]
    pub fn each<'a, T, Sel, Inv, Fut>(
        &'a self,
        select: Sel,
        mut invoke: Inv,
    ) -> impl Future<Output = SessionResult<()>> + Send + 'a
    where
        T: Send + 'a,
        Sel: Fn(&H) -> Option<T> + Send + 'a,
        Inv: FnMut(T) -> Fut + Send + 'a,
        Fut: Future<Output = SessionResult<()>> + Send + 'a,
    {
        async move {
            for handlers in self.backend.hook_handlers().await? {
                let Some(handler) = handlers.downcast_ref::<H>().and_then(&select) else {
                    continue;
                };
                if let Err(error) = invoke(handler).await {
                    if self.backend.signal().aborted() {
                        return Err(error);
                    }
                    self.backend.report_failure(error);
                }
            }
            Ok(())
        }
    }
}
