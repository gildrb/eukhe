//! Typed and erased task definitions (TS `TaskDefinition`, `Task`,
//! `PhaseHandler`, `defineTask()`, and the harness `AnyTask`).

use std::any::Any;
use std::collections::HashMap;
use std::fmt;
use std::future::Future;
use std::marker::PhantomData;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::de::DeserializeOwned;
use serde::Serialize;

use super::runtime::{RunningTask, TaskRuntime, TaskRuntimeBackend};
use crate::session::{SessionError, SessionResult, TaskDefinitionRef};

/// Bounds of every typed task parameter: input, checkpoint, and result are
/// JSON-serializable values shared across invocations.
pub trait TaskValue: Serialize + DeserializeOwned + Send + Sync + 'static {}

impl<T: Serialize + DeserializeOwned + Send + Sync + 'static> TaskValue for T {}

/// Runs one checkpoint phase (TS `PhaseHandler`). It must commit a changed
/// checkpoint or a terminal outcome through `runtime.commit()`; returning
/// without durable progress faults the task.
pub type PhaseHandler<I, S, R, H> = Arc<
    dyn Fn(
            RunningTask<I, S, R>,
            TaskRuntime<I, S, R, H>,
            Context,
        ) -> BoxFuture<'static, SessionResult<()>>
        + Send
        + Sync,
>;

/// First durable checkpoint for a newly created task.
pub type TaskInitial<I, S> = Arc<dyn Fn(&I) -> SessionResult<S> + Send + Sync>;

/// Converts a record stored by any older supported version:
/// `(input, checkpoint, from_version)`.
pub type TaskMigrate<I, S> =
    Arc<dyn Fn(&JsonValue, &JsonValue, u64) -> SessionResult<Migrated<I, S>> + Send + Sync>;

/// Result of a task migration.
#[derive(Debug, Clone, PartialEq)]
pub struct Migrated<I = JsonValue, S = JsonValue> {
    pub input: I,
    pub checkpoint: S,
}

/// Executable durable state machine definition, registered in the registry
/// by `name` (TS `TaskDefinition<I, S, R, H>`).
///
/// Built with [`TaskDefinition::new`] and [`TaskDefinition::phase`]. The phase
/// map is keyed by the checkpoint's `phase` field; a handler receives the
/// whole typed checkpoint (Rust has no per-phase narrowing). `H` is the hook
/// handler set of this task (TS `hooks?: H`, which is type-only).
pub struct TaskDefinition<I, S, R, H> {
    name: String,
    version: u64,
    initial: TaskInitial<I, S>,
    phases: HashMap<String, PhaseHandler<I, S, R, H>>,
    abort: PhaseHandler<I, S, R, H>,
    migrate: Option<TaskMigrate<I, S>>,
    hooks: PhantomData<fn() -> H>,
}

fn box_handler<I, S, R, H, F, Fut>(handler: F) -> PhaseHandler<I, S, R, H>
where
    F: Fn(RunningTask<I, S, R>, TaskRuntime<I, S, R, H>, Context) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = SessionResult<()>> + Send + 'static,
{
    Arc::new(move |task, runtime, cx| handler(task, runtime, cx).boxed())
}

impl<I, S, R, H> TaskDefinition<I, S, R, H>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    /// A definition without phases. `abort` runs in a fresh invocation after
    /// an abort mark and must commit a terminal outcome.
    pub fn new<Init, Abort, Fut>(
        name: impl Into<String>,
        version: u64,
        initial: Init,
        abort: Abort,
    ) -> Self
    where
        Init: Fn(&I) -> SessionResult<S> + Send + Sync + 'static,
        Abort: Fn(RunningTask<I, S, R>, TaskRuntime<I, S, R, H>, Context) -> Fut
            + Send
            + Sync
            + 'static,
        Fut: Future<Output = SessionResult<()>> + Send + 'static,
    {
        Self {
            name: name.into(),
            version,
            initial: Arc::new(initial),
            phases: HashMap::new(),
            abort: box_handler(abort),
            migrate: None,
            hooks: PhantomData,
        }
    }

    /// Add (or replace) the handler of checkpoints whose `phase` is `phase`.
    #[must_use]
    pub fn phase<F, Fut>(mut self, phase: impl Into<String>, handler: F) -> Self
    where
        F: Fn(RunningTask<I, S, R>, TaskRuntime<I, S, R, H>, Context) -> Fut
            + Send
            + Sync
            + 'static,
        Fut: Future<Output = SessionResult<()>> + Send + 'static,
    {
        self.phases.insert(phase.into(), box_handler(handler));
        self
    }

    /// Convert records stored by older versions; runs at reservation.
    #[must_use]
    pub fn migrate<F>(mut self, migrate: F) -> Self
    where
        F: Fn(&JsonValue, &JsonValue, u64) -> SessionResult<Migrated<I, S>> + Send + Sync + 'static,
    {
        self.migrate = Some(Arc::new(migrate));
        self
    }

    /// Registered task kind persisted in `TaskRecord.kind`.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Definition version persisted with live input and checkpoints.
    #[must_use]
    pub fn version(&self) -> u64 {
        self.version
    }

    /// The first checkpoint of a task created with `input`.
    ///
    /// # Errors
    ///
    /// The definition's own failure.
    pub fn initial(&self, input: &I) -> SessionResult<S> {
        (self.initial)(input)
    }

    /// Whether the definition converts older records.
    #[must_use]
    pub fn has_migrate(&self) -> bool {
        self.migrate.is_some()
    }
}

impl<I, S, R, H> fmt::Debug for TaskDefinition<I, S, R, H> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("TaskDefinition")
            .field("name", &self.name)
            .field("version", &self.version)
            .finish_non_exhaustive()
    }
}

/// Typed executable task definition (TS `Task<I, S, R, H>`). Clones share
/// the definition, so an erased [`AnyTask`] keeps its identity.
pub struct Task<I, S, R, H> {
    definition: Arc<TaskDefinition<I, S, R, H>>,
}

impl<I, S, R, H> Clone for Task<I, S, R, H> {
    fn clone(&self) -> Self {
        Self {
            definition: Arc::clone(&self.definition),
        }
    }
}

impl<I, S, R, H> fmt::Debug for Task<I, S, R, H> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Task")
            .field("definition", &self.definition)
            .finish()
    }
}

/// Define an executable task. Register it in the registry so a Harness can
/// run tasks of its kind.
#[must_use]
pub fn define_task<I, S, R, H>(definition: TaskDefinition<I, S, R, H>) -> Task<I, S, R, H>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    Task {
        definition: Arc::new(definition),
    }
}

impl<I, S, R, H> Task<I, S, R, H>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    /// The typed definition.
    #[must_use]
    pub fn definition(&self) -> &TaskDefinition<I, S, R, H> {
        &self.definition
    }

    /// The erased definition the registry and scheduler use; same identity.
    #[must_use]
    pub fn erase(&self) -> AnyTask {
        AnyTask(Arc::clone(&self.definition) as Arc<dyn ErasedTaskDefinition>)
    }

    /// The definition as `tx.create_task()` takes it.
    #[must_use]
    pub fn as_definition_ref(&self) -> Arc<dyn TaskDefinitionRef> {
        Arc::clone(&self.definition) as Arc<dyn TaskDefinitionRef>
    }
}

impl<I, S, R, H> From<Task<I, S, R, H>> for AnyTask
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    fn from(task: Task<I, S, R, H>) -> Self {
        task.erase()
    }
}

/// Erased executable task definition stored in the registry and run by the
/// scheduler over JSON input, checkpoint, and result (TS
/// `AnyTask.definition`).
///
/// Implemented for every [`TaskDefinition`]; decoding the stored JSON into
/// the typed values happens per call, and a decode failure rejects with
/// [`SessionError::Json`].
pub trait ErasedTaskDefinition: TaskDefinitionRef + Any {
    /// Whether a handler exists for checkpoints of phase `phase`.
    fn has_phase(&self, phase: &str) -> bool;

    /// Run the handler of `task.checkpoint.phase`. A checkpoint whose phase
    /// has no handler rejects with the `TypeError` V8 raises for the TS call
    /// `erased(...).phases[checkpoint.phase](...)`.
    fn run_phase(
        &self,
        task: RunningTask,
        runtime: Arc<dyn TaskRuntimeBackend>,
        cx: Context,
    ) -> BoxFuture<'static, SessionResult<()>>;

    /// Run the abort handler.
    fn run_abort(
        &self,
        task: RunningTask,
        runtime: Arc<dyn TaskRuntimeBackend>,
        cx: Context,
    ) -> BoxFuture<'static, SessionResult<()>>;

    /// TS `definition.migrate !== undefined`.
    fn has_migrate(&self) -> bool;

    /// Convert a stored record of `from_version`; `None` without `migrate`.
    /// The output is already encoded (TS `copyJson`).
    fn migrate(
        &self,
        input: &JsonValue,
        checkpoint: &JsonValue,
        from_version: u64,
    ) -> Option<SessionResult<Migrated>>;
}

impl<I, S, R, H> TaskDefinitionRef for TaskDefinition<I, S, R, H>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> u64 {
        self.version
    }

    fn initial(&self, input: &JsonValue) -> SessionResult<JsonValue> {
        let input: I = from_json(input)?;
        Ok(to_json(&(self.initial)(&input)?)?)
    }
}

fn phase_of(checkpoint: &JsonValue) -> Option<&str> {
    checkpoint.get("phase").and_then(JsonValue::as_str)
}

impl<I, S, R, H> TaskDefinition<I, S, R, H>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    fn run(
        handler: Option<PhaseHandler<I, S, R, H>>,
        task: RunningTask,
        runtime: Arc<dyn TaskRuntimeBackend>,
        cx: Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        let Some(handler) = handler else {
            return futures::future::ready(Err(SessionError::type_error(
                "erased(...).phases[checkpoint.phase] is not a function",
            )))
            .boxed();
        };
        let task = match task.decode::<I, S, R>() {
            Ok(task) => task,
            Err(error) => return futures::future::ready(Err(error)).boxed(),
        };
        handler(task, TaskRuntime::new(runtime), cx)
    }
}

impl<I, S, R, H> ErasedTaskDefinition for TaskDefinition<I, S, R, H>
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    fn has_phase(&self, phase: &str) -> bool {
        self.phases.contains_key(phase)
    }

    fn run_phase(
        &self,
        task: RunningTask,
        runtime: Arc<dyn TaskRuntimeBackend>,
        cx: Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        let handler = phase_of(&task.checkpoint)
            .and_then(|phase| self.phases.get(phase))
            .cloned();
        Self::run(handler, task, runtime, cx)
    }

    fn run_abort(
        &self,
        task: RunningTask,
        runtime: Arc<dyn TaskRuntimeBackend>,
        cx: Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        Self::run(Some(Arc::clone(&self.abort)), task, runtime, cx)
    }

    fn has_migrate(&self) -> bool {
        self.migrate.is_some()
    }

    fn migrate(
        &self,
        input: &JsonValue,
        checkpoint: &JsonValue,
        from_version: u64,
    ) -> Option<SessionResult<Migrated>> {
        let migrate = self.migrate.as_ref()?;
        Some(
            migrate(input, checkpoint, from_version).and_then(|migrated| {
                Ok(Migrated {
                    input: to_json(&migrated.input)?,
                    checkpoint: to_json(&migrated.checkpoint)?,
                })
            }),
        )
    }
}

/// Erased executable task definition stored in the registry (TS `AnyTask`).
/// Equality is identity: two erasures of one [`Task`] are equal.
#[derive(Clone)]
pub struct AnyTask(Arc<dyn ErasedTaskDefinition>);

impl AnyTask {
    /// Wrap an erased definition.
    #[must_use]
    pub fn new(definition: Arc<dyn ErasedTaskDefinition>) -> Self {
        Self(definition)
    }

    /// Registered task kind.
    #[must_use]
    pub fn name(&self) -> &str {
        self.0.name()
    }

    /// Definition version.
    #[must_use]
    pub fn version(&self) -> u64 {
        self.0.version()
    }

    /// The erased definition.
    #[must_use]
    pub fn definition(&self) -> &Arc<dyn ErasedTaskDefinition> {
        &self.0
    }

    /// The definition as `tx.create_task()` takes it.
    #[must_use]
    pub fn as_definition_ref(&self) -> Arc<dyn TaskDefinitionRef> {
        Arc::clone(&self.0) as Arc<dyn TaskDefinitionRef>
    }

    /// Whether both are the same definition object.
    #[must_use]
    pub fn ptr_eq(a: &AnyTask, b: &AnyTask) -> bool {
        std::ptr::addr_eq(Arc::as_ptr(&a.0), Arc::as_ptr(&b.0))
    }

    /// The typed task when the definition has these parameters.
    #[must_use]
    pub fn downcast<I, S, R, H>(&self) -> Option<Task<I, S, R, H>>
    where
        I: TaskValue,
        S: TaskValue,
        R: TaskValue,
        H: Send + Sync + 'static,
    {
        let any: Arc<dyn Any + Send + Sync> = Arc::clone(&self.0) as Arc<dyn Any + Send + Sync>;
        any.downcast::<TaskDefinition<I, S, R, H>>()
            .ok()
            .map(|definition| Task { definition })
    }
}

impl PartialEq for AnyTask {
    fn eq(&self, other: &Self) -> bool {
        Self::ptr_eq(self, other)
    }
}

impl Eq for AnyTask {}

impl fmt::Debug for AnyTask {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AnyTask")
            .field("name", &self.name())
            .field("version", &self.version())
            .finish_non_exhaustive()
    }
}
