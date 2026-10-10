//! Executable tools and the operations of one tool invocation (TS
//! `ToolRegistration`, `ToolExecutionApi`, `ToolExecutionResult`,
//! `NestedToolExecutionResult`, `ToolControl`).

use std::any::Any;
use std::fmt;
use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::json::{to_json, JsonValue};
use eukhe_pi_ai::models::Models;
use eukhe_types::pi_ai::{
    JsonObject as PiJsonObject, JsonValue as PiJsonValue, Tool, ToolConstrainedSampling,
    ToolSchema, Usage, UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::{Deserialize, Serialize};

use super::agent::Agent;
use super::conversation::ConversationHandle;
use super::data::ToolDiagnostic;
use super::registry::RegistrySnapshot;
use super::settings::ToolExecutionMode;
use crate::env::{ExecutionEnv, ShellOutputSkip, ShellOutputWindow};
use crate::session::{SessionError, SessionResult, Tx};
use crate::tasks::{AnyTask, SettledTask, Task, TaskValue};
use crate::types::{
    AnyTaskRecord, ConversationId, DocumentObserver, DocumentReader, TaskId, TaskOwnership,
};

/// Post-tools controls requested by a tool result.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ToolControl {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub add_tools: Option<Vec<String>>,
    /// TS `terminate?: true`: `false` is absent.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub terminate: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub handoff: Option<String>,
}

/// What a tool returns, on three channels: `output` for the model,
/// `structured_output` for programs that call the tool (`execute_tool()`
/// callers, code mode scripts), and `details` for UIs.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ToolExecutionResult {
    /// For the model. Omitted: the retained `output()` text.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output: Option<Vec<UserContentBlock>>,
    /// For programs. Required unless `is_error` when the tool declares
    /// `structured_output_schema`, and validated against it; not allowed
    /// without one, where programs get the output itself
    /// ([`NestedToolExecutionResult::structured_output`]).
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "crate::types::json_serde::present"
    )]
    pub structured_output: Option<JsonValue>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub is_error: Option<bool>,
    /// Omitted: the last `details()` value becomes the details.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub details: Option<JsonValue>,
    /// Added after those recorded through `api.diagnostic()`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diagnostics: Option<Vec<ToolDiagnostic>>,
    /// Spend of the execution itself, such as a model call; stored on the
    /// result and in `pi.usage.tools`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub usage: Option<Usage>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub control: Option<ToolControl>,
}

/// Result of a nested call, as `execute_tool()` returns it. Programs read
/// `structured_output`; the output for the model is not kept, and `control`
/// does not apply.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NestedToolExecutionResult {
    /// The nested call's tool task.
    pub task_id: TaskId,
    /// The value for programs. A tool with `structured_output_schema`: its
    /// validated `structured_output`, absent on an error result that has
    /// none. A tool without: its bounded output, success or error, as a
    /// string for one text item, an `ImageContent` for one image, `""` for
    /// none, and the content list otherwise. Absent on an error result the
    /// Harness wrote itself (unavailable, invalid, blocked, interrupted,
    /// aborted); `diagnostics` say what went wrong.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "crate::types::json_serde::present"
    )]
    pub structured_output: Option<JsonValue>,
    pub is_error: bool,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "crate::types::json_serde::present"
    )]
    pub details: Option<JsonValue>,
    pub diagnostics: Vec<ToolDiagnostic>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub usage: Option<Usage>,
    /// Execution time of the attempt that produced the result; absent when
    /// it never executed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub duration_ms: Option<u64>,
}

/// Who may call a tool (TS `"model" | "tools"`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ToolCaller {
    /// `"model"`: the model, in a tool round.
    Model,
    /// `"tools"`: other tools, through `execute_tool()`.
    Tools,
}

/// The output retained so far, as the model will see it when the result
/// omits `output`, and whether earlier output was dropped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RetainedOutput {
    pub text: String,
    pub truncated: bool,
}

/// Options of [`ToolExecutionApi::execute_tool`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExecuteToolOptions {
    /// The nested call's key within this call; default its position.
    pub key: Option<String>,
    /// `Some(false)`: commit no running output, details, or diagnostics to
    /// the nested call's slot, only its status.
    pub progress: Option<bool>,
}

/// Whether an interrupted execution may rerun on recovery.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ToolReplay {
    /// `"safe"`.
    Safe,
    /// `"unsafe"` (the default).
    Unsafe,
}

/// Which end of a tool's output its limits keep.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum OutputRetain {
    /// `"head"`.
    Head,
    /// `"tail"`.
    Tail,
}

/// Limits of a tool's retained output.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ToolOutputLimits {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_bytes: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_lines: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub retain: Option<OutputRetain>,
}

/// One chunk of running tool output (TS `string | Uint8Array`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ToolOutputChunk<'a> {
    Text(&'a str),
    Bytes(&'a [u8]),
}

/// Creation options of a task created by a tool invocation (TS
/// `Omit<TaskOptions, "conversationId">`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvocationTaskOptions {
    pub ownership: TaskOwnership,
    pub background: Option<bool>,
    /// Default for a task-owned child of a tool that is not replay-safe:
    /// `true` (see [`ToolExecutionApi::create_task_erased`]).
    pub abandon_on_restart: Option<bool>,
}

/// An erased `api.commit()` change.
pub type ToolCommitChange = Box<dyn FnOnce(Tx) -> BoxFuture<'static, SessionResult<()>> + Send>;

/// Operations available to one tool invocation (TS `ToolExecutionApi`).
///
/// The tool task implements it; a wrapper implements it by delegating to the
/// inner API and replacing what it changes. Every operation rejects after
/// the invocation ends. The TS `TDetails` parameter is erased to JSON.
pub trait ToolExecutionApi: DocumentReader + DocumentObserver {
    fn task_id(&self) -> TaskId;
    fn conversation_id(&self) -> ConversationId;
    fn call_id(&self) -> &str;
    /// The tool task's phase snapshot.
    fn registry(&self) -> RegistrySnapshot;
    /// The calling conversation's agent, as the tool task's phase resolved
    /// it.
    fn agent(&self, cx: &Context) -> BoxFuture<'static, SessionResult<Arc<Agent>>>;
    /// `HarnessOptions.models`: the catalog, credentials, and request
    /// transforms generation uses.
    fn models(&self) -> Models;
    /// Built by `HarnessOptions.env` for this call; `None` without an
    /// environment.
    fn env(&self) -> Option<Arc<dyn ExecutionEnv>>;
    /// Append running output; it becomes the result's `output` when the
    /// result omits it. `skipped` counts output omitted before the chunk, as
    /// reported by an environment given `output_window`.
    ///
    /// # Errors
    ///
    /// The invocation ended.
    fn output(
        &self,
        chunk: ToolOutputChunk<'_>,
        skipped: Option<ShellOutputSkip>,
    ) -> SessionResult<()>;
    /// The tail this call's output keeps and the pace of its progress
    /// commits; `None` when the tool keeps the head of its output, which
    /// cannot accept skips. A wrapper that replaces `output` and transforms
    /// text must also answer `None`, so skipped text cannot bypass its
    /// transform.
    fn output_window(&self) -> Option<ShellOutputWindow>;
    /// The output retained so far, as the model will see it when the result
    /// omits `output`, and whether earlier output was dropped; for a tool
    /// that also returns that text in its `structured_output`.
    ///
    /// # Errors
    ///
    /// The invocation ended.
    fn retained_output(&self) -> SessionResult<RetainedOutput>;
    /// Record a model-visible remark about this call.
    ///
    /// # Errors
    ///
    /// The invocation ended.
    fn diagnostic(&self, diagnostic: ToolDiagnostic) -> SessionResult<()>;
    /// Replace running details; the last value becomes the result details
    /// when the result omits `details`.
    fn details(&self, value: JsonValue, cx: &Context) -> BoxFuture<'static, SessionResult<()>>;
    /// Erased `commit()`; see [`ToolExecutionApiExt::commit`].
    fn commit_erased(
        &self,
        change: ToolCommitChange,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>>;
    /// Read a durable memo of the tool task.
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
    /// Erased `createTask()`; see [`ToolExecutionApiExt::create_task`]. A
    /// task-owned child of a tool that is not replay-safe defaults to
    /// `abandon_on_restart`: the tool never resumes after a restart, so
    /// nothing awaits the child then.
    fn create_task_erased(
        &self,
        task: AnyTask,
        input: JsonValue,
        options: InvocationTaskOptions,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<TaskId>>;
    fn get_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<AnyTaskRecord>>>;
    fn wait_for_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SettledTask>>;
    /// Invocation-bound handle of an existing conversation, such as one this
    /// tool created in `commit()`.
    fn conversation(
        &self,
        id: ConversationId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ConversationHandle>>>>;
    /// Run tool `name` as a nested call of this one and wait for its result.
    /// The nested call is its own `pi.tool` task, owned by this call: it
    /// resolves the tool among the conversation's callable tools,
    /// validates, runs the `ToolTask` hooks (which see `call.parent`),
    /// applies output limits and the tool's replay policy, and reports
    /// progress in `pi.live.nestedTools`. Its result returns here instead
    /// of entering the transcript. A call that is blocked, invalid, throws,
    /// is interrupted, or is aborted returns an `is_error` result.
    ///
    /// The nested call's key names it within this call; its call ID is
    /// `<callId>/<key>`. By default the key is the call's position among
    /// this invocation's nested calls, `1`, `2`, ... An explicit `key` must
    /// be non-empty, without `/`, not `__proto__`, and not a positive
    /// integer. A rerun of a replay-safe tool that makes a call with a used
    /// key gets that nested call back, finished or still running. Reusing a
    /// key with another tool or other arguments rejects. A tool that is not
    /// replay-safe never reruns: after a restart, its unfinished nested
    /// calls are abandoned (`TaskOptions.abandon_on_restart`).
    ///
    /// `progress: Some(false)` commits no running output, details, or
    /// diagnostics to the nested call's slot, only its status.
    ///
    /// Nested calls run as soon as they are made. Cancelling `cx` stops
    /// only the wait; the nested call runs on. When this call settles,
    /// nested calls it left running are aborted first. Rejects once
    /// `execute()` has returned, when this call is aborted, or when the
    /// Harness closes.
    fn execute_tool(
        &self,
        name: &str,
        args: PiJsonObject,
        cx: &Context,
        options: ExecuteToolOptions,
    ) -> BoxFuture<'static, SessionResult<NestedToolExecutionResult>>;
}

/// Typed operations of every [`ToolExecutionApi`].
pub trait ToolExecutionApiExt: ToolExecutionApi {
    /// Session commit bound to the calling conversation; resolves with the
    /// callback's value.
    fn commit<T, F, Fut>(&self, change: F, cx: &Context) -> BoxFuture<'static, SessionResult<T>>
    where
        T: Send + 'static,
        F: FnOnce(Tx) -> Fut + Send + 'static,
        Fut: Future<Output = SessionResult<T>> + Send + 'static,
    {
        let slot = Arc::new(Mutex::new(None));
        let output = Arc::clone(&slot);
        let committed = self.commit_erased(
            Box::new(move |tx| {
                async move {
                    let value = change(tx).await?;
                    *output.lock().unwrap_or_else(PoisonError::into_inner) = Some(value);
                    Ok(())
                }
                .boxed()
            }),
            cx,
        );
        async move {
            committed.await?;
            let value = slot.lock().unwrap_or_else(PoisonError::into_inner).take();
            value.ok_or_else(|| SessionError::error("Tool commit settled without a value"))
        }
        .boxed()
    }

    /// Create a task of `task` owned as `options` says, in the calling
    /// conversation.
    fn create_task<I, S, R, H>(
        &self,
        task: &Task<I, S, R, H>,
        input: &I,
        options: InvocationTaskOptions,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<TaskId<R>>>
    where
        I: TaskValue,
        S: TaskValue,
        R: TaskValue,
        H: Send + Sync + 'static,
    {
        let input = match to_json(input) {
            Ok(input) => input,
            Err(error) => return futures::future::ready(Err(error.into())).boxed(),
        };
        let created = self.create_task_erased(task.erase(), input, options, cx);
        async move { Ok(TaskId::from_number(created.await?.get())) }.boxed()
    }
}

impl<T: ToolExecutionApi + ?Sized> ToolExecutionApiExt for T {}

/// A tool's execution: `(args, api, cx)`. `args` were validated against the
/// tool's `parameters` before the call.
pub type ToolExecute = Arc<
    dyn Fn(
            PiJsonValue,
            Arc<dyn ToolExecutionApi>,
            Context,
        ) -> BoxFuture<'static, SessionResult<ToolExecutionResult>>
        + Send
        + Sync,
>;

/// Repairs arguments models commonly get wrong before validation. Must be
/// pure: it runs again when a call is retried before its intent is
/// recorded. Its result is still validated against `parameters`.
pub type PrepareArguments = Arc<dyn Fn(PiJsonValue) -> SessionResult<PiJsonValue> + Send + Sync>;

/// Executable tool registered in a registry (TS `ToolRegistration`). Only
/// the pi-ai `Tool` fields enter the transcript.
///
/// TS lets an application extend the type (`Tool extends
/// ToolRegistration`); Rust carries such application data in
/// [`extra`](Self::extra).
#[derive(Clone)]
pub struct ToolRegistration {
    pub name: String,
    pub description: String,
    /// JSON Schema of the arguments (`TypeBox` output, with its markers).
    pub parameters: ToolSchema,
    pub constrained_sampling: Option<ToolConstrainedSampling>,
    /// Whether an interrupted execution may rerun on recovery. Default
    /// `Unsafe`.
    pub replay: Option<ToolReplay>,
    /// Default: the settings' `tool_execution`. One sequential call makes its
    /// whole round sequential.
    pub execution_mode: Option<ToolExecutionMode>,
    pub prepare_arguments: Option<PrepareArguments>,
    /// Schema of `structured_output`, which programs that call the tool
    /// receive. `None`: they receive the result's bounded output, success or
    /// error, as [`NestedToolExecutionResult::structured_output`] describes.
    pub structured_output_schema: Option<ToolSchema>,
    /// Who may call the tool: the model, other tools through
    /// `execute_tool()`, or both (`None`, the default).
    pub callers: Option<Vec<ToolCaller>>,
    pub output_limits: Option<ToolOutputLimits>,
    pub execute: ToolExecute,
    /// Application data of an extended tool type.
    pub extra: Option<Arc<dyn Any + Send + Sync>>,
}

impl ToolRegistration {
    /// A tool with only the required fields.
    pub fn new<F, Fut>(
        name: impl Into<String>,
        description: impl Into<String>,
        parameters: impl Into<ToolSchema>,
        execute: F,
    ) -> Self
    where
        F: Fn(PiJsonValue, Arc<dyn ToolExecutionApi>, Context) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = SessionResult<ToolExecutionResult>> + Send + 'static,
    {
        Self {
            name: name.into(),
            description: description.into(),
            parameters: parameters.into(),
            constrained_sampling: None,
            replay: None,
            execution_mode: None,
            prepare_arguments: None,
            structured_output_schema: None,
            callers: None,
            output_limits: None,
            execute: Arc::new(move |args, api, cx| execute(args, api, cx).boxed()),
            extra: None,
        }
    }

    /// The pi-ai tool declaration that enters the transcript.
    #[must_use]
    pub fn tool(&self) -> Tool {
        Tool {
            name: self.name.clone(),
            description: self.description.clone(),
            parameters: self.parameters.clone(),
            constrained_sampling: self.constrained_sampling.clone(),
        }
    }

    /// The application data, when it is a `T`.
    #[must_use]
    pub fn extra<T: Any>(&self) -> Option<&T> {
        self.extra.as_deref().and_then(|extra| extra.downcast_ref())
    }

    /// This tool with application data `value`.
    #[must_use]
    pub fn with_extra<T: Any + Send + Sync>(mut self, value: T) -> Self {
        self.extra = Some(Arc::new(value));
        self
    }
}

impl fmt::Debug for ToolRegistration {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ToolRegistration")
            .field("name", &self.name)
            .field("description", &self.description)
            .field("parameters", &self.parameters)
            .field("constrained_sampling", &self.constrained_sampling)
            .field("replay", &self.replay)
            .field("execution_mode", &self.execution_mode)
            .field("prepare_arguments", &self.prepare_arguments.is_some())
            .field("structured_output_schema", &self.structured_output_schema)
            .field("callers", &self.callers)
            .field("output_limits", &self.output_limits)
            .finish_non_exhaustive()
    }
}
