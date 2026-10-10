//! Hooks of the built-in tasks and what a hook may use (TS `HookApi`,
//! `HookResult`, `GenerationHooks`, `ToolHooks`, `CompactionHooks`).
//!
//! A hook set is a struct of optional handlers (TS `Partial<HooksOf<K>>`);
//! `hook(task, handlers)` registers one for a task's name.

use std::fmt;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json};
use eukhe_types::pi_ai::{AssistantMessage, JsonObject as PiJsonObject, Message, ToolCall};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use super::conversation::UserInput;
use super::data::CompactionReason;
use super::tools::ToolExecutionResult;
use crate::documents::{AnyDocDefinition, ResolvedAddress};
use crate::session::SessionResult;
use crate::tasks::TaskRuntimeBackend;
use crate::types::{ConversationId, DocumentReader, EntryId, EntryRecord, JsonObject, TaskId};

/// A hook's decision: `None` keeps the default (TS `T | undefined`); an error
/// is the hook's throw.
pub type HookResult<T> = SessionResult<Option<T>>;

/// Future of a deciding hook.
pub type HookFuture<T> = BoxFuture<'static, HookResult<T>>;

/// Future of an observing hook.
pub type HookDone = BoxFuture<'static, SessionResult<()>>;

/// What a hook may use: committed reads and the asking task's memos, which
/// hooks and the task share (TS `HookApi`; the asking task's runtime).
#[derive(Clone)]
pub struct HookApi {
    backend: Arc<dyn TaskRuntimeBackend>,
}

impl HookApi {
    /// The hook view of a task invocation.
    #[must_use]
    pub fn new(backend: Arc<dyn TaskRuntimeBackend>) -> Self {
        Self { backend }
    }

    /// The asking task.
    #[must_use]
    pub fn task_id(&self) -> TaskId {
        self.backend.task_id()
    }

    /// The asking task's conversation.
    #[must_use]
    pub fn conversation_id(&self) -> ConversationId {
        self.backend.conversation_id()
    }

    /// Read a durable memo of the asking task.
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
    #[must_use]
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
}

impl fmt::Debug for HookApi {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("HookApi")
            .field("task_id", &self.task_id())
            .field("conversation_id", &self.conversation_id())
            .finish()
    }
}

impl DocumentReader for HookApi {
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

/// The request of `before_request`, and its replacement.
#[derive(Debug, Clone, PartialEq)]
pub struct RequestMessages {
    pub messages: Vec<Message>,
}

/// `on_yield`'s decision: append a user message and continue the run.
#[derive(Debug, Clone, PartialEq)]
pub struct YieldContinuation {
    pub r#continue: UserInput,
}

/// Before every request attempt, including recovery.
pub type BeforeRequestHook =
    Arc<dyn Fn(&RequestMessages, &HookApi, &Context) -> HookFuture<RequestMessages> + Send + Sync>;
/// Every terminal provider message, before classification.
pub type AfterResponseHook =
    Arc<dyn Fn(&AssistantMessage, &HookApi, &Context) -> HookDone + Send + Sync>;
/// A final answer.
pub type OnYieldHook = Arc<
    dyn Fn(&AssistantMessage, &HookApi, &Context) -> HookFuture<YieldContinuation> + Send + Sync,
>;
/// After every tool of the round is terminal: `(assistant, results)`.
pub type AfterToolsHook =
    Arc<dyn Fn(EntryId, &[EntryId], &HookApi, &Context) -> HookDone + Send + Sync>;

/// Hooks of the built-in generation task.
#[derive(Clone, Default)]
pub struct GenerationHooks {
    /// Before every request attempt, including recovery; the result is used
    /// for that request only.
    pub before_request: Option<BeforeRequestHook>,
    /// Every terminal provider message, before classification.
    pub after_response: Option<AfterResponseHook>,
    /// A final answer; the first `continue` appends a user message and
    /// continues the run.
    pub on_yield: Option<OnYieldHook>,
    /// After every tool of the round is terminal; `results` are the round's
    /// result entries in call order.
    pub after_tools: Option<AfterToolsHook>,
}

impl fmt::Debug for GenerationHooks {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("GenerationHooks")
            .field("before_request", &self.before_request.is_some())
            .field("after_response", &self.after_response.is_some())
            .field("on_yield", &self.on_yield.is_some())
            .field("after_tools", &self.after_tools.is_some())
            .finish()
    }
}

/// `before_tool`'s decision: the first `block` wins, otherwise `arguments`
/// replace the call's arguments.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct BeforeToolDecision {
    pub arguments: Option<PiJsonObject>,
    pub block: Option<String>,
}

/// The call that made a nested call: its tool task and its call ID.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ToolCallParent {
    pub task_id: TaskId,
    pub call_id: String,
}

/// A call as tool hooks see it; `parent` is set for a nested call, one a
/// running tool made through `execute_tool()`. Derefs to the [`ToolCall`].
#[derive(Debug, Clone, PartialEq)]
pub struct ToolHookCall {
    pub call: ToolCall,
    pub parent: Option<ToolCallParent>,
}

impl std::ops::Deref for ToolHookCall {
    type Target = ToolCall;

    fn deref(&self) -> &ToolCall {
        &self.call
    }
}

/// Before intent. An error blocks.
pub type BeforeToolHook =
    Arc<dyn Fn(&ToolHookCall, &HookApi, &Context) -> HookFuture<BeforeToolDecision> + Send + Sync>;
/// After execution, before the result is committed; replaces the result.
pub type AfterToolHook = Arc<
    dyn Fn(
            &ToolHookCall,
            &ToolExecutionResult,
            &HookApi,
            &Context,
        ) -> HookFuture<ToolExecutionResult>
        + Send
        + Sync,
>;

/// Hooks of the built-in tool task, for model-issued and nested calls.
#[derive(Clone, Default)]
pub struct ToolHooks {
    /// Before intent; the first `block` wins, otherwise `arguments` replace
    /// the call's arguments. An error blocks.
    pub before_tool: Option<BeforeToolHook>,
    /// After execution, before the result is committed; replaces the result.
    pub after_tool: Option<AfterToolHook>,
}

impl fmt::Debug for ToolHooks {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ToolHooks")
            .field("before_tool", &self.before_tool.is_some())
            .field("after_tool", &self.after_tool.is_some())
            .finish()
    }
}

/// What `before_compact` sees: `entries` are the active entries the summary
/// replaces, the head marker first, and `messages` their model context, the
/// summarizer's source; `first_kept` is the first entry kept verbatim.
#[derive(Debug, Clone, PartialEq)]
pub struct CompactionRequest {
    pub reason: CompactionReason,
    pub entries: Vec<EntryRecord>,
    pub messages: Vec<Message>,
    pub first_kept: EntryId,
    pub instructions: Option<String>,
}

/// `before_compact`'s decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompactionDecision {
    /// `{ decline: true }`.
    Decline,
    /// `{ summary }`.
    Summary(String),
    /// `{ summary }` plus the `pi.compaction` data fields of the harness
    /// digest snapshot the summary leads with (eukhe addition; the old
    /// engine's compaction record carried the same fields).
    SummaryWithData(String, CompactionSnapshot),
}

/// The harness digest snapshot of a [`CompactionDecision::SummaryWithData`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactionSnapshot {
    /// The digest the summary leads with.
    pub harness_digest: String,
    /// The state fingerprint that produced it.
    pub harness_state_fingerprint: String,
}

/// After range selection, before summarizing; the first decision wins.
pub type BeforeCompactHook = Arc<
    dyn Fn(&CompactionRequest, &HookApi, &Context) -> HookFuture<CompactionDecision> + Send + Sync,
>;

/// Hooks of the built-in compaction task.
#[derive(Clone, Default)]
pub struct CompactionHooks {
    /// After range selection, before summarizing; the first decision wins.
    pub before_compact: Option<BeforeCompactHook>,
}

impl fmt::Debug for CompactionHooks {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("CompactionHooks")
            .field("before_compact", &self.before_compact.is_some())
            .finish()
    }
}
