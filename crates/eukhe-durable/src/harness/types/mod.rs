//! Harness types (`harness/types.ts`).
//!
//! TS interfaces that other parts of the harness implement (`Submission`,
//! `ConversationHandle`, `ToolExecutionApi`, `RegistryReader`, the settings
//! source) are object-safe traits used as `Arc<dyn Trait>`. Thrown values
//! are [`SessionError`](crate::session::SessionError)s.

mod agent;
mod conversation;
mod data;
mod extension;
mod hooks;
mod registry;
mod settings;
mod tools;

pub use agent::{
    Agent, AgentChange, AgentState, EnvTarget, ExtensionSelection, ExtensionsChange, FieldChange,
    ModelRef, ToolFilter, ToolsChange,
};
pub use conversation::{
    CompactionResult, ContextView, ConversationAbortOptions, ConversationCreateOptions,
    ConversationHandle, ConversationInit, HarnessInspection, InputSubmissionDraft, SchedulingState,
    SettledSubmissionRecord, Submission, SubmissionAbort, SubmissionDraft, TaskBlockedReason,
    TaskInspection, TaskInspectionState, UserInput, WhenBusy, WriteSubmissionDraft,
};
pub use data::{CompactionReason, ToolDiagnostic, ToolDiagnosticSeverity};
pub use extension::{
    Extension, HookHandlers, HookRegistration, PromptInput, PromptSection, SectionRender,
    SectionWrapper, ToolWrapper, Wrap,
};
pub use hooks::{
    AfterResponseHook, AfterToolHook, AfterToolsHook, BeforeCompactHook, BeforeRequestHook,
    BeforeToolDecision, BeforeToolHook, CompactionDecision, CompactionHooks, CompactionRequest,
    GenerationHooks, HookApi, HookDone, HookFuture, HookResult, OnYieldHook, RequestMessages,
    ToolHooks, YieldContinuation,
};
pub(crate) use registry::BuiltinTasks;
pub use registry::{InstalledSection, InstalledTool, RegistryReader, RegistrySnapshot};
pub use settings::{
    Clock, CompactionPolicy, ConversationCreated, ConversationRetryPolicy,
    ConversationStreamOptions, EnvFactory, HarnessOptions, HarnessSettings, HarnessSettingsSource,
    LiveSettings, PartialCompactionPolicy, PartialProgressPolicy, PartialRetryPolicy,
    ProgressPolicy, QueueMode, ReportFn, Settings, ToolExecutionMode,
};
pub use tools::{
    InvocationTaskOptions, OutputRetain, PrepareArguments, ToolCommitChange, ToolControl,
    ToolExecute, ToolExecutionApi, ToolExecutionApiExt, ToolExecutionResult, ToolOutputChunk,
    ToolOutputLimits, ToolRegistration, ToolReplay,
};
