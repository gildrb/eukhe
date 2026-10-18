//! The session event stream: one typed [`SessionEvent`] per change of an
//! attached session (`session_event` frames). The worker projects its durable
//! agent events onto this vocabulary once; the TUI, the Signal gateway, and
//! the ACP adapter all fold the same typed events, and the RPC mode writes
//! their serde form (the pi event shapes) to stdout.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::{AgentRelayEvent, MemoryUpdate, SessionActionSnapshot};
use crate::ai::{ServiceTier, UserContentBlock};
use crate::goal::GoalState;
use crate::output::OmittedOutput;
use crate::pi_ai::PromptProgress;
use crate::session::AgentMessage;

/// One session event, tagged by `type`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum SessionEvent {
    /// A run started.
    AgentStart,
    /// A run ended; `messages` are the messages it added, prompt included.
    AgentEnd {
        messages: Vec<AgentMessage>,
    },
    /// A turn (one model request and its tool calls) started.
    TurnStart,
    /// A turn ended: its terminal answer, else the error that failed it.
    TurnEnd {
        #[serde(flatten)]
        answer: Option<TurnAnswer>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        error: Option<String>,
    },
    /// The model request's server reported how far it got through the
    /// prompt (llama.cpp `llama-server`), before the first token.
    PromptProgress {
        progress: PromptProgress,
    },
    /// A message entered the transcript. A streamed assistant message
    /// carries the `start` update.
    MessageStart {
        message: AgentMessage,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        assistant_message_event: Option<StreamUpdate>,
    },
    /// The streaming assistant message changed: the whole partial plus the
    /// change.
    MessageUpdate {
        message: AgentMessage,
        assistant_message_event: StreamUpdate,
    },
    /// A message settled.
    MessageEnd {
        message: AgentMessage,
    },
    ToolExecutionStart {
        tool_call_id: String,
        tool_name: String,
        args: Value,
    },
    /// A running tool's output so far.
    ToolExecutionUpdate {
        tool_call_id: String,
        tool_name: String,
        args: Value,
        partial_result: ToolOutput,
    },
    ToolExecutionEnd {
        tool_call_id: String,
        tool_name: String,
        result: ToolOutput,
        is_error: bool,
    },
    /// A failed model request is retried after `delay_ms`. `max_attempts`
    /// is absent when the emitter does not know the retry policy.
    AutoRetryStart {
        attempt: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        max_attempts: Option<u64>,
        delay_ms: u64,
        error_message: String,
        #[serde(flatten)]
        failover: Option<Failover>,
    },
    /// A retry episode ended: recovered, or failed with `final_error`.
    AutoRetryEnd {
        success: bool,
        attempt: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        final_error: Option<String>,
        /// The primary model ("provider/model-id") a successful failover
        /// restored.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        restored_model: Option<String>,
    },
    CompactionStart {
        reason: CompactionReason,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        custom_instructions: Option<String>,
    },
    /// One streamed chunk of the summary a compaction is writing.
    CompactionSummaryDelta {
        delta: String,
    },
    /// A compaction settled: its result, or why it did not compact.
    CompactionEnd {
        reason: CompactionReason,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        result: Option<CompactionResult>,
        aborted: bool,
        /// The failed request runs again on the compacted context.
        will_retry: bool,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        error_message: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        error_severity: Option<ErrorSeverity>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        custom_instructions: Option<String>,
    },
    /// The session display name changed (`None` cleared it).
    SessionInfoChanged {
        name: Option<String>,
    },
    /// The session's effective service tier changed.
    ServiceTierChanged {
        service_tier: ServiceTier,
    },
    /// The queue projection changed.
    SessionActionUpdate {
        actions: SessionActionSnapshot,
    },
    GoalUpdate {
        goal: GoalState,
    },
    /// This window's chat turn waits for another window's turn (`true`),
    /// or that wait ended (`false`).
    ChatTurnWait {
        waiting: bool,
    },
    /// The chat memory summarized lines or merged its view.
    MemoryUpdate {
        update: MemoryUpdate,
    },
    /// Two non-root agents of this session's family exchanged a message.
    AgentRelay(AgentRelayEvent),
    /// A user shell command (`!command`) started.
    BashStart {
        command: String,
        exclude_from_context: bool,
        #[serde(flatten)]
        run: BashRun,
    },
    BashOutput {
        chunk: String,
    },
    /// A user shell command ended: its kept output, what the bound left
    /// out, and where the whole output is.
    BashEnd {
        exit_code: Option<i64>,
        cancelled: bool,
        output: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        omitted: Option<OmittedOutput>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        artifact: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        error_message: Option<String>,
        #[serde(flatten)]
        run: BashRun,
    },
    /// A refinement applied; `result` is its `RefinementResult`.
    RefineComplete {
        result: Value,
    },
    RefineFailed {
        error: String,
    },
    /// The Python kernel sent an agent message after its cell settled.
    IpythonSentAgentMessage {
        tool_call_id: String,
        message: Value,
    },
}

impl SessionEvent {
    /// The message a `message_*` event carries.
    #[must_use]
    pub fn message(&self) -> Option<&AgentMessage> {
        match self {
            Self::MessageStart { message, .. }
            | Self::MessageUpdate { message, .. }
            | Self::MessageEnd { message } => Some(message),
            Self::AgentStart
            | Self::AgentEnd { .. }
            | Self::TurnStart
            | Self::TurnEnd { .. }
            | Self::PromptProgress { .. }
            | Self::ToolExecutionStart { .. }
            | Self::ToolExecutionUpdate { .. }
            | Self::ToolExecutionEnd { .. }
            | Self::AutoRetryStart { .. }
            | Self::AutoRetryEnd { .. }
            | Self::CompactionStart { .. }
            | Self::CompactionSummaryDelta { .. }
            | Self::CompactionEnd { .. }
            | Self::SessionInfoChanged { .. }
            | Self::ServiceTierChanged { .. }
            | Self::SessionActionUpdate { .. }
            | Self::GoalUpdate { .. }
            | Self::ChatTurnWait { .. }
            | Self::MemoryUpdate { .. }
            | Self::AgentRelay(_)
            | Self::BashStart { .. }
            | Self::BashOutput { .. }
            | Self::BashEnd { .. }
            | Self::RefineComplete { .. }
            | Self::RefineFailed { .. }
            | Self::IpythonSentAgentMessage { .. } => None,
        }
    }
}

/// The terminal assistant message of a turn and the tool results after it.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TurnAnswer {
    pub message: AgentMessage,
    pub tool_results: Vec<AgentMessage>,
}

/// The change one `message_update` applies to the streaming assistant
/// message. The deltas of one kind may arrive merged.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum StreamUpdate {
    Start,
    TextStart,
    TextDelta {
        delta: String,
    },
    TextEnd,
    ThinkingStart,
    ThinkingDelta {
        delta: String,
    },
    ThinkingEnd,
    ToolcallStart,
    ToolcallDelta {
        delta: String,
    },
    ToolcallEnd,
    /// The whole message was replaced.
    Message,
}

/// A tool's output: its content blocks and structured details.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ToolOutput {
    pub content: Vec<UserContentBlock>,
    pub details: Option<Value>,
}

/// A provider failover: the failed request re-routes to `backup_model`
/// ("provider/model-id") at once.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Failover {
    pub reason: FailoverReason,
    pub backup_model: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum FailoverReason {
    Backup,
}

/// Why a compaction runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum CompactionReason {
    /// The user asked (`/compact`, the `compact` command).
    Manual,
    /// The context crossed the compaction threshold.
    Threshold,
    /// A request overflowed the context window.
    Overflow,
}

impl CompactionReason {
    /// The wire name.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Manual => "manual",
            Self::Threshold => "threshold",
            Self::Overflow => "overflow",
        }
    }
}

/// What a compaction produced.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompactionResult {
    pub summary: String,
    /// The first entry the summary keeps after it (manual compactions).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_kept_entry_id: Option<String>,
    /// The context size before the compaction.
    pub tokens_before: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ErrorSeverity {
    Warning,
    Error,
}

/// The identity of one user shell run: a `transient` run belongs to a side
/// conversation and shows only in the pane of the client that started it
/// (`run_id`).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BashRun {
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub transient: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub run_id: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::daemon::rt;

    #[test]
    fn lifecycle_and_message_events_roundtrip() {
        let assistant = r#"{"role":"assistant","content":[{"type":"text","text":"hi"}],"api":"a","provider":"p","model":"m","usage":{"input":0,"output":0,"cacheRead":0,"cacheWrite":0,"totalTokens":0,"cost":{"input":0,"output":0,"cacheRead":0,"cacheWrite":0,"total":0}},"stopReason":"stop","timestamp":1}"#;
        let result = r#"{"role":"toolResult","toolCallId":"c","toolName":"ipython","content":[{"type":"text","text":"1"}],"isError":false,"timestamp":2}"#;
        rt::<SessionEvent>(r#"{"type":"agent_start"}"#);
        rt::<SessionEvent>(&format!(
            r#"{{"type":"agent_end","messages":[{assistant}]}}"#
        ));
        rt::<SessionEvent>(r#"{"type":"turn_end","error":"boom"}"#);
        rt::<SessionEvent>(&format!(
            r#"{{"type":"turn_end","message":{assistant},"toolResults":[{result}]}}"#
        ));
        rt::<SessionEvent>(&format!(
            r#"{{"type":"message_start","message":{assistant},"assistantMessageEvent":{{"type":"start"}}}}"#
        ));
        rt::<SessionEvent>(&format!(
            r#"{{"type":"message_update","message":{assistant},"assistantMessageEvent":{{"type":"text_delta","delta":"hi"}}}}"#
        ));
        rt::<SessionEvent>(
            r#"{"type":"message_end","message":{"role":"user","content":"hi","timestamp":1}}"#,
        );
    }

    #[test]
    fn tool_retry_and_compaction_events_roundtrip() {
        rt::<SessionEvent>(
            r#"{"type":"tool_execution_end","toolCallId":"c","toolName":"ipython","result":{"content":[{"type":"text","text":"1"}],"details":null},"isError":false}"#,
        );
        rt::<SessionEvent>(
            r#"{"type":"auto_retry_start","attempt":1,"maxAttempts":3,"delayMs":200,"errorMessage":"e","reason":"backup","backupModel":"p/m"}"#,
        );
        rt::<SessionEvent>(
            r#"{"type":"auto_retry_start","attempt":1,"delayMs":200,"errorMessage":"e"}"#,
        );
        rt::<SessionEvent>(
            r#"{"type":"compaction_end","reason":"manual","result":{"summary":"s","firstKeptEntryId":"7","tokensBefore":10},"aborted":false,"willRetry":false,"customInstructions":"focus"}"#,
        );
        rt::<SessionEvent>(
            r#"{"type":"compaction_end","reason":"threshold","aborted":false,"willRetry":false,"errorMessage":"skipped","errorSeverity":"warning"}"#,
        );
        rt::<SessionEvent>(
            r#"{"type":"bash_end","exitCode":null,"cancelled":true,"output":"tail","omitted":{"bytes":10,"lines":2,"at":"start"},"artifact":"/tmp/out","transient":true,"runId":"r"}"#,
        );
    }
}
