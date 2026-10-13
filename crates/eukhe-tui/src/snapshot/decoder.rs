//! The live-event decoder: the `TurnUpdate` vocabulary, the
//! `event_to_update` fold (one typed session event -> the transcript
//! update), the loader-note partial decode, and the message helpers (moved
//! with their concern).
use super::{assistant_value_to_entries, ChatEntry};
use eukhe_types::ai::{AssistantMessage, ServiceTier, UserContent, UserContentBlock};
use eukhe_types::custom_type::CustomType;
use eukhe_types::daemon::{
    AgentRelayEvent, BashRun, CompactionReason, CompactionResult, ErrorSeverity, Failover,
    MemoryUpdate, SessionActionSnapshot, SessionEvent, StreamUpdate, ToolOutput,
};
use eukhe_types::goal::GoalState;
use eukhe_types::session::{AgentMessage, CompactionSummaryMessage};

/// One session event decoded for the transcript.
#[derive(Debug, Clone, PartialEq)]
pub enum TurnUpdate {
    /// `agent_start` / `turn_start`.
    TurnStarted,
    /// `session_info_changed`: the session display name (cleared when the
    /// event carries none).
    SessionInfoChanged { name: Option<String> },
    /// `service_tier_changed`: the session's effective service tier.
    ServiceTierChanged { tier: ServiceTier },
    /// `message_start` with a user message.
    UserMessage(String),
    /// `message_start`/`message_update`/`message_end` with an assistant
    /// message; `streaming` distinguishes in-flight from final.
    AssistantMessage {
        message: Box<AssistantMessage>,
        streaming: bool,
        stream_event: Option<StreamUpdate>,
    },
    /// `tool_execution_start`: a tool call began executing.
    ToolExecutionStart {
        tool_call_id: String,
        tool_name: String,
        args: serde_json::Value,
    },
    /// `tool_execution_update`: a partial tool result.
    ToolExecutionUpdate {
        tool_call_id: String,
        partial: ToolOutput,
    },
    /// `tool_execution_end`: the final tool result.
    ToolExecutionEnd {
        tool_call_id: String,
        result: ToolOutput,
        is_error: bool,
    },
    /// `turn_end`, with the turn error string when the turn failed.
    TurnEnded { error: Option<String> },
    /// A `custom`-role message the transcript renders.
    CustomRow(ChatEntry),
    /// `auto_retry_start`: a provider failure is being retried after
    /// `delay_ms` (TS retry loader countdown). A `Backup` reason is a
    /// provider-failover switch: the failed turn re-routes to
    /// `backup_model` ("provider/model-id") immediately.
    AutoRetryStart {
        attempt: u32,
        max_attempts: Option<u32>,
        delay_ms: u64,
        error_message: String,
        reason: RetryStartReason,
    },
    /// `auto_retry_end`: the retry loop settled; `final_error` is set when
    /// the retries were exhausted; `restored_model` is the primary model
    /// restored after a failover switch succeeded.
    AutoRetryEnd {
        success: bool,
        attempt: u32,
        final_error: Option<String>,
        restored_model: Option<String>,
    },
    /// `agent_end`: the prompt queue drained.
    Idle,
    /// `compaction_start`: a compaction run began (TS compaction loader).
    CompactionStart {
        reason: CompactionReason,
        /// `/compact <instructions>` focus guidance.
        custom_instructions: Option<String>,
    },
    /// `compaction_summary_delta`: one streamed chunk of the summary the
    /// compaction model is generating. The chunks accumulate onto the live
    /// loader's state; the settling `compaction_end` clears the streamed
    /// block when its durable summary row lands.
    CompactionSummaryDelta { delta: String },
    /// `compaction_end`: the compaction settled. Success carries the result
    /// (summary + token counts); skip/failure carries the error message and
    /// its severity (TS shows those for `manual` runs).
    CompactionEnd {
        reason: CompactionReason,
        result: Option<CompactionResult>,
        /// `/compact <instructions>` focus guidance (the event payload).
        custom_instructions: Option<String>,
        /// `true` when the run was cancelled.
        aborted: bool,
        error_message: Option<String>,
        error_severity: Option<ErrorSeverity>,
    },
    /// `chat_turn_wait`: this session's turn waits for another window's
    /// turn on the shared chat (`waiting`), or that wait ended. The loader
    /// note shows the wait; nothing lands in the transcript.
    ChatTurnWait { waiting: bool },
    /// `memory_update`: the chat memory's compactor summarized lines or
    /// merged the view. A live transcript row (display only) and the
    /// status gauge's view size.
    MemoryUpdate(MemoryUpdate),
    /// `agent_relay`: two non-root agents of this session's family
    /// exchanged a message. A display-only transcript row; never sent to
    /// a model.
    AgentRelay(AgentRelayEvent),
    /// `goal_update`: the session goal state changed (the session view
    /// owns announcement and tray rendering).
    GoalUpdate(GoalState),
    /// `session_action_update`: the queue projection changed (a message
    /// parked behind the run, was delivered, or was cleared).
    QueueUpdated(crate::queued::QueuedMessages),
    /// `bash_start` (the user-bash slot, TS `!command`): a command run
    /// outside the model loop; `transient` marks a side-conversation run
    /// that renders only in the owning client's pane.
    BashStart {
        command: String,
        exclude_from_context: bool,
        run: BashRun,
    },
    /// `bash_output` (the user-bash slot): one streamed output chunk.
    BashOutput { chunk: String },
    /// `bash_end` (the user-bash slot): the settled run.
    BashEnd {
        exit_code: Option<i64>,
        cancelled: bool,
        /// The run's output, bounded once by the daemon.
        output: String,
        omitted: Option<eukhe_types::output::OmittedOutput>,
        artifact: Option<String>,
        error_message: Option<String>,
        run: BashRun,
    },
    /// An event that changes nothing the transcript shows.
    StatusUpdate,
}

/// Why one `auto_retry_start` fired.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RetryStartReason {
    /// Ordinary quick retry on the current provider.
    Quick,
    /// Provider-failover switch: the failed turn re-routes to
    /// `backup_model` ("provider/model-id").
    Backup { backup_model: String },
}

/// Decode one session event.
#[must_use]
pub fn event_to_update(event: &SessionEvent) -> TurnUpdate {
    match event {
        SessionEvent::AgentStart | SessionEvent::TurnStart => TurnUpdate::TurnStarted,
        SessionEvent::AgentEnd { .. } => TurnUpdate::Idle,
        SessionEvent::TurnEnd { error, .. } => TurnUpdate::TurnEnded {
            error: error.clone(),
        },
        SessionEvent::MessageStart {
            message,
            assistant_message_event,
        } => match message {
            AgentMessage::User(user) => match user_display_text(&user.content) {
                Some(text) => TurnUpdate::UserMessage(text),
                // Nothing to show: the transcript does not grow a blank row.
                None => TurnUpdate::StatusUpdate,
            },
            AgentMessage::Assistant(message) => TurnUpdate::AssistantMessage {
                message: Box::new(message.clone()),
                streaming: true,
                stream_event: assistant_message_event.clone(),
            },
            // Custom rows arrive as a message_start + message_end pair
            // carrying the same payload; only the start adds the row.
            AgentMessage::Custom(custom) => {
                match crate::custom_message::custom_message_entries(
                    &CustomType::parse(&custom.custom_type),
                    &custom.content,
                    custom.display,
                    custom.details.as_ref(),
                )
                .first()
                {
                    Some(entry) => TurnUpdate::CustomRow(entry.clone()),
                    None => TurnUpdate::StatusUpdate,
                }
            }
            // Tool results arrive as tool_execution events; bash runs and
            // summaries as their own events or a transcript rebuild.
            AgentMessage::ToolResult(_)
            | AgentMessage::BashExecution(_)
            | AgentMessage::BranchSummary(_)
            | AgentMessage::CompactionSummary(_) => TurnUpdate::StatusUpdate,
        },
        SessionEvent::MessageUpdate {
            message,
            assistant_message_event,
        } => match message {
            AgentMessage::Assistant(message) => TurnUpdate::AssistantMessage {
                message: Box::new(message.clone()),
                streaming: true,
                stream_event: Some(assistant_message_event.clone()),
            },
            AgentMessage::User(_)
            | AgentMessage::ToolResult(_)
            | AgentMessage::BashExecution(_)
            | AgentMessage::Custom(_)
            | AgentMessage::BranchSummary(_)
            | AgentMessage::CompactionSummary(_) => TurnUpdate::StatusUpdate,
        },
        SessionEvent::MessageEnd { message } => match message {
            AgentMessage::Assistant(message) => TurnUpdate::AssistantMessage {
                message: Box::new(message.clone()),
                streaming: false,
                stream_event: None,
            },
            // A user or custom row renders from its message_start twin.
            AgentMessage::User(_)
            | AgentMessage::ToolResult(_)
            | AgentMessage::BashExecution(_)
            | AgentMessage::Custom(_)
            | AgentMessage::BranchSummary(_)
            | AgentMessage::CompactionSummary(_) => TurnUpdate::StatusUpdate,
        },
        SessionEvent::ToolExecutionStart {
            tool_call_id,
            tool_name,
            args,
        } => TurnUpdate::ToolExecutionStart {
            tool_call_id: tool_call_id.clone(),
            tool_name: tool_name.clone(),
            args: args.clone(),
        },
        SessionEvent::ToolExecutionUpdate {
            tool_call_id,
            partial_result,
            ..
        } => TurnUpdate::ToolExecutionUpdate {
            tool_call_id: tool_call_id.clone(),
            partial: partial_result.clone(),
        },
        SessionEvent::ToolExecutionEnd {
            tool_call_id,
            result,
            is_error,
            ..
        } => TurnUpdate::ToolExecutionEnd {
            tool_call_id: tool_call_id.clone(),
            result: result.clone(),
            is_error: *is_error,
        },
        SessionEvent::AutoRetryStart {
            attempt,
            max_attempts,
            delay_ms,
            error_message,
            failover,
        } => TurnUpdate::AutoRetryStart {
            attempt: saturating_u32(*attempt),
            max_attempts: max_attempts.map(saturating_u32),
            delay_ms: *delay_ms,
            error_message: error_message.clone(),
            reason: match failover {
                Some(Failover { backup_model, .. }) => RetryStartReason::Backup {
                    backup_model: backup_model.clone(),
                },
                None => RetryStartReason::Quick,
            },
        },
        SessionEvent::AutoRetryEnd {
            success,
            attempt,
            final_error,
            restored_model,
        } => TurnUpdate::AutoRetryEnd {
            success: *success,
            attempt: saturating_u32(*attempt),
            final_error: final_error.clone(),
            restored_model: restored_model.clone(),
        },
        SessionEvent::CompactionStart {
            reason,
            custom_instructions,
        } => TurnUpdate::CompactionStart {
            reason: *reason,
            custom_instructions: custom_instructions.clone(),
        },
        SessionEvent::CompactionSummaryDelta { delta } => TurnUpdate::CompactionSummaryDelta {
            delta: delta.clone(),
        },
        SessionEvent::CompactionEnd {
            reason,
            result,
            aborted,
            error_message,
            error_severity,
            custom_instructions,
            ..
        } => TurnUpdate::CompactionEnd {
            reason: *reason,
            result: result.clone(),
            custom_instructions: custom_instructions.clone(),
            aborted: *aborted,
            error_message: error_message.clone(),
            error_severity: *error_severity,
        },
        SessionEvent::SessionInfoChanged { name } => {
            TurnUpdate::SessionInfoChanged { name: name.clone() }
        }
        SessionEvent::ServiceTierChanged { service_tier } => TurnUpdate::ServiceTierChanged {
            tier: *service_tier,
        },
        SessionEvent::SessionActionUpdate { actions } => {
            TurnUpdate::QueueUpdated(queued_messages(actions))
        }
        SessionEvent::GoalUpdate { goal } => TurnUpdate::GoalUpdate(goal.clone()),
        SessionEvent::ChatTurnWait { waiting } => TurnUpdate::ChatTurnWait { waiting: *waiting },
        SessionEvent::MemoryUpdate { update } => TurnUpdate::MemoryUpdate(update.clone()),
        SessionEvent::AgentRelay(relay) => TurnUpdate::AgentRelay(relay.clone()),
        SessionEvent::BashStart {
            command,
            exclude_from_context,
            run,
        } => TurnUpdate::BashStart {
            command: command.clone(),
            exclude_from_context: *exclude_from_context,
            run: run.clone(),
        },
        SessionEvent::BashOutput { chunk } => TurnUpdate::BashOutput {
            chunk: chunk.clone(),
        },
        SessionEvent::BashEnd {
            exit_code,
            cancelled,
            output,
            omitted,
            artifact,
            error_message,
            run,
        } => TurnUpdate::BashEnd {
            exit_code: *exit_code,
            cancelled: *cancelled,
            output: output.clone(),
            omitted: *omitted,
            artifact: artifact.clone(),
            error_message: error_message.clone(),
            run: run.clone(),
        },
        SessionEvent::RefineComplete { .. }
        | SessionEvent::RefineFailed { .. }
        | SessionEvent::IpythonSentAgentMessage { .. } => TurnUpdate::StatusUpdate,
    }
}

fn saturating_u32(value: u64) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

/// The queue strip's state from one queue projection. `starting` carries
/// the picked-up prompt whose turn is still preparing (TS #2063
/// `sessionActions.active` with `kind: "turn"` / `phase: "preparing"`), so
/// the strip keeps it visible until the turn begins.
#[must_use]
pub fn queued_messages(actions: &SessionActionSnapshot) -> crate::queued::QueuedMessages {
    let starting = actions
        .active
        .as_ref()
        .filter(|active| active.kind == "turn" && active.phase == "preparing")
        .map(|active| active.label.clone().unwrap_or_default());
    crate::queued::QueuedMessages {
        steering: actions.steering.clone(),
        follow_ups: actions.follow_ups.clone(),
        starting,
    }
}

/// The loader note from a `tool_execution_update` partial result, if the
/// tool owns one. The python-kernel bootstrap reports its startup stages as
/// partial results with `details.status = "starting"` (TS
/// `reportStartupProgress`), so the loader row mirrors the stage text.
/// `None` leaves any current note untouched: streamed cell output reports
/// `ok`, which is not a note change.
#[must_use]
pub fn working_message_from_update(partial: &ToolOutput) -> Option<String> {
    let status = partial
        .details
        .as_ref()
        .and_then(|details| details.get("status"))
        .and_then(serde_json::Value::as_str);
    if status != Some("starting") {
        return None;
    }
    partial
        .content
        .iter()
        .find_map(|block| match block {
            UserContentBlock::Text(text) => Some(text.text.clone()),
            UserContentBlock::Image(_) | UserContentBlock::Raw(_) => None,
        })
        .filter(|text| !text.is_empty())
}

/// The user-message display text (TS `conversation-components`' user
/// branch): the text blocks joined, or the `[image]` placeholder when the
/// message carries content but no text (an image-only prompt), or `None`
/// for a message with nothing to show.
#[must_use]
pub fn user_display_text(content: &UserContent) -> Option<String> {
    let text = content_text(content);
    if !text.is_empty() {
        return Some(text);
    }
    match content {
        UserContent::Text(content) if !content.is_empty() => Some("[image]".to_string()),
        UserContent::Blocks(blocks) if !blocks.is_empty() => Some("[image]".to_string()),
        UserContent::Text(_) | UserContent::Blocks(_) => None,
    }
}

/// Concatenated text of a message's content: the string, or every block's
/// text (tagged text blocks and the engine's untagged `{"text": ...}`
/// form). Adjacent fragments concatenate without separators, like the TS
/// message rendering.
#[must_use]
pub fn content_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks.iter().filter_map(UserContentBlock::text).collect(),
    }
}

/// Fold one message into chat entries. Assistant messages expand into a
/// message component (ordered text/thinking blocks) plus one card per tool
/// call, in content order.
#[must_use]
pub fn message_value_to_entries(message: &AgentMessage) -> Vec<ChatEntry> {
    match message {
        // TS `addMessageToChat`'s user case: a text that IS a skill block
        // renders the skill-invocation card (+ the trailing argument text
        // as its own user block); every other text renders the user block.
        AgentMessage::User(user) => user_display_text(&user.content)
            .map(|text| {
                crate::custom_message::skill_invocation_entries(&text)
                    .unwrap_or_else(|| vec![ChatEntry::User { text }])
            })
            .unwrap_or_default(),
        AgentMessage::Assistant(assistant) => assistant_value_to_entries(assistant),
        AgentMessage::Custom(custom) => crate::custom_message::custom_message_entries(
            &CustomType::parse(&custom.custom_type),
            &custom.content,
            custom.display,
            custom.details.as_ref(),
        ),
        AgentMessage::CompactionSummary(summary) => vec![compaction_summary_entry(summary)],
        // Tool results fold onto their cards (`transcript_to_entries`); bash
        // runs and branch summaries have no transcript row here.
        AgentMessage::ToolResult(_)
        | AgentMessage::BashExecution(_)
        | AgentMessage::BranchSummary(_) => Vec::new(),
    }
}

/// The compaction summary row (TS `CompactionSummaryMessageComponent`).
fn compaction_summary_entry(summary: &CompactionSummaryMessage) -> ChatEntry {
    ChatEntry::CompactionSummary {
        summary: summary.summary.clone(),
        tokens_before: summary.tokens_before,
        custom_instructions: summary.custom_instructions.clone(),
    }
}
