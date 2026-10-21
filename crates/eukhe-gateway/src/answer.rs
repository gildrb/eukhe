//! What a settled session event tells the Signal peer that holds the
//! floor: the agent's text, a failure, or a stop.

use eukhe_types::ai::{AssistantContentBlock, StopReason};
use eukhe_types::daemon::SessionEvent;
use eukhe_types::session::AgentMessage;

/// One reply-worthy outcome of the bound session.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Answer {
    /// The agent's final text (Markdown).
    Text(String),
    /// A failed model request or turn: the reason, on one line.
    Failed(String),
    /// The turn was stopped.
    Stopped,
}

/// What a run that ends without an assistant message tells the phone.
const NO_MODEL_ANSWER: &str =
    "the turn ended before the model answered. Send /status to see the model";

/// The answer `event` carries: a settled assistant message's text (none
/// when it has no text), failure or stop; the error of a turn that
/// faulted without an assistant message; or, for a run that ended with no
/// assistant message at all (no model configured, a request that never
/// started), [`NO_MODEL_ANSWER`]. A tool-use step answers nothing.
pub(crate) fn answer(event: &SessionEvent) -> Option<Answer> {
    match event {
        SessionEvent::AgentEnd { messages } => (!messages
            .iter()
            .any(|message| matches!(message, AgentMessage::Assistant(_))))
        .then(|| Answer::Failed(NO_MODEL_ANSWER.to_string())),
        SessionEvent::MessageEnd {
            message: AgentMessage::Assistant(message),
        } => match message.stop_reason {
            StopReason::Stop | StopReason::Length => {
                let text = message
                    .content
                    .iter()
                    .filter_map(|block| match block {
                        AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                        AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n\n");
                (!text.trim().is_empty()).then_some(Answer::Text(text))
            }
            StopReason::Error => Some(Answer::Failed(failure_line(
                message.error_message.as_deref(),
            ))),
            StopReason::Aborted => Some(Answer::Stopped),
            StopReason::ToolUse => None,
        },
        SessionEvent::TurnEnd {
            answer: None,
            error: Some(error),
        } => Some(Answer::Failed(failure_line(Some(error)))),
        SessionEvent::AgentStart
        | SessionEvent::TurnStart
        | SessionEvent::TurnEnd { .. }
        | SessionEvent::PromptProgress { .. }
        | SessionEvent::MessageStart { .. }
        | SessionEvent::MessageUpdate { .. }
        | SessionEvent::MessageEnd { .. }
        | SessionEvent::ToolExecutionStart { .. }
        | SessionEvent::ToolExecutionUpdate { .. }
        | SessionEvent::ToolExecutionEnd { .. }
        | SessionEvent::AutoRetryStart { .. }
        | SessionEvent::AutoRetryEnd { .. }
        | SessionEvent::CompactionStart { .. }
        | SessionEvent::CompactionSummaryDelta { .. }
        | SessionEvent::CompactionEnd { .. }
        | SessionEvent::SessionInfoChanged { .. }
        | SessionEvent::ServiceTierChanged { .. }
        | SessionEvent::SessionActionUpdate { .. }
        | SessionEvent::GoalUpdate { .. }
        | SessionEvent::ChatTurnWait { .. }
        | SessionEvent::MemoryUpdate { .. }
        | SessionEvent::AgentRelay(_)
        | SessionEvent::BashStart { .. }
        | SessionEvent::BashOutput { .. }
        | SessionEvent::BashEnd { .. }
        | SessionEvent::RefineComplete { .. }
        | SessionEvent::RefineFailed { .. }
        | SessionEvent::IpythonSentAgentMessage { .. } => None,
    }
}

/// `reason` on one line; a missing or blank reason names the failure.
fn failure_line(reason: Option<&str>) -> String {
    reason
        .filter(|reason| !reason.trim().is_empty())
        .unwrap_or("the model request failed")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

#[cfg(test)]
mod tests;
