//! What a settled session event tells the Signal peer that holds the
//! floor: the agent's text, a failure, or a stop. The compiled Bend core
//! decides (`bend/gateway_answer.bend`, entry
//! `bend/ffi_gateway_answer.bend`, laws `laws/gateway_answer.bend`); this
//! file writes what the event holds and reads the answer.

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};
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

/// An error that may be missing, on the wire.
fn maybe(writer: &mut Writer, error: Option<&str>) {
    match error {
        Some(error) => writer.some().str(error),
        None => writer.none(),
    };
}

/// The answer `event` carries: a settled assistant message's text (none
/// when it has no text), failure or stop; the error of a turn that
/// faulted without an assistant message; or, for a run that ended with no
/// assistant message at all (no model configured, a request that never
/// started), a failure that says so. A tool-use step answers nothing.
/// Every text is one the daemon sent: a model's output, far below the
/// wire's `STR_MAX`.
pub(crate) fn answer(event: &SessionEvent) -> Option<Answer> {
    let mut writer = Writer::new();
    match event {
        SessionEvent::AgentEnd { messages } => {
            writer.tag(0).bool(
                messages
                    .iter()
                    .any(|message| matches!(message, AgentMessage::Assistant(_))),
            );
        }
        SessionEvent::MessageEnd {
            message: AgentMessage::Assistant(message),
        } => {
            let stop = match message.stop_reason {
                StopReason::Stop => 0,
                StopReason::Length => 1,
                StopReason::Error => 2,
                StopReason::Aborted => 3,
                StopReason::ToolUse => 4,
            };
            let texts: Vec<&str> = message
                .content
                .iter()
                .filter_map(|block| match block {
                    AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                    AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
                })
                .collect();
            writer.tag(1).tag(stop).count(texts.len());
            for text in texts {
                writer.str(text);
            }
            maybe(&mut writer, message.error_message.as_deref());
        }
        SessionEvent::TurnEnd { answer, error } => {
            writer.tag(2).bool(answer.is_some());
            maybe(&mut writer, error.as_deref());
        }
        SessionEvent::AgentStart
        | SessionEvent::TurnStart
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
        | SessionEvent::MemoryUpdate { .. }
        | SessionEvent::AgentRelay(_)
        | SessionEvent::BashStart { .. }
        | SessionEvent::BashOutput { .. }
        | SessionEvent::BashEnd { .. }
        | SessionEvent::RefineComplete { .. }
        | SessionEvent::RefineFailed { .. }
        | SessionEvent::IpythonSentAgentMessage { .. } => {
            writer.tag(3);
        }
    }
    let mut read = || -> Result<Option<Answer>, Error> {
        let reply = call(Entry::GatewayAnswer, &writer.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let answer = match reader.tag_of(4, "an answer")? {
            0 => None,
            1 => Some(Answer::Text(reader.str()?.to_owned())),
            2 => Some(Answer::Failed(reader.str()?.to_owned())),
            3.. => Some(Answer::Stopped),
        };
        reader.end()?;
        Ok(answer)
    };
    expect_core(Entry::GatewayAnswer, read())
}

#[cfg(test)]
mod tests;
