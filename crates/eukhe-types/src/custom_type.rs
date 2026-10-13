//! The custom message types a client renders with a dedicated row. A
//! custom message's `customType` string parses into [`CustomType`] once;
//! renderers match the enum, never the string.

use crate::slash_commands::{
    SESSION_SLASH_COMMAND_CUSTOM_TYPE, SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
};

/// The type of one custom message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CustomType {
    /// Mail from another agent session.
    AgentMessage,
    /// An agent's answer to the user's `@name` message.
    AgentReply,
    HeartbeatPrompt,
    GoalContext,
    IpythonStateRestored,
    PythonSkillsUnavailable,
    /// A child run failed (rows written before child reports became
    /// typed inputs).
    RlmChildFailure,
    /// A child run ended without a reply (rows written before child
    /// reports became typed inputs).
    RlmChildTerminalNotice,
    /// A detached kernel bash command finished.
    AsyncBashCompletion,
    CompactionOutcome,
    RefinementOutcome,
    /// The one outcome row of a provider retry episode.
    ProviderRetryOutcome,
    ModelPromptError,
    /// The echo of a session slash command.
    SessionSlashCommand,
    SessionSlashCommandResult,
    /// A type without a dedicated row.
    Other(String),
}

impl CustomType {
    /// The type named by a `customType` string.
    #[must_use]
    pub fn parse(custom_type: &str) -> Self {
        match custom_type {
            "agent_message" => Self::AgentMessage,
            "agent_reply" => Self::AgentReply,
            "heartbeat_prompt" => Self::HeartbeatPrompt,
            "goal_context" => Self::GoalContext,
            "ipython_state_restored" => Self::IpythonStateRestored,
            "python_skills_unavailable" => Self::PythonSkillsUnavailable,
            "rlm_child_failure" => Self::RlmChildFailure,
            "rlm_child_terminal_notice" => Self::RlmChildTerminalNotice,
            "async_bash_completion" => Self::AsyncBashCompletion,
            "compaction_outcome" => Self::CompactionOutcome,
            "refinement_outcome" => Self::RefinementOutcome,
            "provider_retry_outcome" => Self::ProviderRetryOutcome,
            "model_prompt_error" => Self::ModelPromptError,
            SESSION_SLASH_COMMAND_CUSTOM_TYPE => Self::SessionSlashCommand,
            SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE => Self::SessionSlashCommandResult,
            other => Self::Other(other.to_owned()),
        }
    }

    /// The `customType` string.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::AgentMessage => "agent_message",
            Self::AgentReply => "agent_reply",
            Self::HeartbeatPrompt => "heartbeat_prompt",
            Self::GoalContext => "goal_context",
            Self::IpythonStateRestored => "ipython_state_restored",
            Self::PythonSkillsUnavailable => "python_skills_unavailable",
            Self::RlmChildFailure => "rlm_child_failure",
            Self::RlmChildTerminalNotice => "rlm_child_terminal_notice",
            Self::AsyncBashCompletion => "async_bash_completion",
            Self::CompactionOutcome => "compaction_outcome",
            Self::RefinementOutcome => "refinement_outcome",
            Self::ProviderRetryOutcome => "provider_retry_outcome",
            Self::ModelPromptError => "model_prompt_error",
            Self::SessionSlashCommand => SESSION_SLASH_COMMAND_CUSTOM_TYPE,
            Self::SessionSlashCommandResult => SESSION_SLASH_COMMAND_RESULT_CUSTOM_TYPE,
            Self::Other(other) => other,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::CustomType;

    #[test]
    fn every_type_parses_from_its_own_string() {
        let types = [
            CustomType::AgentMessage,
            CustomType::AgentReply,
            CustomType::HeartbeatPrompt,
            CustomType::GoalContext,
            CustomType::IpythonStateRestored,
            CustomType::PythonSkillsUnavailable,
            CustomType::RlmChildFailure,
            CustomType::RlmChildTerminalNotice,
            CustomType::AsyncBashCompletion,
            CustomType::CompactionOutcome,
            CustomType::RefinementOutcome,
            CustomType::ProviderRetryOutcome,
            CustomType::ModelPromptError,
            CustomType::SessionSlashCommand,
            CustomType::SessionSlashCommandResult,
            CustomType::Other("autonomous_status".to_owned()),
        ];
        for custom_type in types {
            assert_eq!(CustomType::parse(custom_type.as_str()), custom_type);
        }
    }
}
