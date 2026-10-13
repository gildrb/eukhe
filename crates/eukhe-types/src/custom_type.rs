//! The `customType` of a custom message or custom state row. The string
//! parses into [`CustomType`] once, at deserialization; the engine writes
//! and every client renders by matching the enum, never the string.
//!
//! The set is open: clients define their own types (the
//! `append_custom_message` request and a prompt's `customMessage` carry
//! any non-empty `customType`, e.g. `sideQuestion`), and sessions written
//! by other builds may hold types this build does not know. Those parse
//! into [`CustomType::Other`] and serialize back byte-identical, so they
//! render as the generic panel and round-trip through every store. The
//! engine never writes `Other`: each type it produces has a variant.

use serde::{Deserialize, Deserializer, Serialize, Serializer};

macro_rules! custom_types {
    ($($(#[$meta:meta])* $variant:ident => $string:literal,)*) => {
        /// The type of one custom message or custom state row.
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub enum CustomType {
            $($(#[$meta])* $variant,)*
            /// A type the engine does not produce: a client-defined type
            /// or one from another build (see the module docs).
            Other(String),
        }

        impl CustomType {
            /// Every type the engine produces.
            pub const KNOWN: &'static [CustomType] = &[$(Self::$variant,)*];

            /// The type named by a `customType` string.
            #[must_use]
            pub fn parse(custom_type: &str) -> Self {
                match custom_type {
                    $($string => Self::$variant,)*
                    other => Self::Other(other.to_owned()),
                }
            }

            /// The `customType` string.
            #[must_use]
            pub fn as_str(&self) -> &str {
                match self {
                    $(Self::$variant => $string,)*
                    Self::Other(other) => other,
                }
            }
        }
    };
}

custom_types! {
    /// Mail from another agent session.
    AgentMessage => "agent_message",
    /// An agent's answer to the user's `@name` message.
    AgentReply => "agent_reply",
    /// The answering agent's hidden bookkeeping row: its run owes the
    /// asking session the final answer.
    AgentReplyOwed => "agent_reply_owed",
    /// A heartbeat fire's injected prompt.
    HeartbeatPrompt => "heartbeat_prompt",
    /// A goal continuation prompt.
    GoalContext => "goal_context",
    /// The persisted goal state (a custom state row).
    GoalState => "thread_goal_state",
    /// An autonomous-mode status notice.
    AutonomousStatus => "autonomous_status",
    /// The ipython namespace notice a compaction leaves.
    IpythonState => "ipython_state",
    IpythonStateRestored => "ipython_state_restored",
    PythonSkillsUnavailable => "python_skills_unavailable",
    /// A child run failed (rows written before child reports became
    /// typed inputs).
    RlmChildFailure => "rlm_child_failure",
    /// A child run ended without a reply (rows written before child
    /// reports became typed inputs).
    RlmChildTerminalNotice => "rlm_child_terminal_notice",
    /// A detached kernel bash command finished.
    AsyncBashCompletion => "async_bash_completion",
    /// A detached `ipython` cell settled.
    JobSettled => "job_settled",
    CompactionOutcome => "compaction_outcome",
    RefinementOutcome => "refinement_outcome",
    /// The model-facing notice of an applied refinement.
    RefinementNotice => "refinement_notice",
    /// The audit row of one applied refinement (a custom state row).
    RefinementAudit => "eukhe.refinement",
    /// The model-facing digest of the continual-harness state.
    HarnessDigest => "harness_digest",
    /// The one outcome row of a provider retry episode.
    ProviderRetryOutcome => "provider_retry_outcome",
    /// A session parked until its provider quota resets (a custom state
    /// row).
    ProviderQuotaPark => "provider_quota_park",
    /// A parked session resumed, or its wake was dropped (a custom state
    /// row).
    ProviderQuotaResume => "provider_quota_resume",
    ModelPromptError => "model_prompt_error",
    /// The notice a rename that changed an existing name leaves.
    SessionRenamed => "session_renamed",
    /// The marker that the Anthropic subscription warning was shown (a
    /// custom state row).
    AnthropicSubscriptionWarningShown => "anthropic_subscription_warning_shown",
    /// The echo of a session slash command.
    SessionSlashCommand => "session_slash_command",
    SessionSlashCommandResult => "session_slash_command_result",
}

impl std::fmt::Display for CustomType {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.as_str())
    }
}

impl Serialize for CustomType {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for CustomType {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let custom_type = std::borrow::Cow::<'de, str>::deserialize(deserializer)?;
        Ok(Self::parse(&custom_type))
    }
}

#[cfg(test)]
mod tests {
    use super::CustomType;

    #[test]
    fn every_type_round_trips_through_its_string() {
        let other = CustomType::Other("sideQuestion".to_owned());
        for custom_type in CustomType::KNOWN.iter().chain([&other]) {
            assert_eq!(&CustomType::parse(custom_type.as_str()), custom_type);
            let wire = serde_json::to_value(custom_type).unwrap();
            assert_eq!(wire, serde_json::Value::from(custom_type.as_str()));
            assert_eq!(
                &serde_json::from_value::<CustomType>(wire).unwrap(),
                custom_type
            );
        }
    }

    #[test]
    fn known_strings_never_parse_as_other() {
        for custom_type in CustomType::KNOWN {
            assert!(!matches!(custom_type, CustomType::Other(_)));
        }
        assert_eq!(
            CustomType::parse("eukhe.refinement"),
            CustomType::RefinementAudit
        );
    }
}

#[cfg(test)]
mod persisted {
    use super::CustomType;
    use crate::session::FileEntry;

    /// Session lines written before the field was typed decode into the
    /// typed rows and write back byte-identical, an engine type and a
    /// client-defined one alike.
    #[test]
    fn old_session_rows_round_trip() {
        let lines = [
            r#"{"type":"custom_message","id":"a1","parentId":null,"timestamp":"2026-09-23T00:00:00.000Z","customType":"harness_digest","content":"digest","display":false}"#,
            r#"{"type":"custom_message","id":"a2","parentId":"a1","timestamp":"2026-09-23T00:00:01.000Z","customType":"sideQuestion","content":"why","display":true,"details":{"k":1}}"#,
            r#"{"type":"custom","id":"a3","parentId":"a2","timestamp":"2026-09-23T00:00:02.000Z","customType":"thread_goal_state","data":{"x":1}}"#,
        ];
        let mut types = Vec::new();
        for line in lines {
            let entry: FileEntry = serde_json::from_str(line).expect("old row decodes");
            types.push(match &entry {
                FileEntry::CustomMessage { payload, .. } => payload.custom_type.clone(),
                FileEntry::Custom { payload, .. } => payload.custom_type.clone(),
                other => panic!("a custom row: {other:?}"),
            });
            assert_eq!(
                serde_json::to_value(&entry).unwrap(),
                serde_json::from_str::<serde_json::Value>(line).unwrap()
            );
        }
        assert_eq!(
            types,
            [
                CustomType::HarnessDigest,
                CustomType::Other("sideQuestion".to_owned()),
                CustomType::GoalState,
            ]
        );
    }
}
