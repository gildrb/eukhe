//! The stored entry's `type` tag, parsed once when a row is read.

use serde::de::{self, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

/// A session row's `type`. Tags this daemon never reads keep their text in
/// `Other`, so a row round-trips byte-identical.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EntryType {
    Session,
    Message,
    CustomMessage,
    Custom,
    ModelChange,
    ThinkingLevelChange,
    ServiceTierChange,
    SessionInfo,
    SessionState,
    Label,
    Compaction,
    BranchSummary,
    ChildUsageAttributed,
    Other(String),
}

impl EntryType {
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::Session => "session",
            Self::Message => "message",
            Self::CustomMessage => "custom_message",
            Self::Custom => "custom",
            Self::ModelChange => "model_change",
            Self::ThinkingLevelChange => "thinking_level_change",
            Self::ServiceTierChange => "service_tier_change",
            Self::SessionInfo => "session_info",
            Self::SessionState => "session_state",
            Self::Label => "label",
            Self::Compaction => "compaction",
            Self::BranchSummary => "branch_summary",
            Self::ChildUsageAttributed => "child_usage_attributed",
            Self::Other(tag) => tag,
        }
    }

    /// The known tag `text` names, `None` for any other text.
    fn known(text: &str) -> Option<Self> {
        Some(match text {
            "session" => Self::Session,
            "message" => Self::Message,
            "custom_message" => Self::CustomMessage,
            "custom" => Self::Custom,
            "model_change" => Self::ModelChange,
            "thinking_level_change" => Self::ThinkingLevelChange,
            "service_tier_change" => Self::ServiceTierChange,
            "session_info" => Self::SessionInfo,
            "session_state" => Self::SessionState,
            "label" => Self::Label,
            "compaction" => Self::Compaction,
            "branch_summary" => Self::BranchSummary,
            "child_usage_attributed" => Self::ChildUsageAttributed,
            _ => return None,
        })
    }

    /// Entry types that represent user intent (vs daemon bookkeeping).
    #[must_use]
    pub fn is_content(&self) -> bool {
        match self {
            Self::Message
            | Self::CustomMessage
            | Self::Custom
            | Self::ModelChange
            | Self::ThinkingLevelChange
            | Self::ServiceTierChange
            | Self::SessionInfo
            | Self::Label
            | Self::Compaction
            | Self::BranchSummary => true,
            Self::Session | Self::SessionState | Self::ChildUsageAttributed | Self::Other(_) => {
                false
            }
        }
    }
}

impl From<&str> for EntryType {
    fn from(text: &str) -> Self {
        Self::known(text).unwrap_or_else(|| Self::Other(text.to_owned()))
    }
}

impl From<String> for EntryType {
    fn from(text: String) -> Self {
        Self::known(&text).unwrap_or(Self::Other(text))
    }
}

impl fmt::Display for EntryType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl Serialize for EntryType {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

struct EntryTypeVisitor;

impl Visitor<'_> for EntryTypeVisitor {
    type Value = EntryType;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an entry type string")
    }

    fn visit_str<E: de::Error>(self, text: &str) -> Result<EntryType, E> {
        Ok(EntryType::from(text))
    }

    fn visit_string<E: de::Error>(self, text: String) -> Result<EntryType, E> {
        Ok(EntryType::from(text))
    }
}

impl<'de> Deserialize<'de> for EntryType {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_str(EntryTypeVisitor)
    }
}

impl Default for EntryType {
    /// A row without a `type` (the usage scanner's lenient parse) reads as
    /// the empty tag, matching no known type.
    fn default() -> Self {
        Self::Other(String::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn a_known_tag_parses_to_its_variant() {
        assert_eq!(EntryType::from("message"), EntryType::Message);
        assert_eq!(
            EntryType::from("child_usage_attributed"),
            EntryType::ChildUsageAttributed
        );
    }

    #[test]
    fn an_unknown_tag_keeps_its_text_through_serde() {
        let parsed: EntryType =
            serde_json::from_str(r#""ledger_probe""#).expect("a string tag parses");
        assert_eq!(parsed, EntryType::Other("ledger_probe".to_owned()));
        assert_eq!(
            serde_json::to_string(&parsed).expect("serializes"),
            r#""ledger_probe""#
        );
    }
}
