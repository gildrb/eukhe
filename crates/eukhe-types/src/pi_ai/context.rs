//! Request contexts: the public [`Context`] and the normalized
//! [`TranscriptContext`] providers receive.

use serde::{Deserialize, Serialize};

use super::message::Message;
use super::tool::Tool;

/// Request input accepted by the public stream entry points. `system_prompt`
/// and `tools` are shorthand for a leading system message; `normalizeContext()`
/// folds them into one before the request reaches a provider.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Context {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub system_prompt: Option<String>,
    pub messages: Vec<Message>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tools: Option<Vec<Tool>>,
}

/// Normalized request context passed to providers and API implementations.
/// The prompt and tool declarations are carried by the transcript's system
/// messages.
///
/// TS brands this type so only `normalizeContext()` produces it; here the
/// field is private and the only constructor is
/// [`TranscriptContext::from_normalized_messages`], reserved for the
/// transcript normalizer (`eukhe_pi_ai::utils::transcript`). It is not
/// deserializable, so a raw [`Context`] cannot become one by accident.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TranscriptContext {
    messages: Vec<Message>,
}

impl TranscriptContext {
    /// Brand already-normalized messages. Only the transcript normalizer
    /// (`normalizeContext`, `collapseSystemMessages`) calls this.
    #[doc(hidden)]
    #[must_use]
    pub fn from_normalized_messages(messages: Vec<Message>) -> Self {
        Self { messages }
    }

    /// The transcript.
    #[must_use]
    pub fn messages(&self) -> &[Message] {
        &self.messages
    }

    /// Take the transcript.
    #[must_use]
    pub fn into_messages(self) -> Vec<Message> {
        self.messages
    }
}
