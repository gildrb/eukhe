//! When a response streamed, and how far the server got through the prompt.

use serde::{Deserialize, Serialize};

/// When the stream of one response gave its first byte, its first token and
/// its last token: milliseconds after the request started (the message's
/// `timestamp`), measured with a monotonic clock. Set by
/// `AssistantMessageEventStream` on the final message of a response it saw
/// start; a mark the stream never reached is `None`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ResponseTiming {
    /// The provider answered (the stream's `start` event).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_byte_ms: Option<u64>,
    /// The first text, thinking or tool-call token: the time to first token.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_token_ms: Option<u64>,
    /// The last text, thinking or tool-call token.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_token_ms: Option<u64>,
}

/// How far a server got through the prompt before the first token
/// (llama.cpp `llama-server` `prompt_progress`, sent when the request sets
/// `return_progress`). `processed` includes the `cache` tokens.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PromptProgress {
    /// Prompt tokens in all.
    pub total: u64,
    /// Prompt tokens the server took from its cache.
    pub cache: u64,
    /// Prompt tokens done so far, the cached ones included.
    pub processed: u64,
    /// Milliseconds the server spent on the prompt so far.
    pub time_ms: u64,
}
