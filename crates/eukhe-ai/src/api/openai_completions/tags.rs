//! The `OpenAI` Chat Completions wire tags eukhe reads, parsed with
//! [`wire_type`](crate::utils::wire_type::wire_type).

use serde::Deserialize;

/// A `reasoning_details` entry's `type`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
pub(crate) enum ReasoningDetailType {
    #[serde(rename = "reasoning.summary")]
    Summary,
    #[serde(rename = "reasoning.encrypted")]
    Encrypted,
    #[serde(rename = "reasoning.text")]
    Text,
}

/// A message content part's `type`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum PartType {
    Text,
}
