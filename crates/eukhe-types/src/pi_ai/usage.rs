//! Token usage, its cost, and stop reasons.

use serde::{Deserialize, Serialize};

use super::string_enum::string_enum;

/// Cost of a [`Usage`] in dollars.
#[derive(Debug, Clone, Copy, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UsageCost {
    #[serde(serialize_with = "super::js_number::serialize")]
    pub input: f64,
    #[serde(serialize_with = "super::js_number::serialize")]
    pub output: f64,
    #[serde(serialize_with = "super::js_number::serialize")]
    pub cache_read: f64,
    #[serde(serialize_with = "super::js_number::serialize")]
    pub cache_write: f64,
    #[serde(serialize_with = "super::js_number::serialize")]
    pub total: f64,
}

/// Token usage of one response.
#[derive(Debug, Clone, Copy, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Usage {
    pub input: u64,
    pub output: u64,
    pub cache_read: u64,
    pub cache_write: u64,
    /// Subset of `cache_write` written with 1h retention. Only Anthropic reports this split.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cache_write_1h: Option<u64>,
    /// Reasoning/thinking tokens, when the provider reports them. A subset of
    /// `output`: `output` already includes these tokens. Set (possibly to 0) by
    /// providers that expose a reasoning breakdown; `None` otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reasoning: Option<u64>,
    pub total_tokens: u64,
    pub cost: UsageCost,
}

string_enum! {
    /// Why an assistant response stopped.
    pub enum StopReason {
        Pending => "pending",
        Stop => "stop",
        Length => "length",
        ToolUse => "toolUse",
        Error => "error",
        Aborted => "aborted",
        Deferred => "deferred",
    }
}

string_enum! {
    /// TS `Extract<StopReason, "stop" | "length" | "toolUse" | "deferred">`: the reason of a `done` event.
    pub enum DoneReason {
        Stop => "stop",
        Length => "length",
        ToolUse => "toolUse",
        Deferred => "deferred",
    }
}

string_enum! {
    /// TS `Extract<StopReason, "aborted" | "error">`: the reason of an `error` event.
    pub enum ErrorReason {
        Aborted => "aborted",
        Error => "error",
    }
}

impl From<DoneReason> for StopReason {
    fn from(reason: DoneReason) -> Self {
        match reason {
            DoneReason::Stop => Self::Stop,
            DoneReason::Length => Self::Length,
            DoneReason::ToolUse => Self::ToolUse,
            DoneReason::Deferred => Self::Deferred,
        }
    }
}

impl From<ErrorReason> for StopReason {
    fn from(reason: ErrorReason) -> Self {
        match reason {
            ErrorReason::Aborted => Self::Aborted,
            ErrorReason::Error => Self::Error,
        }
    }
}
