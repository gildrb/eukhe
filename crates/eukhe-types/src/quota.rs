//! Plan quota readings: how much of each window of a subscription plan the
//! account has used, as the provider last reported it.

use serde::{Deserialize, Serialize};

/// One window of a plan quota.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct QuotaWindow {
    /// The window's name: "5h", "7d", "7d opus", "month premium", ...
    pub label: String,
    /// The window's length, when the provider states a fixed one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub window_minutes: Option<u64>,
    /// Used share of the window in permille (1000 = all used; over 1000
    /// when the provider reports overage).
    pub used_permille: u32,
    /// When the window resets, epoch milliseconds.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub resets_at_ms: Option<u64>,
}

/// Where a reading came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum QuotaSource {
    /// Rate-limit headers of a model response.
    Headers,
    /// A rate-limit frame of a model response stream.
    StreamFrame,
    /// The provider's plan usage endpoint.
    UsageEndpoint,
}

/// One reading of a provider's plan quota.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PlanQuota {
    /// Provider id ("anthropic", "openai-codex", "github-copilot").
    pub provider: String,
    /// The plan's name, when the provider names it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub plan: Option<String>,
    /// The windows, in the provider's order.
    pub windows: Vec<QuotaWindow>,
    /// When the reading was taken, epoch milliseconds.
    pub read_at_ms: u64,
    pub source: QuotaSource,
}
