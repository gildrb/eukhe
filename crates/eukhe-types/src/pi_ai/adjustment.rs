//! Request adjustments: what a codec changed in the caller's request because
//! the model, its host, or its limits do not take it as asked. Every drop or
//! clamp is recorded on the response ([`super::AssistantMessage::adjustments`])
//! instead of happening silently.

use serde::{Deserialize, Serialize};

use super::string_enum::string_enum;

string_enum! {
    /// The request field an adjustment touched.
    pub enum AdjustedField {
        /// The requested service tier.
        ServiceTier => "serviceTier",
        /// The output-token cap.
        MaxTokens => "maxTokens",
        /// The thinking token budget.
        ThinkingBudget => "thinkingBudget",
        /// The sampling temperature.
        Temperature => "temperature",
        /// The requested reasoning effort.
        ReasoningEffort => "reasoningEffort",
        /// A tool's JSON-schema constrained sampling (`strict`).
        StrictTool => "strictTool",
        /// Claude's thinking `display` mode.
        ThinkingDisplay => "thinkingDisplay",
        /// Claude's thinking `block_binding` control.
        ThinkingBlockBinding => "thinkingBlockBinding",
    }
}

string_enum! {
    /// Why the request changed.
    pub enum AdjustmentReason {
        /// The model's compat facts say the host does not take the field.
        UnsupportedByModel => "unsupportedByModel",
        /// A Sign in with `ChatGPT` credential rejects the field.
        ChatGptSignIn => "chatGptSignIn",
        /// `GovCloud` Bedrock rejects the field.
        GovCloudRegion => "govCloudRegion",
        /// The value did not fit the model's context window.
        ContextWindow => "contextWindow",
        /// The value did not fit the output-token cap.
        MaxTokens => "maxTokens",
        /// The tool's parameter schema cannot be made strict.
        UnsupportedSchema => "unsupportedSchema",
        /// The value was below the smallest value the host accepts.
        BelowMinimum => "belowMinimum",
        /// The host rejects the field while thinking is on.
        ThinkingEnabled => "thinkingEnabled",
    }
}

/// What happened to the field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "change", rename_all = "camelCase")]
pub enum AdjustmentChange {
    /// The field was not sent.
    Dropped,
    /// The field was sent with a smaller or larger value than requested.
    Clamped { requested: u64, sent: u64 },
}

/// One change a codec made to the caller's request.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RequestAdjustment {
    pub field: AdjustedField,
    #[serde(flatten)]
    pub change: AdjustmentChange,
    pub reason: AdjustmentReason,
    /// What the field belongs to when the request has several (a tool name).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub subject: Option<String>,
}

impl RequestAdjustment {
    /// `field` was not sent because of `reason`.
    #[must_use]
    pub const fn dropped(field: AdjustedField, reason: AdjustmentReason) -> Self {
        Self {
            field,
            change: AdjustmentChange::Dropped,
            reason,
            subject: None,
        }
    }

    /// `field` was sent as `sent` instead of `requested` because of `reason`.
    #[must_use]
    pub const fn clamped(
        field: AdjustedField,
        requested: u64,
        sent: u64,
        reason: AdjustmentReason,
    ) -> Self {
        Self {
            field,
            change: AdjustmentChange::Clamped { requested, sent },
            reason,
            subject: None,
        }
    }

    /// The same adjustment, scoped to `subject` (a tool name).
    #[must_use]
    pub fn for_subject(mut self, subject: impl Into<String>) -> Self {
        self.subject = Some(subject.into());
        self
    }
}
