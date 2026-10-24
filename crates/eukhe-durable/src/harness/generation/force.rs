//! A forced tool call (`bend/infer.bend` §2, `force`). Every request of a
//! generation that forces a tool carries the soft prompt naming it
//! ([`soft_prompt`]). The first request also sets the provider's native
//! forced choice only when the provider supports it and setting it is free
//! (no prompt-cache cost); each retry sets it whenever the provider supports
//! it. A reply without the call is retried while retries remain; after them
//! the generation fails with [`ForcedToolError::NotCalled`]. A forced call
//! makes at most `1 + retries` requests (laws `force_bounded`,
//! `force_first_flag`, `force_retry_flag`, `force_reports`). Each step runs
//! as the compiled core (`eukhe_bend::rules::infer_force`, law
//! `infer_force_steps`): the harness only counts the requests it made.

use eukhe_ai::api::simple_options::maps_forced_tool_choice;
use eukhe_ai::quirks::Quirks;
use eukhe_ai::types::{Model, ThinkingLevel};
use serde::{Deserialize, Serialize};

use crate::harness::types::ForcedTool;

/// The forced call of one request: the option and its escalation on the
/// request's model. A poll pins it with the request it polls for.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Forcing {
    pub(crate) forced: ForcedTool,
    pub(crate) escalation: ForceEscalation,
}

/// The escalation of one forced call: its retries and what the provider
/// offers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ForceEscalation {
    /// Requests after the first that may still make the call.
    pub(crate) retries: u32,
    /// The provider has a native forced tool choice (model `sup`).
    pub(crate) native: bool,
    /// Setting it costs no prompt-cache invalidation (model `free`).
    pub(crate) free: bool,
}

/// Why a forced call failed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, thiserror::Error)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum ForcedToolError {
    /// No reply of the `attempts` requests called `tool`.
    #[error("The model did not call the forced tool {tool} in {attempts} requests")]
    NotCalled { tool: String, attempts: u32 },
}

impl Forcing {
    /// The forced call `forced` on `model` for a request with `reasoning`:
    /// native support where the request's wire form sends a native forced
    /// choice ([`maps_forced_tool_choice`]: not under Anthropic's manual
    /// extended thinking, for one) and the quirks rulebook does not deny it;
    /// a cost the rulebook does not know counts as not free.
    pub(crate) fn of(forced: ForcedTool, model: &Model, reasoning: Option<ThinkingLevel>) -> Self {
        let quirks = Quirks::of(model);
        let escalation = ForceEscalation {
            retries: forced.retries,
            native: maps_forced_tool_choice(model, reasoning)
                && quirks.tool_choice_native() != Some(false),
            free: quirks.tool_choice_free().unwrap_or(false),
        };
        Self { forced, escalation }
    }
}

/// The instruction every request of a forced call ends with, as a user
/// message.
pub(crate) fn soft_prompt(tool: &str) -> String {
    format!("Call the `{tool}` tool now: your reply must include a call to `{tool}`.")
}

#[cfg(test)]
mod tests {
    use eukhe_ai::types::{Model, ThinkingLevel};
    use serde_json::json;

    use super::{ForceEscalation, Forcing};
    use crate::harness::types::ForcedTool;

    /// A request under Anthropic's manual extended thinking sends no forced
    /// choice, so its escalation has no native flag to escalate to; the
    /// same model without thinking has one.
    #[test]
    fn manual_extended_thinking_has_no_native_forced_choice() {
        let model: Model = serde_json::from_value(json!({
            "id": "claude-sonnet-4-5",
            "name": "Claude Sonnet 4.5",
            "api": "anthropic-messages",
            "provider": "anthropic",
            "baseUrl": "https://api.anthropic.com",
            "reasoning": true,
            "input": ["text"],
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
            "contextWindow": 200_000,
            "maxTokens": 64_000,
        }))
        .unwrap();
        let forced = ForcedTool {
            tool: "lookup".to_owned(),
            retries: 2,
        };
        let without = ForceEscalation {
            retries: 2,
            native: false,
            free: false,
        };
        assert_eq!(
            (
                Forcing::of(forced.clone(), &model, Some(ThinkingLevel::High)),
                Forcing::of(forced.clone(), &model, None),
            ),
            (
                Forcing {
                    forced: forced.clone(),
                    escalation: without,
                },
                Forcing {
                    forced,
                    escalation: ForceEscalation {
                        native: true,
                        ..without
                    },
                },
            )
        );
    }
}
