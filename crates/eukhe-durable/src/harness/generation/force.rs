//! A forced tool call (`bend/infer.bend` §2, `force`). Every request of a
//! generation that forces a tool carries the soft prompt naming it
//! ([`soft_prompt`]). The first request also sets the provider's native
//! forced choice only when the provider supports it and setting it is free
//! (no prompt-cache cost); each retry sets it whenever the provider supports
//! it. A reply without the call is retried while retries remain; after them
//! the generation fails with [`ForcedToolError::NotCalled`]. A forced call
//! makes at most `1 + retries` requests (laws `force_bounded`,
//! `force_first_flag`, `force_retry_flag`, `force_reports`).

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

/// A reply to a request of a forced call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ForceReply {
    /// The reply called the forced tool.
    Called,
    /// The reply went without the call.
    Missed,
}

/// What follows a reply to a forced call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ForceStep {
    /// The model called the tool: the reply goes on as any other.
    Called,
    /// The reply went without the call and a retry remains.
    Retry,
    /// The last request went without the call: the generation fails.
    Failed,
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

impl ForceEscalation {
    /// Whether request `attempt` (counted from 1) sets the native flag.
    pub(crate) const fn flag(self, attempt: u32) -> bool {
        if attempt <= 1 {
            self.native && self.free
        } else {
            self.native
        }
    }

    /// The step after `reply`, the reply to request `attempt` (counted
    /// from 1).
    pub(crate) const fn after(self, attempt: u32, reply: ForceReply) -> ForceStep {
        match reply {
            ForceReply::Called => ForceStep::Called,
            ForceReply::Missed if attempt <= self.retries => ForceStep::Retry,
            ForceReply::Missed => ForceStep::Failed,
        }
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

    use super::{ForceEscalation, ForceReply, ForceStep, Forcing};
    use crate::harness::types::ForcedTool;

    use ForceReply::{Called, Missed};

    /// The model's outcome of a forced call (`Forced`).
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Forced {
        Called,
        Missed,
    }

    /// The requests' flags and the outcome of a forced call whose replies
    /// are `replies`, as the harness drives the unit; a missing reply
    /// counts as no call and ends it.
    fn drive(escalation: ForceEscalation, replies: &[ForceReply]) -> (Vec<bool>, Forced) {
        let mut flags = Vec::new();
        let mut attempt = 1;
        loop {
            flags.push(escalation.flag(attempt));
            let Some(&reply) = replies.get(attempt as usize - 1) else {
                return (flags, Forced::Missed);
            };
            match escalation.after(attempt, reply) {
                ForceStep::Called => return (flags, Forced::Called),
                ForceStep::Retry => attempt += 1,
                ForceStep::Failed => return (flags, Forced::Missed),
            }
        }
    }

    #[test]
    fn retries_escalate_to_the_native_flag_until_the_call() {
        let escalation = ForceEscalation {
            retries: 2,
            native: true,
            free: false,
        };
        assert_eq!(
            drive(escalation, &[Missed, Missed, Called]),
            (vec![false, true, true], Forced::Called)
        );
    }

    #[test]
    fn a_free_native_flag_is_set_from_the_first_request() {
        let escalation = ForceEscalation {
            retries: 1,
            native: true,
            free: true,
        };
        assert_eq!(
            drive(escalation, &[Missed, Missed]),
            (vec![true, true], Forced::Missed)
        );
    }

    #[test]
    fn without_native_support_only_the_soft_prompt_asks() {
        let escalation = ForceEscalation {
            retries: 3,
            native: false,
            free: true,
        };
        assert_eq!(
            drive(escalation, &[Missed, Called]),
            (vec![false, false], Forced::Called)
        );
    }

    #[test]
    fn no_retries_fail_on_the_first_miss() {
        let escalation = ForceEscalation {
            retries: 0,
            native: true,
            free: false,
        };
        assert_eq!(
            drive(escalation, &[Missed, Called]),
            (vec![false], Forced::Missed)
        );
    }

    #[test]
    fn a_missing_reply_ends_the_call_unanswered() {
        let escalation = ForceEscalation {
            retries: 2,
            native: true,
            free: true,
        };
        assert_eq!(drive(escalation, &[]), (vec![true], Forced::Missed));
    }

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

    /// Every reply list up to five long, as bits of `bits`.
    fn reply_lists() -> Vec<Vec<ForceReply>> {
        (0..=5usize)
            .flat_map(|len| {
                (0..1u32 << len).map(move |bits| {
                    (0..len)
                        .map(|i| if (bits >> i) & 1 == 1 { Called } else { Missed })
                        .collect()
                })
            })
            .collect()
    }

    /// The laws of `force` (`laws/infer.bend` S6, model
    /// `bend/infer.bend`) over small inputs.
    #[test]
    fn the_force_laws_hold() {
        for retries in 0..4u32 {
            for native in [false, true] {
                for free in [false, true] {
                    for replies in reply_lists() {
                        let escalation = ForceEscalation {
                            retries,
                            native,
                            free,
                        };
                        let (flags, outcome) = drive(escalation, &replies);
                        let within = replies
                            .iter()
                            .take(1 + retries as usize)
                            .any(|&reply| reply == Called);
                        let mut expected = vec![native && free];
                        expected.extend(vec![native; flags.len() - 1]);
                        assert_eq!(
                            (
                                flags.len() <= 1 + retries as usize,
                                flags,
                                outcome == Forced::Called,
                            ),
                            (true, expected, within),
                            "retries {retries}, native {native}, free {free}, replies {replies:?}"
                        );
                    }
                }
            }
        }
    }
}
