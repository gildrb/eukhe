//! Thread goals: state model, validation, host-response serialization, and
//! the goal-context messages. Port of core/goals.ts; the prompt texts, the
//! tokens left and the completion report are the compiled core's
//! (`eukhe_bend::rules::goal_text`).

use eukhe_bend::rules::goal_text;
use serde::{Deserialize, Serialize};

/// Custom message type persisting the goal state in the session JSONL.
pub const GOAL_STATE_CUSTOM_TYPE: &str = "thread_goal_state";
/// Custom message type for goal continuation prompts.
pub const GOAL_CONTEXT_CUSTOM_TYPE: &str = "goal_context";

// The wire/persisted `GoalState` and `GoalStatus` vocabulary lives in
// eukhe-types (shared with the attached surfaces); this module owns the goal
// engine: validation, accounting, host responses, and continuation
// prompts. The slug (`"budget_limited"`) is `GoalStatus::slug`.
pub use eukhe_types::goal::{empty_goal_state, GoalContextKind, GoalState, GoalStatus};

/// Goal payload returned to the kernel-side goal skill (`snake_case`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub struct SerializedGoal {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub goal_id: Option<String>,
    pub objective: String,
    pub status: GoalStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub token_budget: Option<u64>,
    pub tokens_used: u64,
    pub time_used_seconds: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub created_at: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub updated_at: Option<u64>,
}

/// Reply payload for goal.* host requests from the Python kernel.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub struct GoalHostResponse {
    pub goal: Option<SerializedGoal>,
    pub remaining_tokens: Option<u64>,
    pub completion_budget_report: Option<String>,
}

/// Details persisted on goal-context messages.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GoalContextDetails {
    pub kind: GoalContextKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub goal_id: Option<String>,
    pub objective: String,
    pub status: GoalStatus,
    #[serde(rename = "continuationsUsed")]
    pub continuations_used: u64,
}

/// The goal-update dedupe's age-invariant projection: the creation-based
/// timer recomputes `time_used_seconds` from the wall clock on every read
/// (the operator's ruling), so the age must not participate in an
/// "unchanged state" comparison — an unchanged goal would otherwise
/// re-emit `goal_update` every time a second boundary passes between two
/// reads. Emit the real state; dedupe on this projection.
#[must_use]
pub fn goal_update_dedupe_projection(state: &GoalState) -> GoalState {
    let mut projected = state.clone();
    projected.time_used_seconds = 0;
    projected
}

/// Clamp counters and derive `active` from the status. Backfills
/// `created_at` for goals persisted before the creation-based timer
/// contract (operator ruling 2026-09-28): a goal without `created_at`
/// adopts its `updated_at` as the creation time, so rows persisted
/// before the contract read a sane age instead of no age. The empty
/// state (no goal id, no objective) never fabricates a creation time.
#[must_use]
pub fn normalize_goal_state(goal: GoalState) -> GoalState {
    let created_at = match goal.created_at {
        Some(created_at) => Some(created_at),
        None => (goal.goal_id.is_some() || goal.objective.is_some())
            .then_some(goal.updated_at)
            .flatten(),
    };
    GoalState {
        active: goal.status == GoalStatus::Active,
        tokens_used: goal.tokens_used,
        time_used_seconds: goal.time_used_seconds,
        continuations_used: goal.continuations_used,
        created_at,
        ..goal
    }
}

/// Validate and normalize a goal objective: the compiled core's verdict
/// (`eukhe_bend::rules::slash_args::objective`, `laws/slash_args`).
///
/// # Errors
///
/// Returns an error when the objective is empty after trimming or longer
/// than the objective character limit (4000 chars).
pub fn validate_goal_objective(value: &str) -> anyhow::Result<String> {
    eukhe_bend::rules::slash_args::objective(value).map_err(anyhow::Error::msg)
}

/// Validate a goal token budget.
///
/// # Errors
///
/// Returns an error when the budget is present and zero.
pub fn validate_goal_budget(value: Option<u64>) -> anyhow::Result<Option<u64>> {
    if value == Some(0) {
        return Err(anyhow::anyhow!(
            "Goal token budget must be a positive integer."
        ));
    }
    Ok(value)
}

/// Token accounting delta for one usage event.
#[must_use]
pub fn goal_token_delta_for_usage(input: i64, output: i64) -> u64 {
    input.max(0) as u64 + output.max(0) as u64
}

/// The restore-resurrection guard (the 402 diagnosis's (d)): the newest
/// `thread_goal_state` row is `active`, but a provider failure (an
/// assistant row with stop reason `error`, not the quota-park class)
/// settled AFTER it. The failed turn's terminal goal finish never
/// persisted — a worker death or restart interrupted the settle — so a
/// naive rehydration would resurrect the goal and the resume sites
/// would keep delivering continuations into the dead provider (the
/// operator's ~84s restart cadence, 64 cycles in 1.5h). Returns the
/// failure's error text for the caller to adopt as the goal's terminal
/// state.
///
/// Newest-first over `entries` (file order): the newest goal row
/// decides. Entries newer than it hold at most one candidate — their
/// newest assistant row; a terminal provider failure there marks the
/// stale active row. A slice with no goal row scans only the newest
/// assistant row (the windowed-retained case: the goal row lives before
/// the window, so every retained row is newer than it — the caller
/// gates on the adopted state being `active`).
pub fn stale_active_goal_failure(entries: &[eukhe_types::session::FileEntry]) -> Option<String> {
    let mut newest_assistant: Option<&eukhe_types::ai::AssistantMessage> = None;
    for entry in entries.iter().rev() {
        match entry {
            eukhe_types::session::FileEntry::Custom { payload, .. }
                if payload.custom_type == GOAL_STATE_CUSTOM_TYPE =>
            {
                let Some(data) = payload.data.as_ref() else {
                    continue;
                };
                if !is_persisted_goal_state(data) {
                    continue;
                }
                let Ok(state) = serde_json::from_value::<GoalState>(data.clone()) else {
                    continue;
                };
                if state.status != GoalStatus::Active {
                    return None;
                }
                return newest_assistant.and_then(wire_terminal_provider_failure);
            }
            eukhe_types::session::FileEntry::Message {
                message: eukhe_types::session::AgentMessage::Assistant(assistant),
                ..
            } if newest_assistant.is_none() => {
                newest_assistant = Some(assistant);
            }
            _ => {}
        }
    }
    // No goal row in the scanned slice: every scanned entry is newer
    // than the goal row the caller adopted.
    newest_assistant.and_then(wire_terminal_provider_failure)
}

/// The wire form of the session engine's terminal-provider-failure
/// predicate (over a session entry's eukhe-types assistant row): the
/// recorded provider failure text when the row settled as a terminal
/// provider failure. The quota-park class (`rate_limit`) keeps the goal —
/// the parked turn is the park's pause, not the goal's death.
fn wire_terminal_provider_failure(message: &eukhe_types::ai::AssistantMessage) -> Option<String> {
    if message.stop_reason != eukhe_types::ai::StopReason::Error {
        return None;
    }
    // The diagnostic is consulted ONLY to exclude the quota-park class —
    // an error-stop row WITHOUT a provider diagnostic is still terminal
    // (the same predicate the live mint's `terminal_provider_failure`
    // applies: one semantic, two shapes; a diagnostic-less restore must
    // not resurrect a goal the engine itself would have finished).
    let kind = message.diagnostics.as_ref().and_then(|diagnostics| {
        diagnostics
            .iter()
            .find(|diagnostic| diagnostic.type_ == "provider_stream_failure")
            .and_then(|diagnostic| diagnostic.details.as_ref())
            .and_then(|details| details.get("kind"))
            .and_then(serde_json::Value::as_str)
    });
    if kind == Some("rate_limit") {
        return None;
    }
    Some(
        message
            .error_message
            .clone()
            .filter(|error| !error.is_empty())
            .unwrap_or_else(|| "Assistant response failed".to_string()),
    )
}

/// Whether a JSON value round-trips as a well-formed persisted goal state.
pub fn is_persisted_goal_state(value: &serde_json::Value) -> bool {
    let Ok(record) =
        serde_json::from_value::<serde_json::Map<String, serde_json::Value>>(value.clone())
    else {
        return false;
    };
    if !record
        .get("active")
        .is_some_and(serde_json::Value::is_boolean)
    {
        return false;
    }
    let status_ok = matches!(
        record.get("status").and_then(|value| value.as_str()),
        Some("idle" | "active" | "paused" | "budget_limited" | "complete" | "error")
    );
    if !status_ok {
        return false;
    }
    ["tokensUsed", "timeUsedSeconds", "continuationsUsed"]
        .iter()
        .all(|key| {
            record
                .get(*key)
                .is_some_and(|value| value.as_f64().is_some())
        })
}

/// What a goal tool call answers: the goal (none when idle or without an
/// objective), the tokens left and, when `include_completion_report` and
/// the goal is complete, the completion budget report. The texts and the
/// tokens left are the compiled core's (`eukhe_bend::rules::goal_text`,
/// `laws/goal_text.bend`).
#[must_use]
pub fn goal_host_response(goal: &GoalState, include_completion_report: bool) -> GoalHostResponse {
    let report = if include_completion_report {
        goal_text::Report::Asked
    } else {
        goal_text::Report::NotAsked
    };
    let (Some(answer), Some(objective)) = (goal_text::host(goal, report), &goal.objective) else {
        return GoalHostResponse {
            goal: None,
            remaining_tokens: None,
            completion_budget_report: None,
        };
    };
    GoalHostResponse {
        goal: Some(SerializedGoal {
            goal_id: goal.goal_id.clone(),
            objective: objective.clone(),
            status: goal.status,
            token_budget: goal.token_budget,
            tokens_used: goal.tokens_used,
            time_used_seconds: goal.time_used_seconds,
            created_at: goal.created_at,
            updated_at: goal.updated_at,
        }),
        remaining_tokens: answer.remaining_tokens,
        completion_budget_report: answer.completion_budget_report,
    }
}

/// The goal continuation/budget/objective message (custom type, display=true).
///
/// # Errors
///
/// Returns an error when the goal has no objective, or when the goal context
/// details cannot be serialized.
pub fn create_goal_context_message(
    goal: &GoalState,
    kind: GoalContextKind,
) -> anyhow::Result<eukhe_types::session::CustomMessage> {
    let Some(objective) = &goal.objective else {
        anyhow::bail!("Cannot create goal context without an objective.");
    };
    let prompt = goal_text::prompt(goal, kind);
    let text = format!("[goal: {}]\n\n{prompt}", kind.label());
    Ok(eukhe_types::session::CustomMessage {
        custom_type: GOAL_CONTEXT_CUSTOM_TYPE.to_string(),
        content: eukhe_types::ai::UserContent::Text(text),
        display: true,
        details: Some(serde_json::to_value(GoalContextDetails {
            kind,
            goal_id: goal.goal_id.clone(),
            objective: objective.clone(),
            status: goal.status,
            continuations_used: goal.continuations_used,
        })?),
        timestamp: now_millis(),
        rest: serde_json::Map::default(),
    })
}

fn now_millis() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_millis() as u64)
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::ai::UserContent;

    fn active_goal() -> GoalState {
        GoalState {
            active: true,
            status: GoalStatus::Active,
            goal_id: Some("g1".to_string()),
            objective: Some("ship the feature".to_string()),
            token_budget: Some(1000),
            tokens_used: 400,
            time_used_seconds: 120,
            continuations_used: 3,
            created_at: Some(1),
            updated_at: Some(2),
            last_reason: None,
            last_error: None,
        }
    }

    #[test]
    fn normalize_derives_active_from_status() {
        let mut goal = active_goal();
        goal.status = GoalStatus::Paused;
        goal.active = true;
        let normalized = normalize_goal_state(goal);
        assert!(!normalized.active);
        assert_eq!(normalized.status, GoalStatus::Paused);
    }

    #[test]
    fn objective_and_budget_validation() {
        // The objective reaches the compiled core at full size: 4000 chars
        // pass, 4001 do not.
        let at_limit = "x".repeat(4000);
        assert_eq!(validate_goal_objective(&at_limit).unwrap(), at_limit);
        assert_eq!(
            validate_goal_objective(&"x".repeat(4001))
                .unwrap_err()
                .to_string(),
            "Goal objective must be at most 4000 characters."
        );
        assert!(validate_goal_budget(None).unwrap().is_none());
        assert_eq!(validate_goal_budget(Some(10)).unwrap(), Some(10));
        assert!(validate_goal_budget(Some(0)).is_err());
    }

    #[test]
    fn usage_delta_clamps_negatives() {
        assert_eq!(goal_token_delta_for_usage(10, 20), 30);
        assert_eq!(goal_token_delta_for_usage(-5, 20), 20);
        assert_eq!(goal_token_delta_for_usage(-5, -20), 0);
    }

    #[test]
    fn persisted_state_guard() {
        let goal = active_goal();
        let value = serde_json::to_value(&goal).unwrap();
        assert!(is_persisted_goal_state(&value));
        assert!(!is_persisted_goal_state(&serde_json::json!({})));
        assert!(!is_persisted_goal_state(&serde_json::json!({
            "active": true, "status": "nonsense",
            "tokensUsed": 0, "timeUsedSeconds": 0, "continuationsUsed": 0
        })));
        assert!(!is_persisted_goal_state(&serde_json::json!({
            "active": true, "status": "active", "tokensUsed": "many"
        })));
    }

    #[test]
    fn host_response_shapes() {
        let goal = active_goal();
        let response = goal_host_response(&goal, false);
        let serialized = response.goal.unwrap();
        assert_eq!(serialized.goal_id.as_deref(), Some("g1"));
        assert_eq!(serialized.status, GoalStatus::Active);
        assert_eq!(response.remaining_tokens, Some(600));
        assert_eq!(response.completion_budget_report, None);
        // Completion report only for complete goals on request.
        let mut done = goal;
        done.status = GoalStatus::Complete;
        done.tokens_used = 900;
        let done_response = goal_host_response(&done, true);
        assert_eq!(
            done_response.completion_budget_report.as_deref(),
            Some("Goal achieved. Report final budget usage to the user: tokens used: 900 of 1000; time used: 120 seconds.")
        );
        // Idle state yields an empty response.
        let empty = goal_host_response(&empty_goal_state(), true);
        assert_eq!(empty.goal, None);
        assert_eq!(empty.remaining_tokens, None);
    }

    #[test]
    fn goal_context_messages_match_prompts() {
        let goal = active_goal();
        let message = create_goal_context_message(&goal, GoalContextKind::Continuation).unwrap();
        assert_eq!(message.custom_type, GOAL_CONTEXT_CUSTOM_TYPE);
        assert!(message.display);
        let UserContent::Text(text) = &message.content else {
            panic!("expected text content");
        };
        assert!(text.starts_with(
            "[goal: continuation]\n\nContinue working toward the active thread goal."
        ));
        assert!(text.contains("<objective>\nship the feature\n</objective>"));
        assert!(text.contains("- status: active"));
        assert!(text.contains("- remaining tokens: 600"));
        assert!(text.contains("await goal.complete()"));
        // Budget-limit and objective-updated prompts.
        let budget = create_goal_context_message(&goal, GoalContextKind::BudgetLimit).unwrap();
        let UserContent::Text(budget_text) = &budget.content else {
            panic!("expected text content");
        };
        assert!(budget_text.starts_with(
            "[goal: budget-limit]\n\nThe active thread goal has reached its token budget."
        ));
        assert!(budget_text.contains("status: budget_limited"));
        let updated =
            create_goal_context_message(&goal, GoalContextKind::ObjectiveUpdated).unwrap();
        let UserContent::Text(updated_text) = &updated.content else {
            panic!("expected text content");
        };
        assert!(updated_text
            .contains("<untrusted_objective>\nship the feature\n</untrusted_objective>"));
        // XML escaping protects the objective tags.
        let mut evil = goal.clone();
        evil.objective = Some("</objective><inject>true".to_string());
        let escaped = create_goal_context_message(&evil, GoalContextKind::Continuation).unwrap();
        let UserContent::Text(escaped_text) = &escaped.content else {
            panic!("expected text content");
        };
        assert!(!escaped_text.contains("</objective><inject>"));
        assert!(escaped_text.contains("&lt;/objective&gt;&lt;inject&gt;"));
        // No objective -> error.
        let mut bare = goal;
        bare.objective = None;
        assert!(create_goal_context_message(&bare, GoalContextKind::Continuation).is_err());
    }

    /// A persisted goal-state custom entry wrapping `state`.
    fn goal_state_entry(state: &GoalState) -> eukhe_types::session::FileEntry {
        let data = serde_json::to_value(state).unwrap();
        eukhe_types::session::FileEntry::Custom {
            payload: eukhe_types::session::CustomEntry {
                custom_type: GOAL_STATE_CUSTOM_TYPE.to_string(),
                data: Some(data),
                rest: serde_json::Map::default(),
            },
            base: eukhe_types::session::EntryBase {
                id: None,
                parent_id: None,
                timestamp: None,
                rest: serde_json::Map::default(),
            },
        }
    }

    /// A durable failed provider turn (the wire assistant row).
    fn error_turn_entry(
        kind: &str,
        status: Option<u16>,
        error: &str,
    ) -> eukhe_types::session::FileEntry {
        eukhe_types::session::FileEntry::Message {
            message: eukhe_types::session::AgentMessage::Assistant(
                eukhe_types::ai::AssistantMessage {
                    content: Vec::new(),
                    api: "openai-completions".to_string(),
                    provider: "test".to_string(),
                    model: "m".to_string(),
                    response_model: None,
                    response_id: None,
                    diagnostics: Some(vec![eukhe_types::ai::AssistantMessageDiagnostic {
                        type_: "provider_stream_failure".to_string(),
                        timestamp: 0,
                        error: None,
                        details: Some(
                            serde_json::json!({
                                "kind": kind,
                                "status": status,
                            })
                            .as_object()
                            .cloned()
                            .unwrap_or_default(),
                        ),
                    }]),
                    usage: eukhe_types::ai::Usage::default(),
                    stop_reason: eukhe_types::ai::StopReason::Error,
                    stop_reason_raw: None,
                    error_message: Some(error.to_string()),
                    timestamp: 0,
                    timing: None,
                    rest: serde_json::Map::default(),
                },
            ),
            base: eukhe_types::session::EntryBase {
                id: None,
                parent_id: None,
                timestamp: None,
                rest: serde_json::Map::default(),
            },
        }
    }

    /// The restore-resurrection scan (the 402 diagnosis's (d)): the newest
    /// active goal row with a terminal provider failure settled after it.
    #[test]
    fn stale_active_goal_failure_scan() {
        let active = goal_state_entry(&active_goal());
        let mut finished = active_goal();
        finished.status = GoalStatus::Error;
        finished.active = false;
        let finished = goal_state_entry(&finished);
        let failure = error_turn_entry("invalid_request", Some(402), "402 Insufficient balance");
        let rate_limited =
            error_turn_entry("rate_limit", Some(429), "429 Too many concurrent requests");

        // The interrupted settle: the active mint row, then the corpse.
        // Stale -> the failure's text.
        assert_eq!(
            stale_active_goal_failure(&[active.clone(), failure.clone()]),
            Some("402 Insufficient balance".to_string())
        );
        // A corpse with no error text still names the failure.
        // The quota-park class keeps the goal: not stale.
        assert_eq!(
            stale_active_goal_failure(&[active.clone(), rate_limited]),
            None
        );
        // A healthy turn after the mint: not stale.
        let healthy = eukhe_types::session::FileEntry::Message {
            message: eukhe_types::session::AgentMessage::Assistant(
                eukhe_types::ai::AssistantMessage {
                    content: vec![eukhe_types::ai::AssistantContentBlock::Text(
                        eukhe_types::ai::TextContent {
                            text: "progress".to_string(),
                            text_signature: None,
                            rest: serde_json::Map::default(),
                            cache_breakpoint: None,
                        },
                    )],
                    api: "openai-completions".to_string(),
                    provider: "test".to_string(),
                    model: "m".to_string(),
                    response_model: None,
                    response_id: None,
                    diagnostics: None,
                    usage: eukhe_types::ai::Usage::default(),
                    stop_reason: eukhe_types::ai::StopReason::Stop,
                    stop_reason_raw: None,
                    error_message: None,
                    timestamp: 0,
                    timing: None,
                    rest: serde_json::Map::default(),
                },
            ),
            base: eukhe_types::session::EntryBase {
                id: None,
                parent_id: None,
                timestamp: None,
                rest: serde_json::Map::default(),
            },
        };
        assert_eq!(stale_active_goal_failure(&[active.clone(), healthy]), None);
        // The settle completed: the error row is the newest goal row —
        // nothing to resurrect, not stale (the terminal row stands).
        assert_eq!(
            stale_active_goal_failure(&[active.clone(), failure.clone(), finished.clone()]),
            None
        );
        // The goal restarted after the failure: the active row is NEWER
        // than the old corpse — not stale.
        assert_eq!(stale_active_goal_failure(&[failure, active.clone()]), None);
        // A diagnostic-less error row is STILL terminal (the aligned
        // predicate: the diagnostic only excludes the quota-park class —
        // a restore must not resurrect a goal the engine itself would
        // have finished).
        let mut bare_failure = error_turn_entry("invalid_request", Some(402), "402 no diagnostic");
        if let eukhe_types::session::FileEntry::Message {
            message: eukhe_types::session::AgentMessage::Assistant(assistant),
            ..
        } = &mut bare_failure
        {
            assistant.diagnostics = None;
        }
        assert_eq!(
            stale_active_goal_failure(&[active, bare_failure]),
            Some("402 no diagnostic".to_string())
        );
        // A goal row that is the newest entry overall: no failure after
        // it — not stale.
        assert_eq!(stale_active_goal_failure(&[finished]), None);
    }
}
