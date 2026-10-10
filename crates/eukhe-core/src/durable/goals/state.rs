//! Goal-state transitions: the durable port of the old goal driver's
//! lifecycle (`session_engine/goal_driver.rs` and its `progress` child) as
//! pure functions over [`GoalState`]. The callers read the `eukhe.goal`
//! document inside a commit, apply one transition, and write the result back
//! in the same commit, so every transition is one atomic read-modify-write.
//!
//! Every write goes through [`stamp`] (the old `set_state` normalization:
//! `updated_at`, the derived `active` flag, and the creation-based timer).

use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, StopReason, Usage};

use crate::goals::{
    normalize_goal_state, validate_goal_budget, validate_goal_objective, GoalState, GoalStatus,
};

/// How many consecutive no-output turns the continuation mint tolerates
/// before the goal finishes (the 402 diagnosis's small cap).
pub(crate) const CONTINUATION_NO_PROGRESS_CAP: u32 = 3;

/// The backoff base for consecutive no-output turns (10s, 20s, 40s ...).
pub(crate) const CONTINUATION_NO_PROGRESS_BACKOFF_BASE_MS: u64 = 10_000;

/// The terminal reason of a goal whose continuations stopped making progress.
pub const NO_PROGRESS_CAP_REASON: &str =
    "Goal continuation cap reached: consecutive turns made no progress";

/// The default reason of a failed assistant response.
const ASSISTANT_FAILED: &str = "Assistant response failed";

/// The goal timer (operator ruling 2026-09-28): `time_used_seconds` is the
/// goal's age, the wall clock since `created_at`.
#[must_use]
pub fn creation_elapsed_seconds(created_at: Option<u64>, now: u64) -> u64 {
    created_at.map_or(0, |created| now.saturating_sub(created) / 1000)
}

/// The served goal state: `time_used_seconds` reads the goal's age fresh.
/// A state without `created_at` keeps its last persisted value.
#[must_use]
pub fn served(state: &GoalState, now: u64) -> GoalState {
    match state.created_at {
        Some(created_at) => GoalState {
            time_used_seconds: creation_elapsed_seconds(Some(created_at), now),
            ..state.clone()
        },
        None => state.clone(),
    }
}

/// The written form of `next` (old `GoalDriver::set_state`): stamped
/// `updated_at`, normalized, and carrying the goal's age at the write.
#[must_use]
pub(crate) fn stamp(next: GoalState, now: u64) -> GoalState {
    let normalized = normalize_goal_state(GoalState {
        updated_at: Some(now),
        ..next
    });
    served(&normalized, now)
}

/// Whether an active goal with an objective drives the continuation loop
/// (old `owns_continuation_wakeup`); it takes exclusive priority over the
/// autonomous arm.
#[must_use]
pub fn owns_continuation_wakeup(state: &GoalState) -> bool {
    state.status == GoalStatus::Active && state.objective.is_some()
}

/// A fresh active goal (old `GoalDriver::start`).
///
/// # Errors
///
/// The objective or budget fails validation.
pub(crate) fn new_goal(
    objective: &str,
    token_budget: Option<u64>,
    now: u64,
) -> anyhow::Result<GoalState> {
    let objective = validate_goal_objective(objective)?;
    let token_budget = validate_goal_budget(token_budget)?;
    Ok(GoalState {
        active: true,
        status: GoalStatus::Active,
        goal_id: Some(uuid::Uuid::new_v4().to_string()),
        objective: Some(objective),
        token_budget,
        tokens_used: 0,
        time_used_seconds: 0,
        continuations_used: 0,
        created_at: Some(now),
        // A fresh goal never inherits the previous goal's no-progress streak.
        no_progress_streak: Some(0),
        no_progress_turn_ms: None,
        updated_at: Some(now),
        last_reason: None,
        last_error: None,
    })
}

/// The paused goal; `None` when the goal is not active.
#[must_use]
pub(crate) fn paused(state: &GoalState, reason: &str) -> Option<GoalState> {
    (state.status == GoalStatus::Active).then(|| GoalState {
        active: false,
        status: GoalStatus::Paused,
        last_reason: Some(reason.to_owned()),
        last_error: None,
        ..state.clone()
    })
}

/// The resumed goal (active, or still `budget_limited` when its budget is
/// spent); `None` when there is nothing to resume.
#[must_use]
pub(crate) fn resumed(state: &GoalState) -> Option<GoalState> {
    if state.objective.is_none()
        || !matches!(state.status, GoalStatus::Paused | GoalStatus::BudgetLimited)
    {
        return None;
    }
    let exhausted = state
        .token_budget
        .is_some_and(|budget| state.tokens_used >= budget);
    let status = if exhausted {
        GoalStatus::BudgetLimited
    } else {
        GoalStatus::Active
    };
    Some(GoalState {
        active: status == GoalStatus::Active,
        status,
        last_reason: exhausted.then(|| "Goal token budget already reached".to_owned()),
        last_error: None,
        ..state.clone()
    })
}

/// The completed goal; `None` when there is no goal.
#[must_use]
pub(crate) fn completed(state: &GoalState) -> Option<GoalState> {
    if state.objective.is_none() || state.status == GoalStatus::Idle {
        return None;
    }
    Some(GoalState {
        active: false,
        status: GoalStatus::Complete,
        last_reason: Some("Goal achieved".to_owned()),
        last_error: None,
        ..state.clone()
    })
}

/// The goal failed by a terminal provider error (old
/// `finish_for_terminal_message` with `StopReason::Error`); `None` when the
/// goal is not active.
#[must_use]
pub(crate) fn failed(state: &GoalState, error: Option<&str>) -> Option<GoalState> {
    if state.status != GoalStatus::Active {
        return None;
    }
    let reason = error
        .filter(|message| !message.is_empty())
        .unwrap_or(ASSISTANT_FAILED);
    Some(GoalState {
        active: false,
        status: GoalStatus::Error,
        last_reason: Some(reason.to_owned()),
        last_error: Some(reason.to_owned()),
        ..state.clone()
    })
}

/// What accounting one settled response did to the goal.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum UsageOutcome {
    /// The usage was added.
    Accounted(GoalState),
    /// The goal hit its token budget and moved to `budget_limited`.
    BudgetReached(GoalState),
    /// The goal was not active.
    Ignored,
}

/// Account one settled response's usage (old `record_assistant_usage`):
/// input plus output tokens, as `crate::goals::goal_token_delta_for_usage`.
#[must_use]
pub(crate) fn accounted(state: &GoalState, usage: &Usage) -> UsageOutcome {
    if state.status != GoalStatus::Active {
        return UsageOutcome::Ignored;
    }
    let next = GoalState {
        tokens_used: state
            .tokens_used
            .saturating_add(usage.input)
            .saturating_add(usage.output),
        ..state.clone()
    };
    match next.token_budget {
        Some(budget) if next.tokens_used >= budget => UsageOutcome::BudgetReached(GoalState {
            active: false,
            status: GoalStatus::BudgetLimited,
            last_reason: Some(format!("Reached {budget} token goal budget")),
            last_error: None,
            ..next
        }),
        Some(_) | None => UsageOutcome::Accounted(next),
    }
}

/// Whether a settled response spends the goal and autonomous budgets: every
/// settled response except a failed or aborted one.
#[must_use]
pub(crate) fn spends_budget(stop_reason: StopReason) -> bool {
    match stop_reason {
        StopReason::Stop | StopReason::Length | StopReason::ToolUse => true,
        StopReason::Error | StopReason::Aborted | StopReason::Pending | StopReason::Deferred => {
            false
        }
    }
}

/// Whether the response produced no output: every content block is empty.
/// Tool calls are always output.
#[must_use]
pub fn turn_produced_no_output(message: &AssistantMessage) -> bool {
    message.content.iter().all(|block| match block {
        AssistantContentBlock::Text(text) => text.text.is_empty(),
        AssistantContentBlock::Thinking(thinking) => thinking.thinking.is_empty(),
        AssistantContentBlock::ToolCall(_) => false,
    })
}

/// The provider-failure text when `message` settled as a terminal provider
/// failure (stop reason `error`, not the quota-park `rate_limit` class).
#[must_use]
pub fn terminal_provider_failure(message: &AssistantMessage) -> Option<String> {
    if message.stop_reason != StopReason::Error {
        return None;
    }
    let kind = message.diagnostics.as_ref().and_then(|diagnostics| {
        diagnostics
            .iter()
            .find(|diagnostic| diagnostic.kind == "provider_stream_failure")
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
            .unwrap_or_else(|| ASSISTANT_FAILED.to_owned()),
    )
}

/// The continuation mint's decision at a final answer.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Mint {
    /// No continuation; `Some` carries a state change to write (the
    /// no-progress cap's terminal error).
    Refuse(Option<GoalState>),
    /// The answer produced no output: the strike is written and the
    /// continuation waits until `until` (wall-clock ms).
    Backoff { state: GoalState, until: u64 },
    /// One continuation slot is consumed; the goal-context continuation
    /// text of the written state continues the run.
    Continue(GoalState),
}

/// The mint at a final answer (old `next_continuation_message` with its
/// progress gate). Provider failures and quota parks never reach a final
/// answer on the Harness, so the gate's remaining arm is the no-output
/// strike with its doubling backoff and the unconditional cap.
#[must_use]
pub(crate) fn mint(state: &GoalState, answer: &AssistantMessage, now: u64) -> Mint {
    if !owns_continuation_wakeup(state) {
        return Mint::Refuse(None);
    }
    let mut current = state.clone();
    // Only a turn of this goal's lifetime judges it; a legacy state without
    // `created_at` keeps the check.
    let turn_is_this_goals = current
        .created_at
        .is_none_or(|created_at| answer.timestamp > created_at);
    // The examined-turn dedup: a turn at or before the last counted one
    // never re-enters the progress machinery.
    let turn_ms = i64::try_from(answer.timestamp).unwrap_or(i64::MAX);
    let turn_is_new = current
        .no_progress_turn_ms
        .is_none_or(|examined| turn_ms > examined);
    let streak = current.no_progress_streak.unwrap_or(0);
    if turn_is_this_goals && turn_is_new {
        if turn_produced_no_output(answer) {
            let streak = streak.saturating_add(1);
            let struck = GoalState {
                no_progress_streak: Some(streak),
                no_progress_turn_ms: Some(turn_ms),
                ..current
            };
            if streak >= CONTINUATION_NO_PROGRESS_CAP {
                return Mint::Refuse(Some(cap_error(&struck)));
            }
            let until = now.saturating_add(
                CONTINUATION_NO_PROGRESS_BACKOFF_BASE_MS
                    .saturating_mul(2u64.saturating_pow(streak.saturating_sub(1))),
            );
            return Mint::Backoff {
                state: struck,
                until,
            };
        }
        if streak != 0 {
            // A progress turn resets the streak.
            current = GoalState {
                no_progress_streak: Some(0),
                no_progress_turn_ms: Some(turn_ms),
                ..current
            };
        }
    }
    mint_slot(&current)
}

/// The mint once a no-progress backoff window passed: the cap check and the
/// slot, without judging a turn again.
#[must_use]
pub(crate) fn mint_after_backoff(state: &GoalState) -> Mint {
    if !owns_continuation_wakeup(state) {
        return Mint::Refuse(None);
    }
    mint_slot(state)
}

/// The unconditional cap, then one continuation slot.
fn mint_slot(state: &GoalState) -> Mint {
    if state.no_progress_streak.unwrap_or(0) >= CONTINUATION_NO_PROGRESS_CAP {
        return Mint::Refuse(Some(cap_error(state)));
    }
    Mint::Continue(GoalState {
        continuations_used: state.continuations_used.saturating_add(1),
        last_reason: None,
        last_error: None,
        ..state.clone()
    })
}

fn cap_error(state: &GoalState) -> GoalState {
    GoalState {
        active: false,
        status: GoalStatus::Error,
        last_reason: Some(NO_PROGRESS_CAP_REASON.to_owned()),
        last_error: Some(NO_PROGRESS_CAP_REASON.to_owned()),
        ..state.clone()
    }
}
