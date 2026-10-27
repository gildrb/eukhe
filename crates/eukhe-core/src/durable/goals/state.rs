//! Goal-state transitions: the goal driver's lifecycle (and its
//! `progress` child) as
//! pure functions over [`GoalState`]. The callers read the `eukhe.goal`
//! document inside a commit, apply one transition, and write the result back
//! in the same commit, so every transition is one atomic read-modify-write.
//!
//! Every write goes through [`stamp`] (the state normalization:
//! `updated_at`, the derived `active` flag, and the creation-based timer).

use eukhe_bend::wire::{Reader, Writer, NAT_MAX};
use eukhe_bend::Entry;
use eukhe_types::pi_ai::{AssistantMessage, StopReason, Usage};

use crate::goals::{
    normalize_goal_state, validate_goal_budget, validate_goal_objective, GoalState, GoalStatus,
};

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

/// The continuation mint at a final answer or after a manual compaction
/// (old `next_continuation_message`): the goal with one continuation slot
/// consumed, whose goal-context continuation text continues the run; `None`
/// when the goal does not own the continuation wakeup. An empty reply never
/// reaches it: the Harness fails it as a model error (LAWS.bend
/// H4.7), and the failed run fails the goal.
#[must_use]
pub(crate) fn mint(state: &GoalState) -> Option<GoalState> {
    owns_continuation_wakeup(state).then(|| GoalState {
        continuations_used: state.continuations_used.saturating_add(1),
        last_reason: None,
        last_error: None,
        ..state.clone()
    })
}

/// The goal's last progress check of the same run and goal: its count of
/// continuations in a row with no new work, and the session's work then
/// (its [`crate::durable::children::WorkLedger::count`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Prior {
    pub(crate) stalls: u64,
    pub(crate) work: u64,
}

/// The progress check's verdict at one goal continuation: the count of
/// continuations in a row that did no new work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Stall {
    /// The goal continues.
    Go { stalls: u64 },
    /// The count reached the cap: the goal pauses.
    Stop { stalls: u64 },
}

/// The progress check (`judge` in `bend/progress.bend`, run by the
/// compiled Bend core; `laws/progress.bend`): the first check (no
/// `prior`) starts the count; new work (the count grew) clears it; else it
/// grows by one, and at `cap` the goal stops. The counts saturate at the
/// wire's [`NAT_MAX`], below which the core holds the count of stalls
/// (`goal_judge_held`).
pub(crate) fn stall_check(cap: u64, prior: Option<Prior>, work: u64) -> Stall {
    eukhe_bend::expect_core(Entry::Progress, judge(cap, prior, work))
}

fn judge(cap: u64, prior: Option<Prior>, work: u64) -> Result<Stall, eukhe_bend::Error> {
    let mut request = Writer::new();
    // The bound of the count of stalls: the wire's largest Nat.
    request.nat(NAT_MAX).nat(cap.min(NAT_MAX));
    match prior {
        None => request.none(),
        Some(prior) => request
            .some()
            .nat(prior.stalls.min(NAT_MAX))
            .nat(prior.work.min(NAT_MAX)),
    };
    request.nat(work.min(NAT_MAX));
    let reply = eukhe_bend::call(Entry::Progress, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let stall = match reply.tag_of(2, "a goal check")? {
        0 => Stall::Go {
            stalls: reply.nat()?,
        },
        // `tag_of` answers a tag below 2: this is 1.
        _ => Stall::Stop {
            stalls: reply.nat()?,
        },
    };
    reply.end()?;
    Ok(stall)
}
