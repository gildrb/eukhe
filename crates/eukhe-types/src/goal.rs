//! Thread-goal wire state. The `goal_update` session event and the attach
//! snapshot's `state.goal` field carry this object to every attached
//! surface (TUI, ACP, CLI), so the shared vocabulary lives in eukhe-types;
//! the goal engine (validation, continuation prompts) lives in eukhe-core.
//! Field shape is the TS `GoalState` (camelCase, optional keys omitted).
//!
//! A goal counts no tokens: its token budget is a limit on the session's
//! budget (`crate::budget`), and the tokens a goal shows are that budget's
//! ([`GoalTokens`]).

use serde::{Deserialize, Serialize};

use crate::budget::BudgetReport;

/// The lifecycle status of a thread goal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GoalStatus {
    Idle,
    Active,
    Paused,
    BudgetLimited,
    Complete,
    Error,
}

impl GoalStatus {
    /// The wire/persisted slug (`"active"`, `"budget_limited"`, ...), the
    /// same string the TS `GoalStatus` union uses in status lines.
    #[must_use]
    pub fn slug(self) -> &'static str {
        match self {
            GoalStatus::Idle => "idle",
            GoalStatus::Active => "active",
            GoalStatus::Paused => "paused",
            GoalStatus::BudgetLimited => "budget_limited",
            GoalStatus::Complete => "complete",
            GoalStatus::Error => "error",
        }
    }
}

/// The kind of goal context the goal engine submits as input.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GoalContextKind {
    Continuation,
    /// Retired: only rows written before the session budget's wrap-up
    /// notice replaced the goal's budget-limit prompt carry it.
    BudgetLimit,
    ObjectiveUpdated,
}

impl GoalContextKind {
    /// The header word: `continuation`, `budget-limit`, or
    /// `objective-updated`.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Continuation => "continuation",
            Self::BudgetLimit => "budget-limit",
            Self::ObjectiveUpdated => "objective-updated",
        }
    }
}

/// The persisted thread-goal state (custom entry data of the
/// `thread_goal_state` session record, and the `goal_update` event payload).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct GoalState {
    pub status: GoalStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub goal_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub objective: Option<String>,
    pub time_used_seconds: u64,
    pub continuations_used: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub created_at: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub updated_at: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_error: Option<String>,
}

impl Default for GoalState {
    fn default() -> Self {
        empty_goal_state()
    }
}

/// The state with no goal (TS `emptyGoalState`).
#[must_use]
pub fn empty_goal_state() -> GoalState {
    GoalState {
        status: GoalStatus::Idle,
        goal_id: None,
        objective: None,
        time_used_seconds: 0,
        continuations_used: 0,
        created_at: None,
        updated_at: None,
        last_reason: None,
        last_error: None,
    }
}

impl GoalState {
    /// Whether the goal is live. Derived from `status`, so it can never drift
    /// from it (the old separate `active` flag could).
    #[must_use]
    pub fn is_active(&self) -> bool {
        self.status == GoalStatus::Active
    }
}

/// The tokens a goal shows: what the session's budget spent in tokens and
/// its token limit (the goal's token budget is that limit). Without a
/// budget, or one that does not limit tokens, nothing is counted: 0 of no
/// budget.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct GoalTokens {
    /// The tokens the budget spent.
    pub used: u64,
    /// The budget's token limit.
    pub budget: Option<u64>,
}

impl GoalTokens {
    /// The tokens of the session's budget `report` (`None`: no budget).
    #[must_use]
    pub fn of(report: Option<&BudgetReport>) -> Self {
        report.map_or_else(Self::default, |report| Self {
            used: report.spent.tokens,
            budget: report.limits.tokens,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A goal persisted before the no-progress strike was removed carries
    /// `noProgressStreak` and `noProgressTurnMs`, and one persisted before
    /// its token budget moved to the session's budget carries
    /// `tokenBudget` and `tokensUsed`: it still loads, and the old keys are
    /// ignored.
    #[test]
    fn a_goal_with_removed_keys_still_loads() {
        let old = r#"{"active":true,"status":"budget_limited","goalId":"g1","objective":"ship it","tokenBudget":50,"tokensUsed":40,"timeUsedSeconds":12,"continuationsUsed":2,"createdAt":1000,"noProgressStreak":1,"noProgressTurnMs":2000,"updatedAt":3000}"#;
        let goal: GoalState = serde_json::from_str(old).expect("old goal");
        assert_eq!(
            goal,
            GoalState {
                status: GoalStatus::BudgetLimited,
                goal_id: Some("g1".to_owned()),
                objective: Some("ship it".to_owned()),
                time_used_seconds: 12,
                continuations_used: 2,
                created_at: Some(1000),
                updated_at: Some(3000),
                last_reason: None,
                last_error: None,
            }
        );
    }
}
