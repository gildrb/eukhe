//! Thread-goal wire state. The `goal_update` session event and the attach
//! snapshot's `state.goal` field carry this object to every attached
//! surface (TUI, ACP, CLI), so the shared vocabulary lives in eukhe-types;
//! the goal engine (validation, accounting, continuation prompts) lives in
//! eukhe-core. Field shape is the TS `GoalState` (camelCase, optional keys
//! omitted).

use serde::{Deserialize, Serialize};

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
    pub active: bool,
    pub status: GoalStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub goal_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub objective: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub token_budget: Option<u64>,
    pub tokens_used: u64,
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
        active: false,
        status: GoalStatus::Idle,
        goal_id: None,
        objective: None,
        token_budget: None,
        tokens_used: 0,
        time_used_seconds: 0,
        continuations_used: 0,
        created_at: None,
        updated_at: None,
        last_reason: None,
        last_error: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A goal persisted before the no-progress strike was removed carries
    /// `noProgressStreak` and `noProgressTurnMs`: it still loads, and the
    /// old keys are ignored.
    #[test]
    fn a_goal_with_the_removed_no_progress_keys_still_loads() {
        let old = r#"{"active":true,"status":"active","goalId":"g1","objective":"ship it","tokensUsed":40,"timeUsedSeconds":12,"continuationsUsed":2,"createdAt":1000,"noProgressStreak":1,"noProgressTurnMs":2000,"updatedAt":3000}"#;
        let goal: GoalState = serde_json::from_str(old).expect("old goal");
        assert_eq!(
            goal,
            GoalState {
                active: true,
                status: GoalStatus::Active,
                goal_id: Some("g1".to_owned()),
                objective: Some("ship it".to_owned()),
                token_budget: None,
                tokens_used: 40,
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
