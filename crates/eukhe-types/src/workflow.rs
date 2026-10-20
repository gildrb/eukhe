//! Dynamic workflows: the size presets, and the run snapshot the
//! `workflow_activity` daemon lane returns to the `/workflows` view.

use serde::{Deserialize, Serialize};

/// How many agents one dynamic workflow may use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WorkflowSize {
    Small,
    Medium,
    Large,
}

/// The agent limits of one size.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WorkflowLimits {
    /// Agents that run at once.
    pub concurrency: u32,
    /// Agents one run may spawn in total.
    pub max_agents: u32,
}

impl WorkflowSize {
    /// Every size, smallest first.
    pub const ALL: [Self; 3] = [Self::Small, Self::Medium, Self::Large];

    /// The size as typed: `small`, `medium`, or `large`.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Small => "small",
            Self::Medium => "medium",
            Self::Large => "large",
        }
    }

    /// The size named `value`; `None` for any other text.
    #[must_use]
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "small" => Some(Self::Small),
            "medium" => Some(Self::Medium),
            "large" => Some(Self::Large),
            _ => None,
        }
    }

    /// The limits of the size.
    #[must_use]
    pub fn limits(self) -> WorkflowLimits {
        match self {
            Self::Small => WorkflowLimits {
                concurrency: 3,
                max_agents: 5,
            },
            Self::Medium => WorkflowLimits {
                concurrency: 6,
                max_agents: 10,
            },
            Self::Large => WorkflowLimits {
                concurrency: 12,
                max_agents: 25,
            },
        }
    }
}

/// Where a run stands.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "camelCase")]
pub enum WorkflowRunState {
    Running,
    Done,
    Failed { error: String },
    Cancelled,
}

impl WorkflowRunState {
    /// Whether the run ended.
    #[must_use]
    pub fn is_terminal(&self) -> bool {
        match self {
            Self::Running => false,
            Self::Done | Self::Failed { .. } | Self::Cancelled => true,
        }
    }
}

/// Where one phase stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum WorkflowPhaseState {
    Pending,
    Active,
    Done,
}

/// One phase of a run, as its `meta` declares it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WorkflowPhase {
    pub title: String,
    pub state: WorkflowPhaseState,
}

/// Where one agent of a run stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum WorkflowAgentStatus {
    Queued,
    Running,
    Done,
    Failed,
    Cancelled,
    /// A resumed run took the agent's answer from an earlier run.
    Cached,
}

impl WorkflowAgentStatus {
    /// Whether the agent ended.
    #[must_use]
    pub fn is_terminal(self) -> bool {
        match self {
            Self::Queued | Self::Running => false,
            Self::Done | Self::Failed | Self::Cancelled | Self::Cached => true,
        }
    }
}

/// One agent of a run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WorkflowAgent {
    /// The agent's number in its run: 1, 2, ... in call order.
    pub ordinal: u32,
    pub label: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub phase: Option<String>,
    pub status: WorkflowAgentStatus,
    /// The child session; `None` before the spawn, and for a cached agent.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub child_session_id: Option<String>,
    /// A short note: the answer preview or the error.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

/// One run of a dynamic workflow, as the `/workflows` view shows it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WorkflowRunSnapshot {
    pub run_id: String,
    pub session_id: String,
    pub name: String,
    pub description: String,
    pub size: WorkflowSize,
    pub state: WorkflowRunState,
    pub phases: Vec<WorkflowPhase>,
    pub agents: Vec<WorkflowAgent>,
    /// Agents spawned so far (cached agents not counted).
    pub spawned: u32,
    pub done: u32,
    pub failed: u32,
    pub max_agents: u32,
    pub concurrency: u32,
    /// The last log lines, oldest first.
    pub logs: Vec<String>,
}

/// Log lines a snapshot keeps.
pub const WORKFLOW_LOG_TAIL: usize = 20;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes_round_trip_by_name() {
        let names: Vec<Option<WorkflowSize>> = WorkflowSize::ALL
            .iter()
            .map(|size| WorkflowSize::parse(size.as_str()))
            .collect();
        assert_eq!(
            names,
            WorkflowSize::ALL
                .iter()
                .copied()
                .map(Some)
                .collect::<Vec<_>>()
        );
        assert_eq!(WorkflowSize::parse("huge"), None);
    }
}
