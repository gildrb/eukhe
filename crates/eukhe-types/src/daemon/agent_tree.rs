//! A node's place in the agent tree: the runtime metadata a tree node's
//! session carries from its spawn (`treeRole`, `treeScope`, `treePath`,
//! `treeAllowance`, `treeDeadline`), and the node's status its roster row
//! shows.

use serde::{Deserialize, Serialize};

/// A node's role in its tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TreeRole {
    /// The tree's root: the whole scope.
    Root,
    /// A split's left child.
    Left,
    /// A split's right child.
    Right,
    /// A read-only leaf: no write scope.
    Help,
    /// A harness-run internal node of a workflow's tree.
    Integrator,
}

/// A node's place, as its spawn's runtime metadata names it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TreePlace {
    #[serde(rename = "treeRole")]
    pub role: TreeRole,
    /// Paths relative to the workspace root (`""` = everything).
    #[serde(rename = "treeScope")]
    pub scope: Vec<String>,
    /// Left/right steps from the root (`""` = the root, `"L"`, `"LR"`); a
    /// help leaf: its node's path.
    #[serde(rename = "treePath")]
    pub path: String,
    /// The nodes the node may hold, itself included.
    #[serde(rename = "treeAllowance")]
    pub allowance: u64,
    /// The node's deadline (Unix ms); `None`: unlimited.
    #[serde(
        rename = "treeDeadline",
        default,
        skip_serializing_if = "Option::is_none"
    )]
    pub deadline: Option<u64>,
}

/// Where a node stands: running, or how its last run ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TreeStatus {
    Running,
    /// The last run answered.
    Finished,
    /// The last run ended on an error.
    Failed,
    /// The last run was aborted (a tree cancel, a deadline, an abort).
    Cancelled,
}

/// How a node's check (`agentTree.checkCommand`, else the detected one)
/// ended.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum CheckOutcome {
    /// Exit 0.
    Passed,
    /// Another exit code; `None`: killed by a signal, or the command did
    /// not start (the output says why).
    Failed { code: Option<i32> },
    /// Killed at the timeout.
    TimedOut,
}

impl CheckOutcome {
    /// `passed`, `failed (exit 1)`, `failed (no exit code)`, `timed out`.
    #[must_use]
    pub fn verdict(&self) -> String {
        match self {
            Self::Passed => "passed".to_owned(),
            Self::Failed { code: Some(code) } => format!("failed (exit {code})"),
            Self::Failed { code: None } => "failed (no exit code)".to_owned(),
            Self::TimedOut => "timed out".to_owned(),
        }
    }
}

/// Where a child's hand-back runs a check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum CheckPlace {
    /// In the child's checkout, over what it changed.
    Checkout,
    /// In the parent's workspace, over what the integration took.
    Integration,
}

/// A check's state, as its process shows it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum CheckPhase {
    /// The process runs; `last_line`: the last line it printed.
    #[serde(rename_all = "camelCase")]
    Running { last_line: Option<String> },
    /// The process ended; `last_lines`: the last lines of its output.
    #[serde(rename_all = "camelCase")]
    Ended {
        outcome: CheckOutcome,
        last_lines: Vec<String>,
    },
}

/// One report of a child's hand-back check: at its start, at each
/// interval while it runs, and at its end.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CheckProgress {
    /// The child whose hand-back runs the check (its RLM child id).
    pub child: String,
    pub place: CheckPlace,
    pub command: String,
    /// Since the process started.
    pub elapsed_ms: u64,
    pub phase: CheckPhase,
}

impl CheckProgress {
    /// The status line: `check running 12m 30s: <command> (<child>'s
    /// checkout); last line: <line>`, at the end `check failed (exit 1)
    /// in 12m 30s: <command> (...); last lines: <line> | <line>`.
    #[must_use]
    pub fn text(&self) -> String {
        let elapsed = elapsed_text(self.elapsed_ms);
        let place = match self.place {
            CheckPlace::Checkout => format!("{}'s checkout", self.child),
            CheckPlace::Integration => format!("after {}'s integration", self.child),
        };
        let (head, tail) = match &self.phase {
            CheckPhase::Running { last_line } => (
                format!("check running {elapsed}: {} ({place})", self.command),
                last_line
                    .as_ref()
                    .map(|line| format!("; last line: {line}")),
            ),
            CheckPhase::Ended {
                outcome,
                last_lines,
            } => (
                format!(
                    "check {} in {elapsed}: {} ({place})",
                    outcome.verdict(),
                    self.command
                ),
                match outcome {
                    CheckOutcome::Passed => None,
                    CheckOutcome::Failed { .. } | CheckOutcome::TimedOut => (!last_lines
                        .is_empty())
                    .then(|| format!("; last lines: {}", last_lines.join(" | "))),
                },
            ),
        };
        match tail {
            Some(tail) => head + &tail,
            None => head,
        }
    }
}

/// `ms` as `1h 2m 3s`, `12m 30s`, `45s`.
#[must_use]
pub fn elapsed_text(ms: u64) -> String {
    let seconds = ms / 1000;
    let (hours, minutes, seconds) = (seconds / 3600, seconds / 60 % 60, seconds % 60);
    match (hours, minutes) {
        (0, 0) => format!("{seconds}s"),
        (0, _) => format!("{minutes}m {seconds}s"),
        _ => format!("{hours}h {minutes}m {seconds}s"),
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    /// A spawn's runtime metadata reads as the node's place; the other
    /// metadata keys stay out of it.
    #[test]
    fn spawn_metadata_reads_as_the_place() {
        let metadata = json!({
            "kind": "subagent",
            "rlmChildId": "sub-1",
            "treeRole": "left",
            "treeScope": ["crates/eukhe-tui", "docs"],
            "treePath": "L",
            "treeAllowance": 7,
        });
        assert_eq!(
            serde_json::from_value::<TreePlace>(metadata).expect("a place"),
            TreePlace {
                role: TreeRole::Left,
                scope: vec!["crates/eukhe-tui".to_string(), "docs".to_string()],
                path: "L".to_string(),
                allowance: 7,
                deadline: None,
            }
        );
    }

    /// A check's status line names its state, elapsed time, command,
    /// place and the last output it printed.
    #[test]
    fn check_progress_reads_as_a_status_line() {
        let progress = |phase| CheckProgress {
            child: "sub-1".to_string(),
            place: CheckPlace::Checkout,
            command: "./check.sh".to_string(),
            elapsed_ms: 750_400,
            phase,
        };
        assert_eq!(
            [
                progress(CheckPhase::Running {
                    last_line: Some("waiting for a slot".to_string()),
                })
                .text(),
                progress(CheckPhase::Ended {
                    outcome: CheckOutcome::Failed { code: Some(1) },
                    last_lines: vec!["FMT FAILED".to_string(), "CHECK EXIT 1".to_string()],
                })
                .text(),
                CheckProgress {
                    place: CheckPlace::Integration,
                    elapsed_ms: 3_723_000,
                    ..progress(CheckPhase::Ended {
                        outcome: CheckOutcome::Passed,
                        last_lines: vec!["ok".to_string()],
                    })
                }
                .text(),
            ],
            [
                "check running 12m 30s: ./check.sh (sub-1's checkout); last line: waiting for a slot",
                "check failed (exit 1) in 12m 30s: ./check.sh (sub-1's checkout); last lines: FMT FAILED | CHECK EXIT 1",
                "check passed in 1h 2m 3s: ./check.sh (after sub-1's integration)",
            ]
        );
    }
}
