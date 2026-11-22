//! Autonomous mode: a run the principal set to go on without a human. At
//! each final answer the compiled core decides what the run does
//! (`eukhe_bend::rules::autonomous`, `laws/autonomous.bend`): with checks
//! the answer is a claim the checks judge (a refuted or broken claim goes
//! back with its evidence, an ended claim stops the run with its label);
//! without checks the run is continued with its continuation prompt; a
//! budget that admits no more work stops it, and so do continuations that
//! make no progress (no tool call with a new result: steered once to
//! another approach at `directors.stallSteps` in a row, ended not done at
//! twice that). The run has no limit of its own: the run's budget
//! (`crate::durable::budget`) is its only one, and the checks
//! (`crate::durable::acceptance`) its only way to end done.
//!
//! The configuration keeps the fields of the removed own limits and gates
//! (`maxTurns`, `maxTokens`, `timeoutMs`, `maxContinuations`, `gates`) so
//! old clients and commands keep working: each maps onto the budget or the
//! checks ([`AgentAutonomousConfig::limits`],
//! [`AgentAutonomousConfig::gate_checks`],
//! [`AgentAutonomousConfig::max_returns`]), with a note naming the
//! replacement ([`AgentAutonomousConfig::deprecation_note`]).

mod runner;

pub(crate) use runner::run_gate_command;
pub use runner::{ChildProcessResult, GateCommandRunner, GitWorktreeSnapshot, ShellGateRunner};

use eukhe_types::acceptance::{AcceptanceLabel, CheckSpec};
use eukhe_types::budget::{BudgetDimension, BudgetPhase, BudgetReport, LimitValue, RunLimits};
use serde::{Deserialize, Serialize};

pub const DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT: &str = "No human input is available in autonomous mode. Continue the task. If you were asking the user a question, make a reasonable assumption and verify it. A failed command is something to fix. When every part is done, give your final answer: the run's checks judge it, and a refuted claim comes back with its evidence.";

/// JSON-safe sentinel the removed own limits used for "no cap".
pub const UNLIMITED_AUTONOMOUS_LIMIT: u64 = 9_007_199_254_740_991;

/// The durable autonomous status row's custom type (`/auto` output and
/// the driver's stop rows share it).
pub const AUTONOMOUS_STATUS_CUSTOM_TYPE: &str = "autonomous_status";

/// User-facing configuration (`/auto` options, a client's create config).
/// `enabled` and `continuation_prompt` configure the run; every other
/// field is a removed own limit or gate kept as an alias.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct AgentAutonomousConfig {
    pub enabled: Option<bool>,
    /// Alias of the checks' return cap (`--accept-returns`).
    pub max_continuations: Option<u64>,
    /// Alias of the run's model-request limit (`--budget-requests`).
    pub max_turns: Option<u64>,
    /// Alias of the run's token limit (`--budget-tokens`).
    pub max_tokens: Option<u64>,
    /// Alias of the run's time limit in ms (`--budget-time`).
    pub timeout_ms: Option<u64>,
    pub continuation_prompt: Option<String>,
    /// Alias of command checks (`--accept-cmd`).
    pub gates: Option<AgentAutonomousGateConfig>,
    /// Removed: no keep-alive continuation exists; read and ignored.
    pub subagent_keep_alive_ms: Option<u64>,
}

/// The removed gates: each command is a command check that must exit 0.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct AgentAutonomousGateConfig {
    pub commands: Option<Vec<String>>,
    /// Alias of the checks' return cap (`--accept-returns`).
    pub max_retries: Option<u64>,
    /// The time limit of each command check.
    pub timeout_ms: Option<u64>,
}

/// A removed limit as a budget limit: the sentinel is unlimited.
fn limit_value(value: u64) -> LimitValue {
    if value >= UNLIMITED_AUTONOMOUS_LIMIT {
        LimitValue::Unlimited
    } else {
        LimitValue::At(value)
    }
}

impl AgentAutonomousConfig {
    /// The run limits the removed own limits ask: turns are model
    /// requests, tokens are tokens, the timeout is the time limit.
    #[must_use]
    pub fn limits(&self) -> RunLimits {
        RunLimits::default()
            .with(BudgetDimension::Requests, self.max_turns.map(limit_value))
            .with(BudgetDimension::Tokens, self.max_tokens.map(limit_value))
            .with(BudgetDimension::Time, self.timeout_ms.map(limit_value))
    }

    /// The command checks the removed gates ask.
    #[must_use]
    pub fn gate_checks(&self) -> Vec<CheckSpec> {
        let Some(gates) = &self.gates else {
            return Vec::new();
        };
        gates
            .commands
            .iter()
            .flatten()
            .map(|command| CheckSpec::Command {
                command: command.clone(),
                expect: 0,
                timeout_ms: gates.timeout_ms,
                protect: Vec::new(),
                strength: None,
            })
            .collect()
    }

    /// The checks' return cap the removed continuation or gate-retry
    /// limits ask (the gate retries first).
    #[must_use]
    pub fn max_returns(&self) -> Option<u64> {
        self.gates
            .as_ref()
            .and_then(|gates| gates.max_retries)
            .or(self.max_continuations)
    }

    /// One line naming the replacement of each removed field given; `None`
    /// when none is.
    #[must_use]
    pub fn deprecation_note(&self) -> Option<String> {
        let mut moved = Vec::new();
        if self.max_turns.is_some() || self.max_tokens.is_some() || self.timeout_ms.is_some() {
            moved.push("its limits are the run's budget (/budget)");
        }
        if self.gates.is_some() || self.max_continuations.is_some() {
            moved.push("its gates and continuations are acceptance checks (/accept)");
        }
        if self.subagent_keep_alive_ms.is_some() {
            moved.push("the subagent keep-alive is removed");
        }
        (!moved.is_empty())
            .then(|| format!("Autonomous options are deprecated: {}.", moved.join("; ")))
    }
}

/// Why an autonomous run stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum AutonomousStop {
    /// The checks ended the claim with this label.
    Checks(AcceptanceLabel),
    /// The run's budget admits no more work.
    Budget,
    /// This many continuations in a row made no progress (no tool call
    /// with a new result), also after the harness asked for another
    /// approach: the run ended, not done.
    #[serde(rename_all = "camelCase")]
    NoProgress { stalls: u64 },
}

impl AutonomousStop {
    /// The stop as the status and a headless run's stderr show it.
    #[must_use]
    pub fn describe(self, budget: Option<&BudgetReport>) -> String {
        match self {
            Self::Checks(label) => format!("the checks ended the claim: {}", label.slug()),
            Self::Budget => format!(
                "the run's {} budget is used up",
                budget
                    .and_then(|report| report.short)
                    .map_or("work", BudgetDimension::label)
            ),
            Self::NoProgress { stalls } => no_progress_reason(stalls),
        }
    }
}

/// Why an autonomous run ended for want of progress after `stalls`
/// continuations in a row with no new work.
#[must_use]
pub fn no_progress_reason(stalls: u64) -> String {
    format!(
        "no progress: {stalls} autonomous continuations in a row made no tool call with a new result, also after the harness asked for another approach"
    )
}

/// What the session's budget admits for this agent, as its ledger report
/// shows it: an autonomous run stops once it admits no more work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionBudget {
    /// No budget, or one that admits work.
    Working,
    /// The budget's phase left `Working`: the dimension that ran short
    /// (`None`: not recorded).
    Short(Option<BudgetDimension>),
}

impl SessionBudget {
    /// The standing of the budget `report` shows (`None`: no budget).
    #[must_use]
    pub fn of(report: Option<&BudgetReport>) -> Self {
        match report {
            None => Self::Working,
            Some(report) => match report.phase {
                BudgetPhase::Working => Self::Working,
                BudgetPhase::WrapUp | BudgetPhase::Exhausted => Self::Short(report.short),
            },
        }
    }

    /// The standing as the autonomous rule reads it.
    #[must_use]
    pub fn rule(self) -> eukhe_bend::rules::autonomous::Budget {
        match self {
            Self::Working => eukhe_bend::rules::autonomous::Budget::Working,
            Self::Short(_) => eukhe_bend::rules::autonomous::Budget::Short,
        }
    }
}

/// The `/auto` status of a conversation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentAutonomousStatus {
    pub enabled: bool,
    /// The continuations the run made with its prompt.
    pub continuations_used: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub started_at: Option<u64>,
    /// Why the last run stopped.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_stop: Option<AutonomousStop>,
    /// The session's budget when the status was read. `None`: no budget.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub budget: Option<BudgetReport>,
}

/// The plain `[autonomous-continuation]` message body.
#[must_use]
pub fn autonomous_continuation_text(prompt: &str) -> String {
    format!("[autonomous-continuation]\n\n{prompt}")
}

#[must_use]
pub fn now_millis() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_millis() as u64)
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The removed own limits and gates map onto the budget and the
    /// checks, and name their replacement.
    #[test]
    fn removed_options_map_onto_the_budget_and_the_checks() {
        let config = AgentAutonomousConfig {
            enabled: Some(true),
            max_continuations: Some(5),
            max_turns: Some(4),
            max_tokens: Some(UNLIMITED_AUTONOMOUS_LIMIT),
            timeout_ms: Some(60_000),
            gates: Some(AgentAutonomousGateConfig {
                commands: Some(vec!["make check".to_owned()]),
                max_retries: Some(2),
                timeout_ms: Some(9_000),
            }),
            ..AgentAutonomousConfig::default()
        };
        assert_eq!(
            (
                config.limits(),
                config.gate_checks(),
                config.max_returns(),
                config.deprecation_note(),
            ),
            (
                RunLimits {
                    requests: Some(LimitValue::At(4)),
                    tokens: Some(LimitValue::Unlimited),
                    time_ms: Some(LimitValue::At(60_000)),
                    ..RunLimits::default()
                },
                vec![CheckSpec::Command {
                    command: "make check".to_owned(),
                    expect: 0,
                    timeout_ms: Some(9_000),
                    protect: Vec::new(),
                    strength: None,
                }],
                Some(2),
                Some("Autonomous options are deprecated: its limits are the run's budget (/budget); its gates and continuations are acceptance checks (/accept).".to_owned()),
            )
        );
    }

    /// A plain `on` names nothing deprecated.
    #[test]
    fn a_plain_config_has_no_note() {
        let config = AgentAutonomousConfig {
            enabled: Some(true),
            ..AgentAutonomousConfig::default()
        };
        assert_eq!(
            (
                config.limits(),
                config.gate_checks(),
                config.max_returns(),
                config.deprecation_note()
            ),
            (RunLimits::default(), Vec::new(), None, None)
        );
    }
}
