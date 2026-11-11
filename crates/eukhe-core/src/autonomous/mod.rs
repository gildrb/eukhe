//! Autonomous mode: run state, limits, continuation text and gate
//! evaluation.
//!
//! The runtime state (`AutonomousRuntimeState`) holds one autonomous run:
//! its continuations, gates and continuation prompt. What the run may
//! spend is the session's budget (`crate::durable::budget`): enabling the
//! run puts its `maxTokens`, `timeoutMs` and `maxTurns` on the budget as
//! limits ([`autonomous_budget_limits`]), and the run stops when the
//! budget admits no more work ([`SessionBudget`]). `maxContinuations` is
//! the run's own count of continuations.

mod gates;

pub use gates::{
    should_autonomously_continue, ChildProcessResult, GateCommandRunner, ShellGateRunner,
};

use std::collections::HashMap;

use eukhe_types::budget::{
    BudgetDimension, BudgetLimits, BudgetPhase, BudgetReport, BUDGET_AMOUNT_MAX,
};
use serde::{Deserialize, Serialize};

pub const DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT: &str = "No human input is available in autonomous mode. Continue working until the host evaluator, verifier, or configured autonomous limits stop the run. If you were asking the user a question, make a reasonable assumption and verify it. If you believe you are blocked, prove it with host-observable evidence, preserve that evidence, and keep looking for safe progress while budget remains. Do not end the session yourself; the verifier/evaluator decides completion when configured gates pass.";

pub const DEFAULT_MAX_CONTINUATIONS: u64 = 3;
// No turn, token or time default: v0.10.67 checked its 12 turns, 80k
// tokens (input + output + cache write) and 30 minutes only between
// continuations, so a run went past them and still finished; the session
// budget is hard per request and also counts cache reads. Any default
// would cut such runs, so the budget is limited only by what is given.
pub const DEFAULT_GATE_MAX_RETRIES: u64 = 3;
pub const DEFAULT_GATE_TIMEOUT_MS: u64 = 5 * 60 * 1000;
/// One keep-alive continuation per 25 minutes of continuous subagent
/// activity.
pub const DEFAULT_SUBAGENT_KEEP_ALIVE_MS: u64 = 25 * 60 * 1000;
/// Largest keep-alive window accepted (a Node-era clamp; still a sane cap).
pub const MAX_SUBAGENT_KEEP_ALIVE_MS: u64 = 2_147_483_647;
/// JSON-safe sentinel meaning "no cap".
pub const UNLIMITED_AUTONOMOUS_LIMIT: u64 = 9_007_199_254_740_991;

/// The durable autonomous status row's custom type (`/autonomous` output and
/// the driver's stop rows share it).
pub const AUTONOMOUS_STATUS_CUSTOM_TYPE: &str = "autonomous_status";

/// User-facing configuration (`/autonomous` options). `max_turns`,
/// `max_tokens` and `timeout_ms` are limits enabling the run puts on the
/// session's budget ([`autonomous_budget_limits`]).
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct AgentAutonomousConfig {
    pub enabled: Option<bool>,
    pub max_continuations: Option<u64>,
    pub max_turns: Option<u64>,
    pub max_tokens: Option<u64>,
    pub timeout_ms: Option<u64>,
    pub continuation_prompt: Option<String>,
    pub gates: Option<AgentAutonomousGateConfig>,
    /// `0` disables the subagent keep-alive valve.
    pub subagent_keep_alive_ms: Option<u64>,
}

#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct AgentAutonomousGateConfig {
    pub commands: Option<Vec<String>>,
    pub max_retries: Option<u64>,
    pub timeout_ms: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentAutonomousGateFailure {
    pub command: String,
    pub attempt: u64,
    pub exit_text: String,
    pub output: String,
}

/// The run's own limit after normalization. A run persisted before its
/// turn, token and time limits moved to the session's budget carries them
/// too: they are ignored.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AutonomousLimits {
    pub max_continuations: u64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentAutonomousStatus {
    pub enabled: bool,
    pub continuations_used: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub started_at: Option<u64>,
    pub limits: AutonomousLimits,
    pub gates: NormalizedGateConfig,
    pub gate_attempts: HashMap<String, u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_gate_failure: Option<AgentAutonomousGateFailure>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub subagent_keep_alive_ms: Option<u64>,
    /// The session's budget when the status was read: the run's requests,
    /// tokens and time are its spend and limits. `None`: no budget.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub budget: Option<BudgetReport>,
}

impl AgentAutonomousStatus {
    /// Why the run stopped or stops at its next final answer: its
    /// continuations, else the session's budget.
    #[must_use]
    pub fn limit_reason(&self) -> Option<AutonomousLimitReason> {
        limit_reason(
            self.continuations_used,
            self.limits,
            SessionBudget::of(self.budget.as_ref()),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NormalizedGateConfig {
    pub commands: Vec<String>,
    pub max_retries: u64,
    pub timeout_ms: u64,
}

/// The mutable runtime state for one autonomous run.
#[derive(Debug, Clone, PartialEq)]
pub struct AutonomousRuntimeState {
    pub enabled: bool,
    pub continuations_used: u64,
    pub started_at: Option<u64>,
    pub limits: AutonomousLimits,
    pub continuation_prompt: String,
    pub gates: NormalizedGateConfig,
    pub gate_attempts: HashMap<String, u64>,
    pub last_gate_failure: Option<AgentAutonomousGateFailure>,
    pub last_gate_failure_snapshot: Option<GitWorktreeSnapshot>,
    pub subagent_keep_alive_ms: u64,
}

/// What the session's budget admits for this agent, as its ledger report
/// shows it: an autonomous run and a goal stop once it admits no more
/// work.
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
}

/// Why an autonomous run reached its limit: its continuations, or the
/// session's budget, named by the dimension that ran short (tokens:
/// `maxTokens`, time: `timeoutMs`, requests: `maxTurns`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutonomousLimitReason {
    MaxContinuations,
    MaxTurns,
    MaxTokens,
    TimeoutMs,
    /// The budget ran short in money or tool calls (`None`: not recorded).
    Budget(Option<BudgetDimension>),
}

impl AutonomousLimitReason {
    /// The reason of a budget whose `short` dimension ran out.
    #[must_use]
    pub fn of_short(short: Option<BudgetDimension>) -> Self {
        match short {
            Some(BudgetDimension::Tokens) => Self::MaxTokens,
            Some(BudgetDimension::Time) => Self::TimeoutMs,
            Some(BudgetDimension::Requests) => Self::MaxTurns,
            Some(BudgetDimension::Cost | BudgetDimension::ToolCalls) | None => Self::Budget(short),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutonomousGateResult {
    Passed,
    Failed,
    RetryExhausted,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AutonomousDecisionReason {
    MissingTerminalEvidence,
    GateFailed,
    NotNeeded,
    LimitReached,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AutonomousDecision {
    pub should_continue: bool,
    pub reason: AutonomousDecisionReason,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GitWorktreeSnapshot {
    pub status: String,
    pub diff: String,
    pub untracked_hash: String,
}

fn normalize_limit(value: Option<u64>, default: u64) -> u64 {
    value.filter(|value| *value > 0).unwrap_or(default)
}

fn normalize_subagent_keep_alive_ms(value: Option<u64>) -> u64 {
    if value == Some(0) {
        return 0;
    }
    normalize_limit(value, DEFAULT_SUBAGENT_KEEP_ALIVE_MS).min(MAX_SUBAGENT_KEEP_ALIVE_MS)
}

pub fn create_autonomous_runtime_state(
    config: Option<&AgentAutonomousConfig>,
    default_limits: Option<&AgentAutonomousConfig>,
) -> AutonomousRuntimeState {
    let defaults = AgentAutonomousConfig::default();
    let defaults = default_limits.unwrap_or(&defaults);
    let default_continuations =
        normalize_limit(defaults.max_continuations, DEFAULT_MAX_CONTINUATIONS);
    let enabled = config.is_some_and(|config| config.enabled == Some(true));
    let Some(config) = config else {
        return AutonomousRuntimeState {
            enabled: false,
            continuations_used: 0,
            started_at: None,
            limits: AutonomousLimits {
                max_continuations: default_continuations,
            },
            continuation_prompt: DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT.to_string(),
            gates: NormalizedGateConfig {
                commands: Vec::new(),
                max_retries: DEFAULT_GATE_MAX_RETRIES,
                timeout_ms: DEFAULT_GATE_TIMEOUT_MS,
            },
            gate_attempts: HashMap::new(),
            last_gate_failure: None,
            last_gate_failure_snapshot: None,
            subagent_keep_alive_ms: normalize_subagent_keep_alive_ms(None),
        };
    };
    AutonomousRuntimeState {
        enabled,
        continuations_used: 0,
        started_at: enabled.then(now_millis),
        limits: AutonomousLimits {
            max_continuations: normalize_limit(config.max_continuations, default_continuations),
        },
        continuation_prompt: config
            .continuation_prompt
            .as_deref()
            .map(str::trim)
            .filter(|text| !text.is_empty())
            .unwrap_or(DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT)
            .to_string(),
        gates: NormalizedGateConfig {
            commands: config
                .gates
                .as_ref()
                .and_then(|gates| gates.commands.clone())
                .unwrap_or_default(),
            max_retries: normalize_limit(
                config.gates.as_ref().and_then(|gates| gates.max_retries),
                DEFAULT_GATE_MAX_RETRIES,
            ),
            timeout_ms: normalize_limit(
                config.gates.as_ref().and_then(|gates| gates.timeout_ms),
                DEFAULT_GATE_TIMEOUT_MS,
            ),
        },
        gate_attempts: HashMap::new(),
        last_gate_failure: None,
        last_gate_failure_snapshot: None,
        subagent_keep_alive_ms: normalize_subagent_keep_alive_ms(config.subagent_keep_alive_ms),
    }
}

/// The limits enabling the run with `config` puts on the session's budget
/// (`BudgetGate::limit`): `maxTokens` limits tokens, `timeoutMs` time (a
/// deadline that far from now), `maxTurns` model requests. Only a limit
/// given limits: none (or 0), [`UNLIMITED_AUTONOMOUS_LIMIT`] or anything
/// past what a budget holds limits nothing. A dimension the budget limits
/// already keeps its limit.
#[must_use]
pub fn autonomous_budget_limits(config: &AgentAutonomousConfig) -> BudgetLimits {
    let limit = |value: Option<u64>| value.filter(|limit| (1..=BUDGET_AMOUNT_MAX).contains(limit));
    BudgetLimits {
        tokens: limit(config.max_tokens),
        time_ms: limit(config.timeout_ms),
        requests: limit(config.max_turns),
        ..BudgetLimits::default()
    }
}

/// Enable/disable the run; enabling resets the continuations and failure
/// state (what the session spent stays on its budget).
pub fn set_autonomous_enabled(state: &mut AutonomousRuntimeState, enabled: bool) {
    state.enabled = enabled;
    state.gate_attempts.clear();
    state.last_gate_failure = None;
    state.last_gate_failure_snapshot = None;
    if enabled {
        state.continuations_used = 0;
        state.started_at = Some(now_millis());
    } else {
        state.started_at = None;
    }
}

/// Apply only the fields present in `config`; the rest keep their values.
/// The budget limits are the session budget's ([`autonomous_budget_limits`]).
pub fn set_autonomous_limits(state: &mut AutonomousRuntimeState, config: &AgentAutonomousConfig) {
    state.limits.max_continuations =
        normalize_limit(config.max_continuations, state.limits.max_continuations);
    if let Some(prompt) = config.continuation_prompt.as_deref().map(str::trim) {
        if !prompt.is_empty() {
            state.continuation_prompt = prompt.to_string();
        }
    }
    if let Some(gates) = &config.gates {
        if let Some(commands) = &gates.commands {
            state.gates.commands.clone_from(commands);
        }
        state.gates.max_retries = normalize_limit(gates.max_retries, state.gates.max_retries);
        state.gates.timeout_ms = normalize_limit(gates.timeout_ms, state.gates.timeout_ms);
    }
    if config.subagent_keep_alive_ms.is_some() {
        state.subagent_keep_alive_ms =
            normalize_subagent_keep_alive_ms(config.subagent_keep_alive_ms);
    }
}

/// The status of the run under the session's budget `budget`.
#[must_use]
pub fn autonomous_status(
    state: &AutonomousRuntimeState,
    budget: Option<BudgetReport>,
) -> AgentAutonomousStatus {
    AgentAutonomousStatus {
        enabled: state.enabled,
        continuations_used: state.continuations_used,
        started_at: state.started_at,
        limits: state.limits,
        gates: state.gates.clone(),
        gate_attempts: state.gate_attempts.clone(),
        last_gate_failure: state.last_gate_failure.clone(),
        subagent_keep_alive_ms: Some(state.subagent_keep_alive_ms),
        budget,
    }
}

pub fn add_autonomous_continuation(state: &mut AutonomousRuntimeState) {
    if !state.enabled {
        return;
    }
    state.continuations_used += 1;
}

/// Limit check: the run's continuations, then the session's budget.
#[must_use]
pub fn autonomous_limit_reason(
    state: &AutonomousRuntimeState,
    budget: SessionBudget,
) -> Option<AutonomousLimitReason> {
    limit_reason(state.continuations_used, state.limits, budget)
}

fn limit_reason(
    continuations_used: u64,
    limits: AutonomousLimits,
    budget: SessionBudget,
) -> Option<AutonomousLimitReason> {
    if continuations_used >= limits.max_continuations {
        return Some(AutonomousLimitReason::MaxContinuations);
    }
    match budget {
        SessionBudget::Working => None,
        SessionBudget::Short(short) => Some(AutonomousLimitReason::of_short(short)),
    }
}

/// Continuation prompt for a failed gate.
#[must_use]
pub fn build_autonomous_gate_failure_continuation(
    failure: &AgentAutonomousGateFailure,
    max_retries: u64,
    timestamp: u64,
) -> String {
    format!(
        "[autonomous-continuation: gate-failed]\n\nAutonomous quality gate failed (attempt {}/{}): `{}` {}.\n{}\n\nContinue working. Fix the failure, then produce terminal evidence. Timestamp: {}.",
        failure.attempt,
        max_retries,
        failure.command,
        failure.exit_text,
        if failure.output.is_empty() {
            String::new()
        } else {
            format!("\nOutput:\n{}\n", failure.output)
        },
        crate::session::manager::format_iso(timestamp as i64),
    )
}

/// The plain `[autonomous-continuation]` message body.
#[must_use]
pub fn autonomous_continuation_text(state: &AutonomousRuntimeState) -> String {
    format!("[autonomous-continuation]\n\n{}", state.continuation_prompt)
}

/// Highest recorded gate attempt (across the failure record and per-command
/// counts): the terminal-gate headline a headless client prints.
#[must_use]
pub fn latest_autonomous_gate_attempt(status: &AgentAutonomousStatus) -> u64 {
    let from_failure = status
        .last_gate_failure
        .as_ref()
        .map_or(0, |failure| failure.attempt);
    let from_attempts = status.gate_attempts.values().copied().max().unwrap_or(0);
    from_failure.max(from_attempts)
}

/// Human description of an autonomous limit (`<limit> reached (used/cap)`):
/// the budget's from the session budget the status carries.
#[must_use]
pub fn describe_autonomous_limit(
    status: &AgentAutonomousStatus,
    reason: AutonomousLimitReason,
) -> String {
    let budget = status.budget.as_ref();
    let spent = |dimension: BudgetDimension| {
        (
            budget.map_or(0, |report| report.spent.get(dimension)),
            budget
                .and_then(|report| report.limits.get(dimension))
                .unwrap_or(0),
        )
    };
    match reason {
        AutonomousLimitReason::MaxContinuations => format!(
            "maxContinuations reached ({}/{})",
            status.continuations_used, status.limits.max_continuations
        ),
        AutonomousLimitReason::MaxTurns => {
            let (used, limit) = spent(BudgetDimension::Requests);
            format!("maxTurns reached ({used}/{limit})")
        }
        AutonomousLimitReason::MaxTokens => {
            let (used, limit) = spent(BudgetDimension::Tokens);
            format!("maxTokens reached ({used}/{limit})")
        }
        AutonomousLimitReason::TimeoutMs => {
            let limit = budget.and_then(|report| report.limits.time_ms).unwrap_or(0);
            let left = budget.map_or(0, |report| report.free.time_ms);
            format!("timeoutMs reached ({}/{limit})", limit.saturating_sub(left))
        }
        AutonomousLimitReason::Budget(short) => format!(
            "the session's {} budget is used up",
            short.map_or("work", BudgetDimension::label)
        ),
    }
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
    use eukhe_types::budget::BudgetAmounts;

    use super::*;

    fn config(enabled: bool) -> AgentAutonomousConfig {
        AgentAutonomousConfig {
            enabled: Some(enabled),
            ..Default::default()
        }
    }

    /// A budget that ran short in `short` after spending `spent` of
    /// `limits`.
    fn short_budget(
        limits: BudgetLimits,
        spent: BudgetAmounts,
        short: BudgetDimension,
    ) -> BudgetReport {
        BudgetReport {
            limits,
            spent,
            phase: BudgetPhase::WrapUp,
            short: Some(short),
            ..BudgetReport::default()
        }
    }

    #[test]
    fn runtime_state_defaults_and_overrides() {
        let state = create_autonomous_runtime_state(Some(&config(true)), None);
        assert!(state.enabled);
        assert!(state.started_at.is_some());
        assert_eq!(state.limits.max_continuations, DEFAULT_MAX_CONTINUATIONS);
        assert_eq!(
            state.continuation_prompt,
            DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT
        );
        assert_eq!(state.subagent_keep_alive_ms, DEFAULT_SUBAGENT_KEEP_ALIVE_MS);
        // An explicit limit wins; an invalid (zero) one falls back.
        let custom = AgentAutonomousConfig {
            enabled: Some(true),
            max_continuations: Some(2),
            ..Default::default()
        };
        let custom_state = create_autonomous_runtime_state(Some(&custom), None);
        assert_eq!(custom_state.limits.max_continuations, 2);
        let zero = AgentAutonomousConfig {
            enabled: Some(true),
            max_continuations: Some(0),
            ..Default::default()
        };
        assert_eq!(
            create_autonomous_runtime_state(Some(&zero), None)
                .limits
                .max_continuations,
            DEFAULT_MAX_CONTINUATIONS
        );
        // Disabled by default.
        let off = create_autonomous_runtime_state(None, None);
        assert!(!off.enabled);
        assert_eq!(off.started_at, None);
        // Setting limits only changes provided fields.
        let mut state = off;
        set_autonomous_limits(
            &mut state,
            &AgentAutonomousConfig {
                max_continuations: Some(7),
                continuation_prompt: Some("  keep going  ".to_string()),
                ..Default::default()
            },
        );
        assert_eq!(state.limits.max_continuations, 7);
        assert_eq!(state.continuation_prompt, "keep going");
    }

    /// The turn, token and time limits go to the session's budget only when
    /// given: none, 0 or an unlimited one limits nothing (no defaults: the
    /// v0.10.67 defaults were checked only between continuations).
    #[test]
    fn the_budget_limits_of_a_run() {
        assert_eq!(
            [
                autonomous_budget_limits(&config(true)),
                autonomous_budget_limits(&AgentAutonomousConfig {
                    max_turns: Some(5),
                    max_tokens: Some(0),
                    timeout_ms: Some(UNLIMITED_AUTONOMOUS_LIMIT),
                    ..config(true)
                }),
                autonomous_budget_limits(&AgentAutonomousConfig {
                    max_tokens: Some(40_000),
                    timeout_ms: Some(60_000),
                    ..config(true)
                }),
            ],
            [
                BudgetLimits::default(),
                BudgetLimits {
                    requests: Some(5),
                    ..BudgetLimits::default()
                },
                BudgetLimits {
                    tokens: Some(40_000),
                    time_ms: Some(60_000),
                    ..BudgetLimits::default()
                },
            ]
        );
    }

    #[test]
    fn enable_resets_and_disable_clears() {
        let mut state = create_autonomous_runtime_state(Some(&config(true)), None);
        add_autonomous_continuation(&mut state);
        set_autonomous_enabled(&mut state, false);
        assert!(!state.enabled);
        assert_eq!(state.started_at, None);
        assert_eq!(state.continuations_used, 1, "disabling keeps counters");
        set_autonomous_enabled(&mut state, true);
        assert_eq!(state.continuations_used, 0);
        assert!(state.started_at.is_some());
    }

    /// The run's continuations come first; then the budget's phase names
    /// the limit by the dimension that ran short.
    #[test]
    fn limit_reasons() {
        let mut state = create_autonomous_runtime_state(Some(&config(true)), None);
        assert_eq!(
            autonomous_limit_reason(&state, SessionBudget::Working),
            None
        );
        let short =
            |dimension| autonomous_limit_reason(&state, SessionBudget::Short(Some(dimension)));
        assert_eq!(
            [
                short(BudgetDimension::Requests),
                short(BudgetDimension::Tokens),
                short(BudgetDimension::Time),
                short(BudgetDimension::Cost),
                autonomous_limit_reason(&state, SessionBudget::Short(None)),
            ],
            [
                Some(AutonomousLimitReason::MaxTurns),
                Some(AutonomousLimitReason::MaxTokens),
                Some(AutonomousLimitReason::TimeoutMs),
                Some(AutonomousLimitReason::Budget(Some(BudgetDimension::Cost))),
                Some(AutonomousLimitReason::Budget(None)),
            ]
        );
        state.continuations_used = state.limits.max_continuations;
        assert_eq!(
            autonomous_limit_reason(&state, SessionBudget::Short(Some(BudgetDimension::Tokens))),
            Some(AutonomousLimitReason::MaxContinuations)
        );
    }

    #[test]
    fn continuation_texts() {
        let state = create_autonomous_runtime_state(Some(&config(true)), None);
        assert_eq!(
            autonomous_continuation_text(&state),
            format!("[autonomous-continuation]\n\n{DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT}")
        );
        let failure = AgentAutonomousGateFailure {
            command: "make check".to_string(),
            attempt: 2,
            exit_text: "exited with code 1".to_string(),
            output: "error here".to_string(),
        };
        let text = build_autonomous_gate_failure_continuation(&failure, 3, 0);
        assert!(text.starts_with("[autonomous-continuation: gate-failed]\n\nAutonomous quality gate failed (attempt 2/3): `make check` exited with code 1.\n\nOutput:\nerror here\n"));
        assert!(text.contains("Continue working. Fix the failure, then produce terminal evidence."));
    }

    /// The status's budget names what was spent of each limit.
    #[test]
    fn limit_descriptions() {
        let state = create_autonomous_runtime_state(Some(&config(true)), None);
        let limits = BudgetLimits {
            tokens: Some(80_000),
            time_ms: Some(60_000),
            requests: Some(3),
            ..BudgetLimits::default()
        };
        let spent = BudgetAmounts {
            tokens: 81_000,
            requests: 3,
            ..BudgetAmounts::default()
        };
        let mut report = short_budget(limits, spent, BudgetDimension::Requests);
        report.free.time_ms = 5_000;
        let status = autonomous_status(&state, Some(report));
        assert_eq!(status.limit_reason(), Some(AutonomousLimitReason::MaxTurns));
        assert_eq!(
            [
                AutonomousLimitReason::MaxContinuations,
                AutonomousLimitReason::MaxTurns,
                AutonomousLimitReason::MaxTokens,
                AutonomousLimitReason::TimeoutMs,
                AutonomousLimitReason::Budget(Some(BudgetDimension::ToolCalls)),
            ]
            .map(|reason| describe_autonomous_limit(&status, reason)),
            [
                "maxContinuations reached (0/3)",
                "maxTurns reached (3/3)",
                "maxTokens reached (81000/80000)",
                "timeoutMs reached (55000/60000)",
                "the session's tool calls budget is used up",
            ]
            .map(str::to_owned)
        );
        assert_eq!(autonomous_status(&state, None).limit_reason(), None);
    }
}
