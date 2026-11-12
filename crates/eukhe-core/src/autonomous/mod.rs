//! Autonomous mode: run state, limits, continuation text and gate
//! evaluation.
//!
//! The runtime state (`AutonomousRuntimeState`) holds one autonomous run:
//! its continuations, gates, continuation prompt and its own limits, as
//! v0.10.67 had them. The run counts its turns (each settled response of
//! the agent, once per generation; never a side request such as the
//! title) and their tokens (input, output and cache writes) and keeps its
//! start. `maxTurns`, `maxTokens` and `timeoutMs` (12, 80,000 and 30
//! minutes unless given) are soft: they are checked only between
//! continuations, so the turn that crosses one completes and the run then
//! stops. The session's budget (`crate::durable::budget`), set only
//! explicitly, is another, hard limit: the run also stops once it admits
//! no more work ([`SessionBudget`]).

mod gates;

pub use gates::{
    should_autonomously_continue, ChildProcessResult, GateCommandRunner, ShellGateRunner,
};

use std::collections::HashMap;

use eukhe_types::budget::{BudgetDimension, BudgetPhase, BudgetReport};
use eukhe_types::pi_ai::Usage;
use serde::{Deserialize, Serialize};

pub const DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT: &str = "No human input is available in autonomous mode. Continue working until the host evaluator, verifier, or configured autonomous limits stop the run. If you were asking the user a question, make a reasonable assumption and verify it. If you believe you are blocked, prove it with host-observable evidence, preserve that evidence, and keep looking for safe progress while budget remains. Do not end the session yourself; the verifier/evaluator decides completion when configured gates pass.";

pub const DEFAULT_MAX_CONTINUATIONS: u64 = 3;
pub const DEFAULT_MAX_TURNS: u64 = 12;
pub const DEFAULT_MAX_TOKENS: u64 = 80_000;
pub const DEFAULT_TIMEOUT_MS: u64 = 30 * 60 * 1000;
pub const DEFAULT_GATE_MAX_RETRIES: u64 = 3;
pub const DEFAULT_GATE_TIMEOUT_MS: u64 = 5 * 60 * 1000;
/// One keep-alive continuation per 25 minutes of continuous subagent
/// activity, strictly below the default wall-clock limit.
pub const DEFAULT_SUBAGENT_KEEP_ALIVE_MS: u64 = 25 * 60 * 1000;
/// Largest keep-alive window accepted (a Node-era clamp; still a sane cap).
pub const MAX_SUBAGENT_KEEP_ALIVE_MS: u64 = 2_147_483_647;
/// JSON-safe sentinel meaning "no cap".
pub const UNLIMITED_AUTONOMOUS_LIMIT: u64 = 9_007_199_254_740_991;

/// The durable autonomous status row's custom type (`/autonomous` output and
/// the driver's stop rows share it).
pub const AUTONOMOUS_STATUS_CUSTOM_TYPE: &str = "autonomous_status";

/// User-facing configuration (`/autonomous` options). `max_turns`,
/// `max_tokens` and `timeout_ms` are the run's own soft limits
/// ([`AutonomousLimits`]).
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

/// The run's own limits after normalization (soft: checked between
/// continuations). [`UNLIMITED_AUTONOMOUS_LIMIT`] is no limit.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AutonomousLimits {
    pub max_continuations: u64,
    pub max_turns: u64,
    pub max_tokens: u64,
    pub timeout_ms: u64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentAutonomousStatus {
    pub enabled: bool,
    pub continuations_used: u64,
    /// The agent's settled responses in this run.
    pub turns_used: u64,
    /// Their input, output and cache-write tokens.
    pub tokens_used: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub started_at: Option<u64>,
    pub limits: AutonomousLimits,
    pub gates: NormalizedGateConfig,
    pub gate_attempts: HashMap<String, u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_gate_failure: Option<AgentAutonomousGateFailure>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub subagent_keep_alive_ms: Option<u64>,
    /// The session's budget when the status was read. `None`: no budget.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub budget: Option<BudgetReport>,
}

impl AgentAutonomousStatus {
    /// Why the run stopped or stops at its next final answer at `now`: its
    /// own limits, else the session's budget.
    #[must_use]
    pub fn limit_reason(&self, now: u64) -> Option<AutonomousLimitReason> {
        limit_reason(
            Used {
                continuations: self.continuations_used,
                turns: self.turns_used,
                tokens: self.tokens_used,
                started_at: self.started_at,
            },
            self.limits,
            SessionBudget::of(self.budget.as_ref()),
            now,
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
    /// The agent's settled responses since the run was enabled.
    pub turns_used: u64,
    /// Their input, output and cache-write tokens.
    pub tokens_used: u64,
    pub started_at: Option<u64>,
    pub limits: AutonomousLimits,
    pub continuation_prompt: String,
    pub gates: NormalizedGateConfig,
    pub gate_attempts: HashMap<String, u64>,
    pub last_gate_failure: Option<AgentAutonomousGateFailure>,
    pub last_gate_failure_snapshot: Option<GitWorktreeSnapshot>,
    pub subagent_keep_alive_ms: u64,
}

/// What a run used of its own limits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Used {
    continuations: u64,
    turns: u64,
    tokens: u64,
    started_at: Option<u64>,
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

/// Why an autonomous run reached its limit: its own continuations, turns,
/// tokens or time, or the session's budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutonomousLimitReason {
    MaxContinuations,
    MaxTurns,
    MaxTokens,
    TimeoutMs,
    /// The session's budget admits no more work: the dimension that ran
    /// short (`None`: not recorded).
    Budget(Option<BudgetDimension>),
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
    let enabled = config.is_some_and(|config| config.enabled == Some(true));
    let default_limits = AutonomousLimits {
        max_continuations: normalize_limit(defaults.max_continuations, DEFAULT_MAX_CONTINUATIONS),
        max_turns: normalize_limit(defaults.max_turns, DEFAULT_MAX_TURNS),
        max_tokens: normalize_limit(defaults.max_tokens, DEFAULT_MAX_TOKENS),
        timeout_ms: normalize_limit(defaults.timeout_ms, DEFAULT_TIMEOUT_MS),
    };
    let Some(config) = config else {
        return AutonomousRuntimeState {
            enabled: false,
            continuations_used: 0,
            turns_used: 0,
            tokens_used: 0,
            started_at: None,
            limits: default_limits,
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
        turns_used: 0,
        tokens_used: 0,
        started_at: enabled.then(now_millis),
        limits: AutonomousLimits {
            max_continuations: normalize_limit(
                config.max_continuations,
                default_limits.max_continuations,
            ),
            max_turns: normalize_limit(config.max_turns, default_limits.max_turns),
            max_tokens: normalize_limit(config.max_tokens, default_limits.max_tokens),
            timeout_ms: normalize_limit(config.timeout_ms, default_limits.timeout_ms),
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

/// Enable/disable the run; enabling resets the counters and failure
/// state.
pub fn set_autonomous_enabled(state: &mut AutonomousRuntimeState, enabled: bool) {
    state.enabled = enabled;
    state.gate_attempts.clear();
    state.last_gate_failure = None;
    state.last_gate_failure_snapshot = None;
    if enabled {
        state.continuations_used = 0;
        state.turns_used = 0;
        state.tokens_used = 0;
        state.started_at = Some(now_millis());
    } else {
        state.started_at = None;
    }
}

/// Apply only the fields present in `config`; the rest keep their values.
pub fn set_autonomous_limits(state: &mut AutonomousRuntimeState, config: &AgentAutonomousConfig) {
    state.limits.max_continuations =
        normalize_limit(config.max_continuations, state.limits.max_continuations);
    state.limits.max_turns = normalize_limit(config.max_turns, state.limits.max_turns);
    state.limits.max_tokens = normalize_limit(config.max_tokens, state.limits.max_tokens);
    state.limits.timeout_ms = normalize_limit(config.timeout_ms, state.limits.timeout_ms);
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
        turns_used: state.turns_used,
        tokens_used: state.tokens_used,
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

/// The tokens a response spends of a run's `maxTokens`: input, output and
/// cache writes (cache reads are not counted).
#[must_use]
pub fn autonomous_token_delta(usage: &Usage) -> u64 {
    usage
        .input
        .saturating_add(usage.output)
        .saturating_add(usage.cache_write)
}

/// Limit check at `now`: the run's continuations, turns, tokens and time,
/// then the session's budget.
#[must_use]
pub fn autonomous_limit_reason(
    state: &AutonomousRuntimeState,
    budget: SessionBudget,
    now: u64,
) -> Option<AutonomousLimitReason> {
    limit_reason(
        Used {
            continuations: state.continuations_used,
            turns: state.turns_used,
            tokens: state.tokens_used,
            started_at: state.started_at,
        },
        state.limits,
        budget,
        now,
    )
}

fn limit_reason(
    used: Used,
    limits: AutonomousLimits,
    budget: SessionBudget,
    now: u64,
) -> Option<AutonomousLimitReason> {
    if used.continuations >= limits.max_continuations {
        return Some(AutonomousLimitReason::MaxContinuations);
    }
    if used.turns >= limits.max_turns {
        return Some(AutonomousLimitReason::MaxTurns);
    }
    if used.tokens >= limits.max_tokens {
        return Some(AutonomousLimitReason::MaxTokens);
    }
    if let Some(started_at) = used.started_at {
        if now.saturating_sub(started_at) >= limits.timeout_ms {
            return Some(AutonomousLimitReason::TimeoutMs);
        }
    }
    match budget {
        SessionBudget::Working => None,
        SessionBudget::Short(short) => Some(AutonomousLimitReason::Budget(short)),
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

/// Human description of an autonomous limit (`<limit> reached (used/cap)`)
/// at `now`: the run's own counts, or the session's budget.
#[must_use]
pub fn describe_autonomous_limit(
    status: &AgentAutonomousStatus,
    reason: AutonomousLimitReason,
    now: u64,
) -> String {
    match reason {
        AutonomousLimitReason::MaxContinuations => format!(
            "maxContinuations reached ({}/{})",
            status.continuations_used, status.limits.max_continuations
        ),
        AutonomousLimitReason::MaxTurns => format!(
            "maxTurns reached ({}/{})",
            status.turns_used, status.limits.max_turns
        ),
        AutonomousLimitReason::MaxTokens => format!(
            "maxTokens reached ({}/{})",
            status.tokens_used, status.limits.max_tokens
        ),
        AutonomousLimitReason::TimeoutMs => {
            let elapsed = status
                .started_at
                .map_or(0, |started_at| now.saturating_sub(started_at));
            format!("timeoutMs reached ({elapsed}/{})", status.limits.timeout_ms)
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
        .map_or_default(|duration| duration.as_millis() as u64)
}

#[cfg(test)]
mod tests {
    use eukhe_types::budget::{BudgetAmounts, BudgetLimits};

    use super::*;

    fn config(enabled: bool) -> AgentAutonomousConfig {
        AgentAutonomousConfig {
            enabled: Some(enabled),
            ..Default::default()
        }
    }

    fn usage(input: u64, output: u64, cache_write: u64) -> Usage {
        Usage {
            input,
            output,
            cache_read: 1_000_000,
            cache_write,
            ..Usage::default()
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

    /// The turn, token and time limits are v0.10.67's: 12 turns, 80,000
    /// tokens and 30 minutes unless given; 0 keeps the current one and
    /// [`UNLIMITED_AUTONOMOUS_LIMIT`] is no limit.
    #[test]
    fn the_limits_of_a_run() {
        let limits = |config: &AgentAutonomousConfig| {
            let state = create_autonomous_runtime_state(Some(config), None);
            (
                state.limits.max_turns,
                state.limits.max_tokens,
                state.limits.timeout_ms,
            )
        };
        assert_eq!(
            [
                limits(&config(true)),
                limits(&AgentAutonomousConfig {
                    max_turns: Some(5),
                    max_tokens: Some(0),
                    timeout_ms: Some(UNLIMITED_AUTONOMOUS_LIMIT),
                    ..config(true)
                }),
                limits(&AgentAutonomousConfig {
                    max_tokens: Some(40_000),
                    timeout_ms: Some(60_000),
                    ..config(true)
                }),
            ],
            [
                (12, 80_000, 1_800_000),
                (5, 80_000, UNLIMITED_AUTONOMOUS_LIMIT),
                (12, 40_000, 60_000),
            ]
        );
        let mut state = create_autonomous_runtime_state(Some(&config(true)), None);
        set_autonomous_limits(
            &mut state,
            &AgentAutonomousConfig {
                max_turns: Some(2),
                ..AgentAutonomousConfig::default()
            },
        );
        set_autonomous_limits(
            &mut state,
            &AgentAutonomousConfig {
                max_tokens: Some(9),
                ..AgentAutonomousConfig::default()
            },
        );
        assert_eq!((state.limits.max_turns, state.limits.max_tokens), (2, 9));
    }

    /// A response spends its input, output and cache-write tokens of a
    /// run's `maxTokens`, never its cache reads.
    #[test]
    fn a_response_spends_its_tokens_but_no_cache_reads() {
        assert_eq!(
            [usage(100, 40, 10), usage(5, 5, 0)].map(|usage| autonomous_token_delta(&usage)),
            [150, 10]
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

    /// The run's own limits come first (continuations, turns, tokens,
    /// time); then a session budget that admits no more work, named by the
    /// dimension that ran short.
    #[test]
    fn limit_reasons() {
        let mut state = create_autonomous_runtime_state(
            Some(&AgentAutonomousConfig {
                max_turns: Some(3),
                max_tokens: Some(100),
                timeout_ms: Some(1_000),
                ..config(true)
            }),
            None,
        );
        let start = state.started_at.unwrap_or(0);
        assert_eq!(
            autonomous_limit_reason(&state, SessionBudget::Working, start),
            None
        );
        let short = |state: &AutonomousRuntimeState, dimension| {
            autonomous_limit_reason(state, SessionBudget::Short(dimension), start)
        };
        assert_eq!(
            [
                short(&state, Some(BudgetDimension::Requests)),
                short(&state, Some(BudgetDimension::Tokens)),
                short(&state, None),
            ],
            [
                Some(AutonomousLimitReason::Budget(Some(
                    BudgetDimension::Requests
                ))),
                Some(AutonomousLimitReason::Budget(Some(BudgetDimension::Tokens))),
                Some(AutonomousLimitReason::Budget(None)),
            ]
        );
        assert_eq!(
            autonomous_limit_reason(&state, SessionBudget::Working, start + 1_000),
            Some(AutonomousLimitReason::TimeoutMs)
        );
        state.tokens_used = 100;
        assert_eq!(
            short(&state, Some(BudgetDimension::Cost)),
            Some(AutonomousLimitReason::MaxTokens)
        );
        state.turns_used = 3;
        assert_eq!(
            short(&state, Some(BudgetDimension::Cost)),
            Some(AutonomousLimitReason::MaxTurns)
        );
        state.continuations_used = state.limits.max_continuations;
        assert_eq!(
            short(&state, Some(BudgetDimension::Tokens)),
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

    /// A limit names what the run used of it; the budget's names the
    /// dimension.
    #[test]
    fn limit_descriptions() {
        let mut state = create_autonomous_runtime_state(
            Some(&AgentAutonomousConfig {
                max_turns: Some(3),
                max_tokens: Some(80_000),
                timeout_ms: Some(60_000),
                ..config(true)
            }),
            None,
        );
        state.turns_used = 3;
        state.tokens_used = 81_000;
        let start = state.started_at.unwrap_or(0);
        let report = short_budget(
            BudgetLimits {
                tool_calls: Some(4),
                ..BudgetLimits::default()
            },
            BudgetAmounts {
                tool_calls: 4,
                ..BudgetAmounts::default()
            },
            BudgetDimension::ToolCalls,
        );
        let status = autonomous_status(&state, Some(report));
        assert_eq!(
            status.limit_reason(start),
            Some(AutonomousLimitReason::MaxTurns)
        );
        assert_eq!(
            [
                AutonomousLimitReason::MaxContinuations,
                AutonomousLimitReason::MaxTurns,
                AutonomousLimitReason::MaxTokens,
                AutonomousLimitReason::TimeoutMs,
                AutonomousLimitReason::Budget(Some(BudgetDimension::ToolCalls)),
            ]
            .map(|reason| describe_autonomous_limit(&status, reason, start + 55_000)),
            [
                "maxContinuations reached (0/3)",
                "maxTurns reached (3/3)",
                "maxTokens reached (81000/80000)",
                "timeoutMs reached (55000/60000)",
                "the session's tool calls budget is used up",
            ]
            .map(str::to_owned)
        );
        let fresh = create_autonomous_runtime_state(Some(&config(true)), None);
        assert_eq!(autonomous_status(&fresh, None).limit_reason(start), None);
    }
}
