//! Autonomous mode on the Harness: the run state lives in the
//! `eukhe.autonomous` conversation document (the old daemon kept it in
//! process memory), and each final answer asks [`decide`] whether the run
//! continues (the old `ShellAutonomousDriver::after_turn`, with the gates
//! from `crate::autonomous`). What the run spends is the session's budget:
//! enabling it puts its turn, token and time limits on the budget
//! ([`autonomous_budget_limits`]), and the run stops when the budget admits
//! no more work.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::ops::{budget_report, conversation_of};
use eukhe_chord::context::Context;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReader};
use eukhe_types::budget::{BudgetDimension, BudgetLimits, BudgetReport};
use eukhe_types::input_origin::AutonomousNudge;
use eukhe_types::pi_ai::{StopReason, UserContent};
use serde::{Deserialize, Serialize};

use super::docs::{open_doc, read_doc, write_doc, AUTONOMOUS_DOC};
use crate::autonomous::{
    add_autonomous_continuation, autonomous_budget_limits, autonomous_continuation_text,
    autonomous_limit_reason, autonomous_status, build_autonomous_gate_failure_continuation,
    create_autonomous_runtime_state, now_millis, set_autonomous_enabled, set_autonomous_limits,
    should_autonomously_continue, AgentAutonomousConfig, AgentAutonomousGateFailure,
    AgentAutonomousStatus, AutonomousDecisionReason, AutonomousLimitReason, AutonomousLimits,
    AutonomousRuntimeState, GateCommandRunner, GitWorktreeSnapshot, NormalizedGateConfig,
    SessionBudget, AUTONOMOUS_STATUS_CUSTOM_TYPE,
};
use crate::durable::budget::BudgetGate;
use crate::durable::entries::custom_entry_draft;
use crate::slash_command_args::format_autonomous_status;

/// The persisted autonomous run (the runtime state plus the last stop
/// decision). A run persisted before its turn, token and time limits moved
/// to the session's budget carries `turnsUsed` and `tokensUsed` too: they
/// are ignored.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AutonomousDocState {
    pub enabled: bool,
    pub continuations_used: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub started_at: Option<u64>,
    pub limits: AutonomousLimits,
    pub continuation_prompt: String,
    pub gates: NormalizedGateConfig,
    #[serde(default)]
    pub gate_attempts: BTreeMap<String, u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_gate_failure: Option<AgentAutonomousGateFailure>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_gate_failure_snapshot: Option<WorktreeSnapshot>,
    pub subagent_keep_alive_ms: u64,
    /// Why the last run stopped; cleared when a run is enabled.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_stop: Option<AutonomousStop>,
}

/// The workspace snapshot taken after a failed gate (old
/// `GitWorktreeSnapshot`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WorktreeSnapshot {
    pub status: String,
    pub diff: String,
    pub untracked_hash: String,
}

/// Why an autonomous run stopped. `MaxTurns`, `MaxTokens` and `TimeoutMs`
/// are the session's budget running short in requests, tokens and time;
/// `Budget` in money or tool calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum AutonomousStop {
    GatePassed,
    GateRetryExhausted,
    MaxContinuations,
    MaxTurns,
    MaxTokens,
    TimeoutMs,
    Budget,
}

impl AutonomousStop {
    fn of_limit(reason: AutonomousLimitReason) -> Self {
        match reason {
            AutonomousLimitReason::MaxContinuations => Self::MaxContinuations,
            AutonomousLimitReason::MaxTurns => Self::MaxTurns,
            AutonomousLimitReason::MaxTokens => Self::MaxTokens,
            AutonomousLimitReason::TimeoutMs => Self::TimeoutMs,
            AutonomousLimitReason::Budget(_) => Self::Budget,
        }
    }
}

impl AutonomousDocState {
    /// A disabled run with the default limits (the document's initial value).
    #[must_use]
    pub fn initial() -> Self {
        Self::from_runtime(&create_autonomous_runtime_state(None, None), None)
    }

    /// The persisted form of `state`.
    #[must_use]
    pub fn from_runtime(state: &AutonomousRuntimeState, last_stop: Option<AutonomousStop>) -> Self {
        Self {
            enabled: state.enabled,
            continuations_used: state.continuations_used,
            started_at: state.started_at,
            limits: state.limits,
            continuation_prompt: state.continuation_prompt.clone(),
            gates: state.gates.clone(),
            gate_attempts: state
                .gate_attempts
                .iter()
                .map(|(command, attempts)| (command.clone(), *attempts))
                .collect(),
            last_gate_failure: state.last_gate_failure.clone(),
            last_gate_failure_snapshot: state.last_gate_failure_snapshot.as_ref().map(|snapshot| {
                WorktreeSnapshot {
                    status: snapshot.status.clone(),
                    diff: snapshot.diff.clone(),
                    untracked_hash: snapshot.untracked_hash.clone(),
                }
            }),
            subagent_keep_alive_ms: state.subagent_keep_alive_ms,
            last_stop,
        }
    }

    /// The runtime state the `crate::autonomous` functions work on.
    #[must_use]
    pub fn to_runtime(&self) -> AutonomousRuntimeState {
        AutonomousRuntimeState {
            enabled: self.enabled,
            continuations_used: self.continuations_used,
            started_at: self.started_at,
            limits: self.limits,
            continuation_prompt: self.continuation_prompt.clone(),
            gates: self.gates.clone(),
            gate_attempts: self
                .gate_attempts
                .iter()
                .map(|(command, attempts)| (command.clone(), *attempts))
                .collect(),
            last_gate_failure: self.last_gate_failure.clone(),
            last_gate_failure_snapshot: self.last_gate_failure_snapshot.as_ref().map(|snapshot| {
                GitWorktreeSnapshot {
                    status: snapshot.status.clone(),
                    diff: snapshot.diff.clone(),
                    untracked_hash: snapshot.untracked_hash.clone(),
                }
            }),
            subagent_keep_alive_ms: self.subagent_keep_alive_ms,
        }
    }

    /// The `/autonomous` status snapshot under the session's `budget`
    /// (`None`: no budget).
    #[must_use]
    pub fn status(&self, budget: Option<BudgetReport>) -> AgentAutonomousStatus {
        autonomous_status(&self.to_runtime(), budget)
    }
}

/// An `/autonomous` change.
#[derive(Debug, Clone, PartialEq)]
pub enum AutonomousChange {
    /// Enable (resetting the counters) and apply the given limits.
    On(AgentAutonomousConfig),
    /// Disable.
    Off,
}

/// What [`decide`] concluded for one final answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AutonomousYield {
    /// Autonomous mode does not apply.
    Inactive,
    /// Continue the run with this user text (one continuation consumed).
    Continue {
        text: String,
        nudge: AutonomousNudge,
    },
    /// Stop the run.
    Stop(AutonomousStop),
}

/// The after-turn decision over the runtime state: gates first (a pass
/// stops the run), then the limits (the run's continuations and the
/// session's `budget`), else a continuation.
pub(crate) async fn decide(
    state: &mut AutonomousRuntimeState,
    stop_reason: StopReason,
    gates: &dyn GateCommandRunner,
    budget: SessionBudget,
) -> AutonomousYield {
    let Some(stop_reason) = legacy_stop_reason(stop_reason) else {
        return AutonomousYield::Inactive;
    };
    if !state.enabled
        || matches!(
            stop_reason,
            eukhe_types::ai::StopReason::Error | eukhe_types::ai::StopReason::Aborted
        )
    {
        return AutonomousYield::Inactive;
    }
    let decision = should_autonomously_continue(state, Some(stop_reason), gates, budget).await;
    match decision.reason {
        AutonomousDecisionReason::MissingTerminalEvidence => {
            add_autonomous_continuation(state);
            AutonomousYield::Continue {
                text: autonomous_continuation_text(state),
                nudge: AutonomousNudge::Continuation,
            }
        }
        AutonomousDecisionReason::GateFailed => {
            add_autonomous_continuation(state);
            match state.last_gate_failure.as_ref() {
                Some(failure) => AutonomousYield::Continue {
                    text: build_autonomous_gate_failure_continuation(
                        failure,
                        state.gates.max_retries,
                        now_millis(),
                    ),
                    nudge: AutonomousNudge::GateFailed,
                },
                None => AutonomousYield::Continue {
                    text: autonomous_continuation_text(state),
                    nudge: AutonomousNudge::Continuation,
                },
            }
        }
        AutonomousDecisionReason::NotNeeded => AutonomousYield::Stop(AutonomousStop::GatePassed),
        AutonomousDecisionReason::LimitReached => AutonomousYield::Stop(
            autonomous_limit_reason(state, budget)
                .map_or(AutonomousStop::GateRetryExhausted, AutonomousStop::of_limit),
        ),
    }
}

/// The wire stop reason of a final answer; `None` for the reasons a
/// final answer never carries.
fn legacy_stop_reason(stop_reason: StopReason) -> Option<eukhe_types::ai::StopReason> {
    match stop_reason {
        StopReason::Stop => Some(eukhe_types::ai::StopReason::Stop),
        StopReason::Length => Some(eukhe_types::ai::StopReason::Length),
        StopReason::ToolUse => Some(eukhe_types::ai::StopReason::ToolUse),
        StopReason::Error => Some(eukhe_types::ai::StopReason::Error),
        StopReason::Aborted => Some(eukhe_types::ai::StopReason::Aborted),
        StopReason::Pending | StopReason::Deferred => None,
    }
}

/// The persisted autonomous run of `conversation_id` (the initial disabled
/// run when none was ever enabled).
///
/// # Errors
///
/// Read failures.
pub async fn autonomous_state(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<AutonomousDocState> {
    Ok(read_doc(reader, &AUTONOMOUS_DOC, conversation_id, cx)
        .await?
        .unwrap_or_else(AutonomousDocState::initial))
}

/// Apply an `/autonomous` change and append its `autonomous_status` row (old
/// `execute_autonomous`), in one commit. Enabling puts the run's limits on
/// the session's `budget`. Returns the new status.
///
/// # Errors
///
/// The budget is not limited, read or commit failures, or no such
/// conversation.
pub async fn set_autonomous(
    harness: &Harness,
    budget: &Arc<BudgetGate>,
    conversation_id: ConversationId,
    change: AutonomousChange,
    cx: &Context,
) -> SessionResult<AgentAutonomousStatus> {
    apply_autonomous(
        harness,
        budget,
        conversation_id,
        change,
        /*announce*/ true,
        cx,
    )
    .await
}

/// Enable the autonomous run from a session's startup configuration (the
/// CLI `--autonomous*` flags; TS `createAgentSession({ autonomous })`): the
/// state and the session budget's limits only, no `autonomous_status` row.
/// Returns the new status.
///
/// # Errors
///
/// The budget is not limited, read or commit failures, or no such
/// conversation.
pub async fn configure_autonomous(
    harness: &Harness,
    budget: &Arc<BudgetGate>,
    conversation_id: ConversationId,
    config: AgentAutonomousConfig,
    cx: &Context,
) -> SessionResult<AgentAutonomousStatus> {
    apply_autonomous(
        harness,
        budget,
        conversation_id,
        AutonomousChange::On(config),
        /*announce*/ false,
        cx,
    )
    .await
}

/// Put `limits` on the session's `budget` (`BudgetGate::limit`); nothing
/// when they limit nothing. Returns the budget's report.
async fn limit_budget(
    budget: &Arc<BudgetGate>,
    limits: BudgetLimits,
) -> SessionResult<Option<BudgetReport>> {
    if limits.is_unlimited() {
        return budget_report(budget).await;
    }
    let gate = Arc::clone(budget);
    tokio::task::spawn_blocking(move || gate.limit(limits))
        .await
        .map_err(SessionError::other)?
        .map(Some)
        .map_err(|error| {
            SessionError::error(format!(
                "The autonomous limits were not put on the session's budget: {error}"
            ))
        })
}

/// The note of each limit `asked` named that the session's budget kept
/// (`report` limited that dimension already, to another amount).
fn kept_limits(asked: &AgentAutonomousConfig, report: Option<&BudgetReport>) -> Vec<String> {
    let Some(report) = report else {
        return Vec::new();
    };
    let named = autonomous_budget_limits(asked);
    [
        (asked.max_turns, "maxTurns", BudgetDimension::Requests),
        (asked.max_tokens, "maxTokens", BudgetDimension::Tokens),
        (asked.timeout_ms, "timeoutMs", BudgetDimension::Time),
    ]
    .into_iter()
    .filter(|(given, _, _)| given.is_some())
    .filter_map(|(_, name, dimension)| {
        let kept = report.limits.get(dimension)?;
        let wanted = named.get(dimension);
        (wanted != Some(kept)).then(|| {
            format!(
                "The session's budget already limits {} to {kept}: {name} keeps it (/budget add raises it).",
                dimension.label()
            )
        })
    })
    .collect()
}

/// Apply `change` in one commit; `announce` appends its `autonomous_status`
/// row.
async fn apply_autonomous(
    harness: &Harness,
    budget: &Arc<BudgetGate>,
    conversation_id: ConversationId,
    change: AutonomousChange,
    announce: bool,
    cx: &Context,
) -> SessionResult<AgentAutonomousStatus> {
    let (report, notes) = match &change {
        AutonomousChange::On(config) => {
            let report = limit_budget(budget, autonomous_budget_limits(config)).await?;
            let notes = kept_limits(config, report.as_ref());
            (report, notes)
        }
        AutonomousChange::Off => (budget_report(budget).await?, Vec::new()),
    };
    conversation_of(harness, conversation_id, cx)
        .await?
        .commit(
            move |tx| async move {
                let (draft, current) = open_doc(&tx, &AUTONOMOUS_DOC, conversation_id).await?;
                let mut state = current.to_runtime();
                let last_stop = match change {
                    AutonomousChange::On(config) => {
                        set_autonomous_enabled(&mut state, true);
                        set_autonomous_limits(&mut state, &config);
                        None
                    }
                    AutonomousChange::Off => {
                        set_autonomous_enabled(&mut state, false);
                        current.last_stop
                    }
                };
                let next = AutonomousDocState::from_runtime(&state, last_stop);
                write_doc(&draft, &next)?;
                let status = next.status(report);
                if announce {
                    let details = serde_json::to_value(&status)
                        .map_err(|error| SessionError::error(error.to_string()))?;
                    let text = std::iter::once(format_autonomous_status(&status))
                        .chain(notes)
                        .collect::<Vec<_>>()
                        .join("\n");
                    let entry = custom_entry_draft(
                        AUTONOMOUS_STATUS_CUSTOM_TYPE,
                        UserContent::Text(text),
                        /*display*/ true,
                        Some(details),
                        now_millis(),
                    )?;
                    tx.append_entry(conversation_id, entry).await?;
                }
                Ok(status)
            },
            cx,
        )
        .await
}
