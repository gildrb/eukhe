//! Autonomous mode on the Harness: the run state lives in the
//! `eukhe.autonomous` conversation document (the old daemon kept it in
//! process memory), settled responses are accounted in `after_response`, and
//! each final answer asks [`decide`] whether the run continues (the old
//! `ShellAutonomousDriver::after_turn`, with today's limits and gates from
//! `crate::autonomous`).

use std::collections::BTreeMap;

use super::ops::conversation_of;
use eukhe_chord::context::Context;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReader};
use eukhe_types::pi_ai::{StopReason, Usage, UserContent};
use serde::{Deserialize, Serialize};

use super::docs::{open_doc, read_doc, write_doc, AUTONOMOUS_DOC};
use crate::autonomous::{
    add_autonomous_continuation, autonomous_continuation_text, autonomous_limit_reason,
    autonomous_status, build_autonomous_gate_failure_continuation, create_autonomous_runtime_state,
    now_millis, set_autonomous_enabled, set_autonomous_limits, should_autonomously_continue,
    AgentAutonomousConfig, AgentAutonomousGateFailure, AgentAutonomousStatus,
    AutonomousDecisionReason, AutonomousLimitReason, AutonomousLimits, AutonomousRuntimeState,
    AutonomousStopReason, GateCommandRunner, GitWorktreeSnapshot, NormalizedGateConfig,
    AUTONOMOUS_STATUS_CUSTOM_TYPE,
};
use crate::durable::entries::custom_entry_draft;
use crate::slash_command_args::format_autonomous_status;

/// The persisted autonomous run (the old `AutonomousRuntimeState` plus the
/// last stop decision).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AutonomousDocState {
    pub enabled: bool,
    pub continuations_used: u64,
    pub turns_used: u64,
    pub tokens_used: u64,
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

/// Why an autonomous run stopped (old `AutonomousStopReason`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum AutonomousStop {
    GatePassed,
    GateRetryExhausted,
    MaxContinuations,
    MaxTurns,
    MaxTokens,
    TimeoutMs,
}

impl AutonomousStop {
    /// The old driver's stop reason.
    #[must_use]
    pub fn reason(self) -> AutonomousStopReason {
        match self {
            Self::GatePassed => AutonomousStopReason::GatePassed,
            Self::GateRetryExhausted => AutonomousStopReason::GateRetryExhausted,
            Self::MaxContinuations => {
                AutonomousStopReason::Limit(AutonomousLimitReason::MaxContinuations)
            }
            Self::MaxTurns => AutonomousStopReason::Limit(AutonomousLimitReason::MaxTurns),
            Self::MaxTokens => AutonomousStopReason::Limit(AutonomousLimitReason::MaxTokens),
            Self::TimeoutMs => AutonomousStopReason::Limit(AutonomousLimitReason::TimeoutMs),
        }
    }

    fn of_limit(reason: AutonomousLimitReason) -> Self {
        match reason {
            AutonomousLimitReason::MaxContinuations => Self::MaxContinuations,
            AutonomousLimitReason::MaxTurns => Self::MaxTurns,
            AutonomousLimitReason::MaxTokens => Self::MaxTokens,
            AutonomousLimitReason::TimeoutMs => Self::TimeoutMs,
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
            turns_used: state.turns_used,
            tokens_used: state.tokens_used,
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
            turns_used: self.turns_used,
            tokens_used: self.tokens_used,
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

    /// The `/autonomous` status snapshot.
    #[must_use]
    pub fn status(&self) -> AgentAutonomousStatus {
        autonomous_status(&self.to_runtime())
    }

    /// Account one settled response (old `account_message` +
    /// `add_autonomous_usage`): one turn, and input + output + cache-write
    /// tokens (`crate::autonomous::autonomous_token_delta`).
    pub(crate) fn account(&mut self, usage: &Usage) {
        if !self.enabled {
            return;
        }
        self.turns_used = self.turns_used.saturating_add(1);
        self.tokens_used = self.tokens_used.saturating_add(
            usage
                .input
                .saturating_add(usage.output)
                .saturating_add(usage.cache_write),
        );
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
    Continue(String),
    /// Stop the run.
    Stop(AutonomousStop),
}

/// The old `ShellAutonomousDriver::after_turn` over the runtime state: gates
/// first (a pass stops the run), then the limits, else a continuation.
pub(crate) async fn decide(
    state: &mut AutonomousRuntimeState,
    stop_reason: StopReason,
    gates: &dyn GateCommandRunner,
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
    let decision = should_autonomously_continue(state, Some(stop_reason), gates).await;
    match decision.reason {
        AutonomousDecisionReason::MissingTerminalEvidence => {
            add_autonomous_continuation(state);
            AutonomousYield::Continue(autonomous_continuation_text(state))
        }
        AutonomousDecisionReason::GateFailed => {
            add_autonomous_continuation(state);
            let text = state.last_gate_failure.as_ref().map_or_else(
                || autonomous_continuation_text(state),
                |failure| {
                    build_autonomous_gate_failure_continuation(
                        failure,
                        state.gates.max_retries,
                        now_millis(),
                    )
                },
            );
            AutonomousYield::Continue(text)
        }
        AutonomousDecisionReason::NotNeeded => AutonomousYield::Stop(AutonomousStop::GatePassed),
        AutonomousDecisionReason::LimitReached => AutonomousYield::Stop(
            autonomous_limit_reason(state, now_millis())
                .map_or(AutonomousStop::GateRetryExhausted, AutonomousStop::of_limit),
        ),
    }
}

/// The old engine's stop reason of a final answer; `None` for the reasons a
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
/// `execute_autonomous`), in one commit. Returns the new status.
///
/// # Errors
///
/// Read or commit failures, or no such conversation.
pub async fn set_autonomous(
    harness: &Harness,
    conversation_id: ConversationId,
    change: AutonomousChange,
    cx: &Context,
) -> SessionResult<AgentAutonomousStatus> {
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
                let status = next.status();
                let details = serde_json::to_value(&status)
                    .map_err(|error| SessionError::error(error.to_string()))?;
                let entry = custom_entry_draft(
                    AUTONOMOUS_STATUS_CUSTOM_TYPE,
                    UserContent::Text(format_autonomous_status(&status)),
                    /*display*/ true,
                    Some(details),
                    now_millis(),
                )?;
                tx.append_entry(conversation_id, entry).await?;
                Ok(status)
            },
            cx,
        )
        .await
}
