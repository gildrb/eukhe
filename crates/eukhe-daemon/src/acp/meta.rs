//! Namespaced `_meta` payloads for eukhe capabilities that ACP has no
//! native concept for (cwd reporting, quiescence observation, correlation).
//!
//! ACP reserves `_meta` on capability objects, notifications, and content
//! blocks so agents can carry non-standard data. Vanilla ACP clients ignore
//! these keys; a eukhe-aware client reads them. Non-standard fields
//! never appear at an ACP object root.

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

/// Reverse-domain namespace for every eukhe `_meta` payload.
pub const EUKHE_META_NAMESPACE: &str = "com.eukhe";

/// A client-requested cwd that differs from the agent's actual startup cwd.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EukheCwdMeta {
    pub requested: String,
    pub actual: String,
}

/// Observed subagent and autonomous-continuation counts at a completion
/// point, and the work whose end wakes the session (absent when nothing
/// runs): a completion that names any is not quiescent, and the prompt
/// holds until a terminal names none.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EukheQuiescenceMeta {
    pub outstanding_subagents: u64,
    pub remaining_autonomous_continuations: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub waiting_on: Option<eukhe_types::daemon::WaitingOn>,
}

/// Producer-side ordering of an update inside its prompt turn.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EukheEventPhase {
    /// Ordinary streamed work.
    #[serde(rename = "event")]
    Event,
    /// The correlated boundary in front of a prompt response.
    #[serde(rename = "responseBoundary")]
    ResponseBoundary,
    /// The final settled state after the response boundary.
    #[serde(rename = "terminalQuiescence")]
    TerminalQuiescence,
}

/// The outcome carried by a response boundary and terminal envelope. ACP
/// transport stop reasons (including `end_turn`) are never a causal
/// completion signal, so this is deliberately only `result` and `error`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EukheOutcome {
    #[serde(rename = "result")]
    Result,
    #[serde(rename = "error")]
    Error,
}

/// The eukhe payload under the `_meta` namespace key.
///
/// `prompt_turn_id` is allocated when ACP accepts a prompt, never inferred
/// from whichever prompt happens to be running when an update is delivered;
/// `0` means a session-scoped event with no prompt origin. `event_sequence`
/// is connection-wide and strictly increases for every published update.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EukheSessionMeta {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub prompt_turn_id: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub event_sequence: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub phase: Option<EukheEventPhase>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub outcome: Option<EukheOutcome>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub terminal_quiescence_expected: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cwd: Option<EukheCwdMeta>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub quiescence: Option<EukheQuiescenceMeta>,
    /// Rich kernel output reported by the python tool (attachments the cell
    /// loaded into context).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub python: Option<Value>,
    /// Set when the session's heartbeat or cron schedule changed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub heartbeats_changed: Option<bool>,
    /// The session's `/loop`: its whole status, after every change.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub r#loop: Option<eukhe_types::loop_mode::LoopStatus>,
    /// The session's budget as its `budget_update` carried it (the whole
    /// report: limits, free, held, spent, lent, the agent's phase, the
    /// deadline).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub budget: Option<eukhe_types::budget::BudgetReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub refinement: Option<EukheRefinementMeta>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub agent_message: Option<EukheAgentMessageMeta>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compaction: Option<EukheCompactionMeta>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub subagents: Option<Vec<EukheSubagentMeta>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub autonomous: Option<EukheAutonomousMeta>,
}

/// The outcome of one continual-harness refinement run.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EukheRefinementMeta {
    pub status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub summary: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub changes: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// An agent-to-agent message sent from inside a kernel cell.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EukheAgentMessageMeta {
    pub tool_call_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub delivery_status: Option<String>,
}

/// One compaction that ran during the session.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EukheCompactionMeta {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tokens_before: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub summary: Option<String>,
}

/// One RLM subagent roster row.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EukheSubagentMeta {
    pub id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_name: Option<String>,
    pub status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub model: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub depth: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub token_count: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// Autonomous-mode accounting surfaced with a turn's completion: whether
/// the run is on, the continuations it made, and why it stopped.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EukheAutonomousMeta {
    pub enabled: bool,
    pub continuations_used: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub limit_reason: Option<String>,
}

/// The `_meta.autonomous` accounting for a completion update. The
/// daemon-attached settlement's accounting.
pub fn autonomous_meta(
    status: &eukhe_core::autonomous::AgentAutonomousStatus,
) -> EukheAutonomousMeta {
    EukheAutonomousMeta {
        enabled: status.enabled,
        continuations_used: status.continuations_used,
        limit_reason: status
            .last_stop
            .map(|stop| stop.describe(status.budget.as_ref())),
    }
}

/// Map a finished turn onto an ACP stop reason. Precedence: an explicit
/// cancel, then an enabled autonomous run the budget stopped (the budget
/// short in tokens maps to `max_tokens`, in anything else to
/// `max_turn_requests`), then the turn's final assistant stop reason
/// (#3363): a per-call output-token truncation (`StopReason::Length`) is
/// an honest `max_tokens`, so `end_turn` stays reserved for a finished
/// answer; a final request that failed while the session's budget admits
/// no more work was the budget's refusal, and ends at that limit
/// ([`budget_stop_reason`]); every other final reason (and none) keeps
/// `end_turn`.
pub fn acp_stop_reason_for_status(
    cancelled: bool,
    status: Option<&eukhe_core::autonomous::AgentAutonomousStatus>,
    assistant_stop_reason: Option<eukhe_types::ai::StopReason>,
) -> super::types::AcpStopReason {
    use eukhe_core::autonomous::AutonomousStop;
    use eukhe_types::ai::StopReason;
    if cancelled {
        return super::types::AcpStopReason::Cancelled;
    }
    let budget = status.and_then(|status| status.budget.as_ref());
    match status
        .filter(|status| status.enabled)
        .and_then(|status| status.last_stop)
    {
        Some(AutonomousStop::Budget) => limit_stop_reason(budget.and_then(|report| report.short)),
        Some(AutonomousStop::Checks(_) | AutonomousStop::NoProgress { .. }) | None => {
            match assistant_stop_reason {
                Some(StopReason::Length) => super::types::AcpStopReason::MaxTokens,
                Some(StopReason::Error) => {
                    budget_stop_reason(budget).unwrap_or(super::types::AcpStopReason::EndTurn)
                }
                Some(StopReason::Stop | StopReason::ToolUse | StopReason::Aborted) | None => {
                    super::types::AcpStopReason::EndTurn
                }
            }
        }
    }
}

/// The stop reason of a turn that failed because the session's budget
/// admits no more work (its phase left `Working`, `budget` is its report):
/// the limit of the dimension that ran short. `None` while the budget
/// admits work, or without one.
pub fn budget_stop_reason(
    budget: Option<&eukhe_types::budget::BudgetReport>,
) -> Option<super::types::AcpStopReason> {
    use eukhe_core::autonomous::SessionBudget;
    match SessionBudget::of(budget) {
        SessionBudget::Working => None,
        SessionBudget::Short(short) => Some(limit_stop_reason(short)),
    }
}

/// The ACP stop reason of a budget that ran short in `short`: tokens are
/// `max_tokens`; every other dimension (or none recorded)
/// `max_turn_requests`.
fn limit_stop_reason(
    short: Option<eukhe_types::budget::BudgetDimension>,
) -> super::types::AcpStopReason {
    use eukhe_types::budget::BudgetDimension;
    match short {
        Some(BudgetDimension::Tokens) => super::types::AcpStopReason::MaxTokens,
        Some(
            BudgetDimension::Cost
            | BudgetDimension::Time
            | BudgetDimension::ToolCalls
            | BudgetDimension::Requests,
        )
        | None => super::types::AcpStopReason::MaxTurnRequests,
    }
}

/// Wrap a eukhe payload in its reverse-domain `_meta` envelope.
pub fn eukhe_meta(payload: &EukheSessionMeta) -> Value {
    json!({ EUKHE_META_NAMESPACE: payload })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn meta_wraps_under_the_namespace_key() {
        let wrapped = eukhe_meta(&EukheSessionMeta {
            prompt_turn_id: Some(1),
            event_sequence: Some(2),
            phase: Some(EukheEventPhase::ResponseBoundary),
            outcome: Some(EukheOutcome::Error),
            ..Default::default()
        });
        assert_eq!(
            wrapped,
            json!({ "com.eukhe": {
                "promptTurnId": 1,
                "eventSequence": 2,
                "phase": "responseBoundary",
                "outcome": "error",
            }})
        );
    }

    #[test]
    fn acp_stop_reason_keeps_cancel_and_run_limits_first() {
        // The explicit cancel and a run the budget stopped stay ahead of
        // the final assistant stop reason (the e2e covers the
        // disabled-status and below-mapping cases).
        use super::super::types::AcpStopReason;
        use eukhe_core::autonomous::{AgentAutonomousStatus, AutonomousStop};
        use eukhe_types::ai::StopReason;
        use eukhe_types::budget::{BudgetDimension, BudgetPhase, BudgetReport};
        // An enabled run whose session budget ran short in `short` (and
        // stopped it then).
        let status = |enabled: bool, short: Option<BudgetDimension>| AgentAutonomousStatus {
            enabled,
            continuations_used: 0,
            started_at: None,
            last_stop: short.map(|_| AutonomousStop::Budget),
            budget: Some(BudgetReport {
                phase: if short.is_some() {
                    BudgetPhase::WrapUp
                } else {
                    BudgetPhase::Working
                },
                short,
                ..BudgetReport::default()
            }),
        };
        let reason = |cancelled, status: AgentAutonomousStatus, stop| {
            acp_stop_reason_for_status(cancelled, Some(&status), Some(stop))
        };
        assert_eq!(
            [
                reason(true, status(false, None), StopReason::Length),
                reason(false, status(true, None), StopReason::Length),
                reason(
                    false,
                    status(true, Some(BudgetDimension::Requests)),
                    StopReason::Length
                ),
                reason(
                    false,
                    status(true, Some(BudgetDimension::Tokens)),
                    StopReason::Stop
                ),
            ],
            [
                AcpStopReason::Cancelled,
                AcpStopReason::MaxTokens,
                AcpStopReason::MaxTurnRequests,
                AcpStopReason::MaxTokens,
            ]
        );
    }

    #[test]
    fn quiescence_serializes_camel_case() {
        let wrapped = eukhe_meta(&EukheSessionMeta {
            quiescence: Some(EukheQuiescenceMeta {
                outstanding_subagents: 0,
                remaining_autonomous_continuations: 0,
                waiting_on: None,
            }),
            ..Default::default()
        });
        assert_eq!(
            wrapped[EUKHE_META_NAMESPACE]["quiescence"],
            json!({ "outstandingSubagents": 0, "remainingAutonomousContinuations": 0 })
        );
    }
}
