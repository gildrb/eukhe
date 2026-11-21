//! Autonomous mode on the Harness: the run state lives in the
//! `eukhe.autonomous` conversation document, and each final answer asks
//! the compiled core ([`decide`], `eukhe_bend::rules::autonomous`) what
//! the run does, from the checks' outcome at that answer, the session's
//! budget and, for a claim that passed, the final-answer judge's reading
//! of the answer (a passing check does not end a run whose answer states
//! work left). Turning a run on sets its checks
//! (`crate::durable::acceptance`): the intent check when it has none, and
//! the commands of the removed gates; the removed own limits become the
//! session's budget limits.

use std::path::Path;
use std::sync::Arc;

use super::ops::{budget_report, conversation_of};
use eukhe_bend::rules::autonomous::{self, Answer, Budget, Cause, Facts, Mode, Step};
use eukhe_bend::rules::verify::Label;
use eukhe_bend::rules::work_left::Reading;
use eukhe_chord::context::Context;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReader};
use eukhe_types::acceptance::AcceptanceLabel;
use eukhe_types::budget::{BudgetReport, RunLimits};
use eukhe_types::input_origin::AutonomousNudge;
use eukhe_types::pi_ai::{StopReason, UserContent};
use serde::{Deserialize, Serialize};

use super::docs::{open_doc, read_doc, write_doc, AUTONOMOUS_DOC};
use crate::autonomous::{
    autonomous_continuation_text, now_millis, AgentAutonomousConfig, AgentAutonomousStatus,
    AutonomousStop, AUTONOMOUS_STATUS_CUSTOM_TYPE, DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT,
};
use crate::durable::acceptance::{autonomous_checks, AnswerChecks};
use crate::durable::budget::BudgetGate;
use crate::durable::entries::custom_entry_draft;
use crate::slash_command_args::format_autonomous_status;

/// The persisted autonomous run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AutonomousDocState {
    pub enabled: bool,
    /// The continuations the run made with its prompt.
    pub continuations_used: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub started_at: Option<u64>,
    pub continuation_prompt: String,
    /// Why the last run stopped; cleared when a run is enabled.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_stop: Option<AutonomousStop>,
}

impl AutonomousDocState {
    /// A run that is off (the document's initial value).
    #[must_use]
    pub fn initial() -> Self {
        Self {
            enabled: false,
            continuations_used: 0,
            started_at: None,
            continuation_prompt: DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT.to_owned(),
            last_stop: None,
        }
    }

    /// The `/auto` status under the session's `budget` (`None`: no
    /// budget).
    #[must_use]
    pub fn status(&self, budget: Option<BudgetReport>) -> AgentAutonomousStatus {
        AgentAutonomousStatus {
            enabled: self.enabled,
            continuations_used: self.continuations_used,
            started_at: self.started_at,
            last_stop: self.last_stop,
            budget,
        }
    }

    /// The run turned on with `config`'s prompt: counters reset.
    fn on(&self, config: &AgentAutonomousConfig) -> Self {
        Self {
            enabled: true,
            continuations_used: 0,
            started_at: Some(now_millis()),
            continuation_prompt: config
                .continuation_prompt
                .as_deref()
                .map(str::trim)
                .filter(|text| !text.is_empty())
                .unwrap_or(&self.continuation_prompt)
                .to_owned(),
            last_stop: None,
        }
    }

    /// The run turned off, its last stop kept.
    fn off(&self) -> Self {
        Self {
            enabled: false,
            started_at: None,
            ..self.clone()
        }
    }
}

/// An `/auto` change.
#[derive(Debug, Clone, PartialEq)]
pub enum AutonomousChange {
    /// Turn on (resetting the counters) with this configuration.
    On(AgentAutonomousConfig),
    /// Turn off.
    Off,
}

/// What [`decide`] concluded for one final answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AutonomousYield {
    /// The run is off, the answer broke, or the checks' return continues
    /// the run: the run adds nothing.
    Inactive,
    /// Continue the run with this user text.
    Continue {
        text: String,
        nudge: AutonomousNudge,
        next: AutonomousDocState,
    },
    /// Stop the run.
    Stop {
        stop: AutonomousStop,
        next: AutonomousDocState,
    },
    /// The claim passed and the budget admits work: the final-answer
    /// judge's reading decides; [`decide`] again with it.
    Ask,
    /// The claim passed but the final answer states work left: continue
    /// the run with the work the answer left.
    Finish { next: AutonomousDocState },
}

/// How a final answer ended, for the rule; `None` for the reasons a
/// final answer never carries.
fn answer_of(stop_reason: StopReason) -> Option<Answer> {
    match stop_reason {
        StopReason::Stop | StopReason::Length | StopReason::ToolUse => Some(Answer::Settled),
        StopReason::Error | StopReason::Aborted => Some(Answer::Broken),
        StopReason::Pending | StopReason::Deferred => None,
    }
}

/// The acceptance label of the core's `label`.
fn acceptance_label(label: Label) -> AcceptanceLabel {
    match label {
        Label::Verified => AcceptanceLabel::Verified,
        Label::Failed => AcceptanceLabel::Failed,
        Label::Unverified => AcceptanceLabel::Unverified,
        Label::Passed => AcceptanceLabel::ChecksPassedUnconfined,
    }
}

/// The step of `state` at a final answer that ended with `stop_reason`,
/// with the checks' outcome `checks`, the session's `budget` and the
/// final-answer judge's `reading` of the answer: the compiled core's
/// decision. A run its checks stop keeps the label the checks ended the
/// claim with.
///
/// # Errors
///
/// A compiled-core failure.
pub(crate) fn decide(
    state: &AutonomousDocState,
    stop_reason: StopReason,
    checks: AnswerChecks,
    budget: Budget,
    reading: Reading,
) -> SessionResult<AutonomousYield> {
    let Some(answer) = answer_of(stop_reason) else {
        return Ok(AutonomousYield::Inactive);
    };
    let facts = Facts {
        mode: if state.enabled {
            Mode::Autonomous
        } else {
            Mode::Attended
        },
        answer,
        checks: checks.core(),
        budget,
        reading,
    };
    let continued = || AutonomousDocState {
        continuations_used: state.continuations_used.saturating_add(1),
        ..state.clone()
    };
    Ok(
        match autonomous::step(facts).map_err(SessionError::other)? {
            Step::Off | Step::Hold => AutonomousYield::Inactive,
            Step::Continue => AutonomousYield::Continue {
                text: autonomous_continuation_text(&state.continuation_prompt),
                nudge: AutonomousNudge::Continuation,
                next: continued(),
            },
            Step::Stop(cause) => {
                let stop = match cause {
                    Cause::Checks(label) => AutonomousStop::Checks(match checks {
                        AnswerChecks::Ended(ended) => ended,
                        AnswerChecks::Unchecked | AnswerChecks::Returned => acceptance_label(label),
                    }),
                    Cause::Budget => AutonomousStop::Budget,
                };
                AutonomousYield::Stop {
                    stop,
                    next: AutonomousDocState {
                        last_stop: Some(stop),
                        ..state.clone()
                    },
                }
            }
            Step::Ask => AutonomousYield::Ask,
            Step::Finish => AutonomousYield::Finish { next: continued() },
        },
    )
}

/// The persisted autonomous run of `conversation_id` (the initial run
/// that is off when none was ever enabled).
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

/// Apply an `/auto` change and append its `autonomous_status` row, in one
/// commit; the principal's change sets the run's checks and limits.
/// Returns the new status, with the session's `budget`.
///
/// # Errors
///
/// Read or commit failures, or no such conversation.
pub async fn set_autonomous(
    harness: &Harness,
    budget: &Arc<BudgetGate>,
    conversation_id: ConversationId,
    change: AutonomousChange,
    cwd: &Path,
    cx: &Context,
) -> SessionResult<AgentAutonomousStatus> {
    apply_autonomous(
        harness,
        budget,
        conversation_id,
        change,
        Some(cwd),
        Announce::Row,
        cx,
    )
    .await
}

/// Turn the autonomous run on from a session's startup configuration (the
/// CLI flags, a client's create config): the state, the checks and the
/// limits, no `autonomous_status` row. Returns the new status.
///
/// # Errors
///
/// Read or commit failures, or no such conversation.
pub async fn configure_autonomous(
    harness: &Harness,
    budget: &Arc<BudgetGate>,
    conversation_id: ConversationId,
    config: AgentAutonomousConfig,
    cwd: &Path,
    cx: &Context,
) -> SessionResult<AgentAutonomousStatus> {
    apply_autonomous(
        harness,
        budget,
        conversation_id,
        AutonomousChange::On(config),
        Some(cwd),
        Announce::Quiet,
        cx,
    )
    .await
}

/// Turn the harness's own continuation on or off (autoresearch's loop):
/// the state only. Its checks and limits stay as they are: the loop has
/// its own end.
///
/// # Errors
///
/// Read or commit failures, or no such conversation.
pub(crate) async fn set_internal_autonomous(
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
        None,
        Announce::Row,
        cx,
    )
    .await
}

/// Whether a change appends its `autonomous_status` row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Announce {
    Row,
    Quiet,
}

/// The principal's terms of turning a run on: the checks (in `cwd`) and
/// the limits the configuration asks.
async fn principal_terms(
    harness: &Harness,
    budget: &Arc<BudgetGate>,
    conversation_id: ConversationId,
    config: &AgentAutonomousConfig,
    cwd: &Path,
    cx: &Context,
) -> SessionResult<()> {
    autonomous_checks(
        harness,
        conversation_id,
        config.gate_checks(),
        config.max_returns(),
        cwd,
        cx,
    )
    .await?;
    set_run_limits(budget, config.limits()).await
}

/// Set `limits` on the run the principal starts next, over what was set
/// for it before (the create's or the flags' budget); unset limits change
/// nothing.
///
/// # Errors
///
/// The ledger's failures.
pub async fn set_run_limits(budget: &Arc<BudgetGate>, limits: RunLimits) -> SessionResult<()> {
    if limits.is_unset() {
        return Ok(());
    }
    let gate = Arc::clone(budget);
    tokio::task::spawn_blocking(move || gate.set_next(limits))
        .await
        .map_err(SessionError::other)?
        .map_err(SessionError::other)?;
    Ok(())
}

/// Apply `change` in one commit; `cwd` (the principal's change) sets the
/// run's checks and limits first; `announce` appends its
/// `autonomous_status` row, with the configuration's deprecation note.
async fn apply_autonomous(
    harness: &Harness,
    budget: &Arc<BudgetGate>,
    conversation_id: ConversationId,
    change: AutonomousChange,
    cwd: Option<&Path>,
    announce: Announce,
    cx: &Context,
) -> SessionResult<AgentAutonomousStatus> {
    let note = match (&change, cwd) {
        (AutonomousChange::On(config), Some(cwd)) => {
            principal_terms(harness, budget, conversation_id, config, cwd, cx).await?;
            config.deprecation_note()
        }
        (AutonomousChange::On(_) | AutonomousChange::Off, _) => None,
    };
    let report = budget_report(budget).await?;
    conversation_of(harness, conversation_id, cx)
        .await?
        .commit(
            move |tx| async move {
                let (draft, current) = open_doc(&tx, &AUTONOMOUS_DOC, conversation_id).await?;
                let next = match &change {
                    AutonomousChange::On(config) => current.on(config),
                    AutonomousChange::Off => current.off(),
                };
                write_doc(&draft, &next)?;
                let status = next.status(report);
                match announce {
                    Announce::Row => {
                        let details = serde_json::to_value(&status)
                            .map_err(|error| SessionError::error(error.to_string()))?;
                        let text = match &note {
                            Some(note) => {
                                format!("{}\n\n{note}", format_autonomous_status(&status))
                            }
                            None => format_autonomous_status(&status),
                        };
                        let entry = custom_entry_draft(
                            AUTONOMOUS_STATUS_CUSTOM_TYPE,
                            UserContent::Text(text),
                            /*display*/ true,
                            Some(details),
                            now_millis(),
                        )?;
                        tx.append_entry(conversation_id, entry).await?;
                    }
                    Announce::Quiet => {}
                }
                Ok(status)
            },
            cx,
        )
        .await
}

#[cfg(test)]
mod tests {
    use super::*;

    fn on() -> AutonomousDocState {
        AutonomousDocState::initial().on(&AgentAutonomousConfig::default())
    }

    /// The core's step reaches the run: a continuation counts, a stop is
    /// recorded with its cause (the label the checks ended the claim with,
    /// not certified included), a return or a broken answer adds nothing; a
    /// passing claim asks for the final-answer judge's reading, goes on
    /// (counted) when the answer states work left and stops when it states
    /// none.
    #[test]
    fn the_core_decides_each_final_answer() {
        let run = on();
        let passed = AnswerChecks::Ended(AcceptanceLabel::ChecksPassedNotCertified);
        let got = [
            decide(
                &run,
                StopReason::Stop,
                AnswerChecks::Unchecked,
                Budget::Working,
                Reading::Unread,
            ),
            decide(
                &run,
                StopReason::Stop,
                AnswerChecks::Returned,
                Budget::Working,
                Reading::Unread,
            ),
            decide(
                &run,
                StopReason::Stop,
                passed,
                Budget::Working,
                Reading::Finished,
            ),
            decide(
                &run,
                StopReason::ToolUse,
                AnswerChecks::Unchecked,
                Budget::Short,
                Reading::Unread,
            ),
            decide(
                &run,
                StopReason::Error,
                AnswerChecks::Unchecked,
                Budget::Working,
                Reading::Unread,
            ),
            decide(
                &AutonomousDocState::initial(),
                StopReason::Stop,
                AnswerChecks::Unchecked,
                Budget::Working,
                Reading::Unread,
            ),
            decide(
                &run,
                StopReason::Stop,
                passed,
                Budget::Working,
                Reading::Unread,
            ),
            decide(
                &run,
                StopReason::Stop,
                passed,
                Budget::Working,
                Reading::Left,
            ),
        ]
        .map(Result::unwrap);
        let stopped = |stop| AutonomousYield::Stop {
            stop,
            next: AutonomousDocState {
                last_stop: Some(stop),
                ..run.clone()
            },
        };
        let counted = AutonomousDocState {
            continuations_used: 1,
            ..run.clone()
        };
        assert_eq!(
            got,
            [
                AutonomousYield::Continue {
                    text: autonomous_continuation_text(DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT),
                    nudge: AutonomousNudge::Continuation,
                    next: counted.clone(),
                },
                AutonomousYield::Inactive,
                stopped(AutonomousStop::Checks(
                    AcceptanceLabel::ChecksPassedNotCertified
                )),
                stopped(AutonomousStop::Budget),
                AutonomousYield::Inactive,
                AutonomousYield::Inactive,
                AutonomousYield::Ask,
                AutonomousYield::Finish { next: counted },
            ]
        );
    }
}
