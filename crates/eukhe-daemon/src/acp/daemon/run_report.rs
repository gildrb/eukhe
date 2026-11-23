//! `_eukhe/run_report`: what one prompt turn left (its answer, the checks
//! and their label, the irreversible effects that ran, the steps a restart
//! treated as not run, the work left), sent before the turn's
//! `session/prompt` response, for every turn.

use std::collections::HashSet;

use eukhe_types::acceptance::{AcceptanceCheck, AcceptanceState};
use eukhe_types::daemon::DaemonCommand;
use eukhe_types::effects::{RanEffect, UnknownEffect};
use serde_json::{json, Map, Value};

use super::extensions::{effect_ledgers, reply, ExtensionError};
use super::{jsonrpc, DaemonLink};
use crate::acp::wire_events::check_text;

/// The notification method.
pub(super) const METHOD: &str = "_eukhe/run_report";

/// The effect ledgers' ids before a turn: an entry the turn's end shows and
/// these lack is the turn's.
pub(super) struct EffectsBefore {
    ran: HashSet<String>,
    unknown: HashSet<String>,
}

/// The ledgers' ids now; `None` when they do not read.
pub(super) async fn effects_before(link: &DaemonLink, session: &str) -> Option<EffectsBefore> {
    let (ran, unknown) = effect_ledgers(link, session).await.ok()?;
    Some(EffectsBefore {
        ran: ran.effects.into_iter().map(|effect| effect.id).collect(),
        unknown: unknown
            .effects
            .into_iter()
            .map(|effect| effect.id)
            .collect(),
    })
}

/// What the report tells of one turn.
pub(super) struct Turn<'a> {
    pub(super) acp_session_id: &'a str,
    pub(super) daemon_session_id: &'a str,
    pub(super) turn_id: u64,
    /// The turn's `session/prompt` reply frame.
    pub(super) reply: &'a Value,
    /// The text of the turn's last assistant message.
    pub(super) answer: Option<String>,
    pub(super) before: Option<EffectsBefore>,
}

/// The parts of a report that did not read (the daemon went away, a
/// command failed): named in `unreadable`, never filled with a guess.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Part {
    Acceptance,
    Effects,
    Left,
}

impl Part {
    fn name(self) -> &'static str {
        match self {
            Part::Acceptance => "acceptance",
            Part::Effects => "effects",
            Part::Left => "left",
        }
    }
}

/// The report's notification frame.
pub(super) async fn report(link: &DaemonLink, turn: Turn<'_>) -> Value {
    let mut unreadable: Vec<Part> = Vec::new();
    let acceptance = reply::<AcceptanceState>(
        link,
        DaemonCommand::GetAcceptance {
            id: None,
            active_session_id: turn.daemon_session_id.to_string(),
            rest: Map::default(),
        },
    )
    .await
    .inspect_err(|_| unreadable.push(Part::Acceptance))
    .ok();
    let effects = match (
        turn.before.as_ref(),
        effect_ledgers(link, turn.daemon_session_id).await,
    ) {
        (Some(before), Ok((ran, unknown))) => {
            Some(new_effects(before, ran.effects, unknown.effects))
        }
        (None, _) | (_, Err(_)) => {
            unreadable.push(Part::Effects);
            None
        }
    };
    let left = work_left(link, turn.daemon_session_id)
        .await
        .inspect_err(|_| unreadable.push(Part::Left))
        .ok();
    let (stop_reason, error) = turn_end(turn.reply);
    let (ran, unknown) = effects.unwrap_or_default();
    let mut params = json!({
        "sessionId": turn.acp_session_id,
        "promptTurnId": turn.turn_id,
        "stopReason": stop_reason,
        "answer": turn.answer,
        "label": acceptance.as_ref().map(|state| state.label.slug()),
        "certified": acceptance.as_ref().is_some_and(|state| state.label.passed()),
        "checks": acceptance.as_ref().map(|state| state.checks.iter().map(check_row).collect::<Vec<_>>()).unwrap_or_default(),
        "ran": ran,
        "unknown": unknown,
        "left": left.flatten().unwrap_or_default(),
    });
    if let Some(error) = error {
        params["error"] = json!(error);
    }
    if !unreadable.is_empty() {
        params["unreadable"] = json!(unreadable
            .iter()
            .map(|part| part.name())
            .collect::<Vec<_>>());
    }
    jsonrpc::notification(METHOD, &params)
}

/// The turn's stop reason, or why it failed, from its reply frame.
fn turn_end(reply: &Value) -> (Value, Option<String>) {
    match (reply.get("result"), reply.get("error")) {
        (Some(result), _) => (
            result.get("stopReason").cloned().unwrap_or(Value::Null),
            None,
        ),
        (None, Some(error)) => (
            Value::Null,
            Some(
                error["data"]["details"]
                    .as_str()
                    .or_else(|| error["message"].as_str())
                    .unwrap_or("the turn failed")
                    .to_string(),
            ),
        ),
        (None, None) => (Value::Null, None),
    }
}

/// The ledger entries the turn added.
fn new_effects(
    before: &EffectsBefore,
    ran: Vec<RanEffect>,
    unknown: Vec<UnknownEffect>,
) -> (Vec<RanEffect>, Vec<UnknownEffect>) {
    (
        ran.into_iter()
            .filter(|effect| !before.ran.contains(&effect.id))
            .collect(),
        unknown
            .into_iter()
            .filter(|effect| !before.unknown.contains(&effect.id))
            .collect(),
    )
}

/// One check's row: what it asks and its last verdict.
fn check_row(check: &AcceptanceCheck) -> Value {
    let kind = serde_json::to_value(&check.spec)
        .ok()
        .and_then(|spec| spec.get("kind").cloned())
        .unwrap_or(Value::Null);
    json!({
        "kind": kind,
        "text": check_text(&check.spec),
        "verdict": check.result.as_ref().map(|result| result.verdict.slug()),
        "summary": check.result.as_ref().map(|result| result.summary.clone()),
    })
}

/// What the session's last run found left (`get_state`'s `left`).
async fn work_left(
    link: &DaemonLink,
    session: &str,
) -> Result<Option<Vec<String>>, ExtensionError> {
    let state = reply::<Value>(
        link,
        DaemonCommand::GetState {
            id: None,
            active_session_id: session.to_string(),
            rest: Map::default(),
        },
    )
    .await?;
    serde_json::from_value(state.get("left").cloned().unwrap_or(Value::Null))
        .map_err(ExtensionError::Decode)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_turn_end_reads_the_reply() {
        assert_eq!(
            [
                turn_end(&json!({ "id": 1, "result": { "stopReason": "cancelled" } })),
                turn_end(
                    &json!({ "id": 1, "error": { "code": -32603, "message": "Internal error",
                    "data": { "details": "eukhe turn failed: no_model" } } })
                ),
            ],
            [
                (json!("cancelled"), None),
                (Value::Null, Some("eukhe turn failed: no_model".to_string())),
            ]
        );
    }
}
