//! The autonomous extension's conversation documents and their typed
//! read/write helpers.
//!
//! - `eukhe.goal.loop`: continuation bookkeeping that makes the hooks
//!   idempotent across a crash rerun (the last `on_yield` decision, keyed
//!   by the generation task), and the autonomous run's progress check. The
//!   kind keeps the name the sessions already hold.
//! - `eukhe.autonomous`: the autonomous run state (see `run.rs`).
//!
//! The removed goal's `eukhe.goal` records stay in old sessions as records
//! no definition reads.

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::delta::Draft;
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use eukhe_durable::documents::{
    CallbackError, ConversationDoc, DocDefinition, DocToken, SingletonDocToken,
};
use eukhe_durable::harness::json::assign_json;
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::types::{
    ConversationId, DocumentReader, DocumentReaderExt, LatestFork, SubmissionId, TaskId,
};
use eukhe_types::input_origin::InputOrigin;
use serde::{Deserialize, Serialize};

use super::run::AutonomousDocState;
use crate::autonomous::DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT;

/// Version 1 recorded a continuation without its origin. Versions 1 and 2
/// could record the removed no-progress backoff (`{"type":"wait","until":
/// ms}`). The record only replays a decision on a crash rerun, so the
/// migration drops such a record and the rerun decides again. Versions 1
/// to 3 held the removed goal's progress check and the generation it last
/// accounted: both are dropped, so the run's progress check starts its own
/// count.
fn migrate_loop(value: &JsonObject, from: u64) -> Result<LoopState, CallbackError> {
    let mut value = value.clone();
    let outcome = value
        .get("yield")
        .and_then(|record| record.get("outcome"))
        .and_then(|outcome| outcome.get("type"))
        .and_then(JsonValue::as_str);
    if outcome == Some("wait") || (from == 1 && outcome == Some("continue")) {
        value.remove("yield");
    }
    value.remove("progress");
    value.remove("accounted");
    Ok(from_json(&JsonValue::Object(Arc::new(value)))?)
}

/// Continuation bookkeeping of one conversation; a fork starts empty.
pub(crate) static LOOP_DOC: ConversationDoc<LoopState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.goal.loop",
        version: 4,
        initial: LoopState::default,
        migrate: Some(migrate_loop),
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.goal.loop has a valid version"),
};

/// Version 1 held the removed own limits (turns, tokens, time, the
/// continuation cap) and gates with their counts: they are dropped (the
/// budget and the checks hold those terms now), and a last stop by a gate
/// or a limit reads as the checks' or the budget's.
fn migrate_autonomous(value: &JsonObject, _from: u64) -> Result<AutonomousDocState, CallbackError> {
    let old: serde_json::Value = from_json(&JsonValue::Object(Arc::new(value.clone())))?;
    let last_stop = match old.get("lastStop").and_then(serde_json::Value::as_str) {
        Some("gatePassed") => serde_json::json!({ "checks": "checks_passed_unconfined" }),
        Some("gateRetryExhausted") => serde_json::json!({ "checks": "failed" }),
        Some(_) => serde_json::json!("budget"),
        None => serde_json::Value::Null,
    };
    let mut state = serde_json::json!({
        "enabled": old.get("enabled").cloned().unwrap_or(serde_json::Value::Bool(false)),
        "continuationsUsed": old.get("continuationsUsed").cloned().unwrap_or_else(|| serde_json::json!(0)),
        "continuationPrompt": old
            .get("continuationPrompt")
            .cloned()
            .unwrap_or_else(|| serde_json::json!(DEFAULT_AUTONOMOUS_CONTINUATION_PROMPT)),
    });
    if let Some(started_at) = old.get("startedAt") {
        state["startedAt"] = started_at.clone();
    }
    if !last_stop.is_null() {
        state["lastStop"] = last_stop;
    }
    Ok(serde_json::from_value(state)?)
}

/// The autonomous run of one conversation; a fork starts disabled.
pub static AUTONOMOUS_DOC: ConversationDoc<AutonomousDocState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.autonomous",
        version: 2,
        initial: AutonomousDocState::initial,
        migrate: Some(migrate_autonomous),
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.autonomous has a valid version"),
};

/// `eukhe.goal.loop`: what the hooks already decided, keyed by the asking
/// generation task, so a rerun after a crash repeats the decision.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct LoopState {
    /// The last `on_yield` decision.
    #[serde(default, rename = "yield", skip_serializing_if = "Option::is_none")]
    pub yield_record: Option<YieldRecord>,
    /// The autonomous run's progress check at its last continuation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub progress: Option<RunProgress>,
}

/// The autonomous run's progress check at its last continuation: whose it
/// is (the run's first input), the work the session had done then
/// (`crate::durable::children::WorkLedger::count`), and the continuations
/// in a row that did no new work. A new run (a new user input) starts the
/// count again.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct RunProgress {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input: Option<SubmissionId>,
    pub work: u64,
    pub stalls: u64,
}

/// One `on_yield` decision of generation `task_id`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct YieldRecord {
    pub task_id: TaskId,
    pub outcome: YieldOutcome,
}

/// The decided outcome of one final answer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "camelCase")]
pub(crate) enum YieldOutcome {
    /// Continue the run with this user text.
    Continue { text: String, origin: InputOrigin },
    /// End the run.
    End,
}

/// The committed value of `token` in `conversation_id`; `None` when the
/// document does not exist.
///
/// # Errors
///
/// Read failures, or a value that does not decode.
pub(crate) async fn read_doc<D>(
    reader: &(impl DocumentReader + ?Sized),
    token: &D,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Option<D::Value>>
where
    D: for<'a> DocToken<Locator<'a> = ConversationId>,
{
    let Some(value) = reader.snapshot(token, conversation_id, cx).await? else {
        return Ok(None);
    };
    Ok(Some(from_json(&JsonValue::Object(value))?))
}

/// The draft of `token` in `conversation_id` (created with its initial
/// value when absent) and its current typed value.
///
/// # Errors
///
/// Transaction failures, or a value that does not decode.
pub(crate) async fn open_doc<D>(
    tx: &Tx,
    token: &D,
    conversation_id: ConversationId,
) -> SessionResult<(Draft, D::Value)>
where
    D: for<'a> SingletonDocToken<Locator<'a> = ConversationId>,
{
    let draft = tx.doc(token, conversation_id).await?;
    let value = from_json(&draft.value()?)?;
    Ok((draft, value))
}

/// Replace the draft's value with `value`, leaf by leaf.
///
/// # Errors
///
/// Encoding or draft failures.
pub(crate) fn write_doc<T: Serialize>(draft: &Draft, value: &T) -> SessionResult<()> {
    let encoded = to_json(value)?;
    let Some(fields) = encoded.as_object() else {
        return Err(SessionError::error("a document value must be an object"));
    };
    for name in draft.keys()? {
        if !fields.contains_key(&name) {
            draft.delete(name.as_str())?;
        }
    }
    for (name, child) in fields.iter() {
        assign_json(draft, name, child)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use eukhe_types::acceptance::AcceptanceLabel;
    use eukhe_types::input_origin::GoalContextKind;

    use crate::autonomous::AutonomousStop;

    use super::*;

    fn migrated(text: &str, from: u64) -> LoopState {
        let value = JsonValue::parse(text).expect("json");
        migrate_loop(value.as_object().expect("object"), from).expect("migrate")
    }

    /// A version 2 record of the removed no-progress backoff loads: the
    /// migration drops it, so the rerun decides again; the removed goal's
    /// accounted generation goes too.
    #[test]
    fn a_wait_record_of_the_removed_backoff_is_dropped() {
        let old = r#"{"accounted":7,"yield":{"taskId":7,"outcome":{"type":"wait","until":20000}}}"#;
        assert_eq!(migrated(old, 2), LoopState::default());
    }

    /// A version 3 record of an old session: its continuation (with the
    /// removed goal's origin, which old sessions still hold) is kept; the
    /// removed goal's progress check and accounted generation go, so the
    /// run's own check starts its count.
    #[test]
    fn a_version_3_record_keeps_its_continuation_and_drops_the_goal_check() {
        let old = r#"{"accounted":7,"progress":{"goalId":"g1","work":4,"stalls":2},"yield":{"taskId":7,"outcome":{"type":"continue","text":"go on","origin":{"kind":"goal","context":"continuation"}}}}"#;
        assert_eq!(
            migrated(old, 3),
            LoopState {
                yield_record: Some(YieldRecord {
                    task_id: TaskId::from_number(7),
                    outcome: YieldOutcome::Continue {
                        text: "go on".to_owned(),
                        origin: InputOrigin::Goal {
                            context: GoalContextKind::Continuation,
                        },
                    },
                }),
                progress: None,
            }
        );
    }

    fn migrated_run(text: &str) -> AutonomousDocState {
        let value = JsonValue::parse(text).expect("json");
        migrate_autonomous(value.as_object().expect("object"), 1).expect("migrate")
    }

    /// A version 1 run held its own limits, gates and their counts: the
    /// migration drops them and keeps the run, its continuations, start
    /// and prompt; a stop by a gate reads as the checks' end (passed, or
    /// failed when its retries ran out), one by a limit as the budget's.
    #[test]
    fn a_version_1_autonomous_run_drops_its_own_limits_and_gates() {
        let v1 = |stop: &str| {
            format!(
                r#"{{"enabled":true,"continuationsUsed":2,"turnsUsed":3,"tokensUsed":900,"startedAt":5,"limits":{{"maxContinuations":3,"maxTurns":12,"maxTokens":80000,"timeoutMs":1800000}},"continuationPrompt":"go on","gates":{{"commands":["make test"],"maxRetries":3,"timeoutMs":60000}},"gateAttempts":{{"make test":1}},"subagentKeepAliveMs":0{stop}}}"#
            )
        };
        let run = |last_stop| AutonomousDocState {
            enabled: true,
            continuations_used: 2,
            started_at: Some(5),
            continuation_prompt: "go on".to_owned(),
            last_stop,
        };
        assert_eq!(
            [
                migrated_run(&v1("")),
                migrated_run(&v1(r#","lastStop":"gatePassed""#)),
                migrated_run(&v1(r#","lastStop":"gateRetryExhausted""#)),
                migrated_run(&v1(r#","lastStop":"maxTurns""#)),
                migrated_run(&v1(r#","lastStop":"budget""#)),
            ],
            [
                run(None),
                run(Some(AutonomousStop::Checks(
                    AcceptanceLabel::ChecksPassedUnconfined
                ))),
                run(Some(AutonomousStop::Checks(AcceptanceLabel::Failed))),
                run(Some(AutonomousStop::Budget)),
                run(Some(AutonomousStop::Budget)),
            ]
        );
    }

    /// A version 1 run that was never enabled, without a prompt, migrates
    /// to the initial run.
    #[test]
    fn a_version_1_run_without_a_prompt_takes_the_default() {
        assert_eq!(
            migrated_run(r#"{"enabled":false,"continuationsUsed":0}"#),
            AutonomousDocState::initial()
        );
    }
}
