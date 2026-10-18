//! The goal extension's conversation documents and their typed read/write
//! helpers.
//!
//! - `eukhe.goal`: the thread goal ([`GoalState`], the old
//!   `thread_goal_state` row's payload). Rewindable: a fork starts from the
//!   goal as of its fork entry (the old "goal state follows the branch cut").
//! - `eukhe.goal.loop`: continuation bookkeeping that makes the hooks
//!   idempotent across a crash rerun (the last accounted generation and the
//!   last `on_yield` decision, both keyed by the generation task).
//! - `eukhe.autonomous`: the autonomous run state (see `autonomous.rs`).

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::delta::Draft;
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use eukhe_durable::documents::{
    CallbackError, ConversationDoc, DocDefinition, DocToken, RewindableConversationDoc,
    SingletonDocToken,
};
use eukhe_durable::harness::json::assign_json;
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::types::{
    ConversationId, DocumentReader, DocumentReaderExt, LatestFork, RewindableFork, TaskId,
};
use eukhe_types::input_origin::InputOrigin;
use serde::{Deserialize, Serialize};

use super::autonomous::AutonomousDocState;
use crate::goals::{empty_goal_state, GoalState};

/// The thread goal of one conversation.
pub static GOAL_DOC: RewindableConversationDoc<GoalState> = match RewindableConversationDoc::define(
    DocDefinition {
        kind: "eukhe.goal",
        version: 1,
        initial: empty_goal_state,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    RewindableFork::AsOf,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.goal has a valid version"),
};

/// Version 1 recorded a continuation without its origin. Versions 1 and 2
/// could record the removed no-progress backoff (`{"type":"wait","until":
/// ms}`). The record only replays a decision on a crash rerun, so the
/// migration drops such a record and the rerun decides again.
fn migrate_loop(value: &JsonObject, from: u64) -> Result<GoalLoopState, CallbackError> {
    let mut value = value.clone();
    let outcome = value
        .get("yield")
        .and_then(|record| record.get("outcome"))
        .and_then(|outcome| outcome.get("type"))
        .and_then(JsonValue::as_str);
    if outcome == Some("wait") || (from == 1 && outcome == Some("continue")) {
        value.remove("yield");
    }
    Ok(from_json(&JsonValue::Object(Arc::new(value)))?)
}

/// Continuation bookkeeping of one conversation; a fork starts empty.
pub(crate) static LOOP_DOC: ConversationDoc<GoalLoopState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.goal.loop",
        version: 3,
        initial: GoalLoopState::default,
        migrate: Some(migrate_loop),
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.goal.loop has a valid version"),
};

/// The autonomous run of one conversation; a fork starts disabled.
pub static AUTONOMOUS_DOC: ConversationDoc<AutonomousDocState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.autonomous",
        version: 1,
        initial: AutonomousDocState::initial,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.autonomous has a valid version"),
};

/// `eukhe.goal.loop`: what the hooks already decided, keyed by the asking
/// generation task, so a rerun after a crash repeats the decision instead of
/// charging the goal again.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct GoalLoopState {
    /// The generation whose settled response was last accounted.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub accounted: Option<TaskId>,
    /// The last `on_yield` decision.
    #[serde(default, rename = "yield", skip_serializing_if = "Option::is_none")]
    pub yield_record: Option<YieldRecord>,
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
    use eukhe_types::goal::GoalContextKind;

    use super::*;

    fn migrated(text: &str, from: u64) -> GoalLoopState {
        let value = JsonValue::parse(text).expect("json");
        migrate_loop(value.as_object().expect("object"), from).expect("migrate")
    }

    /// A version 2 record of the removed no-progress backoff loads: the
    /// migration drops it, so the rerun decides again.
    #[test]
    fn a_wait_record_of_the_removed_backoff_is_dropped() {
        let old = r#"{"accounted":7,"yield":{"taskId":7,"outcome":{"type":"wait","until":20000}}}"#;
        assert_eq!(
            migrated(old, 2),
            GoalLoopState {
                accounted: Some(TaskId::from_number(7)),
                yield_record: None,
            }
        );
    }

    /// A version 2 continuation carries its origin: the migration keeps it.
    #[test]
    fn a_version_2_continuation_is_kept() {
        let state = GoalLoopState {
            accounted: None,
            yield_record: Some(YieldRecord {
                task_id: TaskId::from_number(7),
                outcome: YieldOutcome::Continue {
                    text: "go on".to_owned(),
                    origin: InputOrigin::Goal {
                        context: GoalContextKind::Continuation,
                    },
                },
            }),
        };
        let text = serde_json::to_string(&state).expect("encode");
        assert_eq!(migrated(&text, 2), state);
    }
}
