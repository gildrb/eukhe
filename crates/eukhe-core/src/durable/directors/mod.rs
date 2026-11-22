//! The Director stack (the model `bend/director.bend`):
//! after each final answer the agent loop asks a stack of Directors what to
//! do. The autonomous run, a reminder, and a forced tool call are layers
//! ([`LayerKind`]); the top layer decides first, and the loop of one run
//! has a global budget of steps ([`Loop::tick`]).
//!
//! The stack and the loop of the conversation's last run live in the
//! rewindable `eukhe.directors` document ([`DIRECTORS_DOC`]): each step
//! commits it, a resume reads it back, and a fork or a branch move starts
//! from the stack as of its fork entry. The autonomous extension's
//! `on_yield` hook runs the steps (`autonomous/hooks.rs`); after it, the
//! work-left Director's extension (`work_left.rs`) continues a run whose
//! final answer leaves task work undone, and records its decision in the
//! same document.

mod pending;
mod progress;
mod stack;
mod work_left;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod work_left_tests;

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, JsonObject, JsonValue};
use eukhe_durable::documents::{CallbackError, DocDefinition, RewindableConversationDoc};
use eukhe_durable::harness::types::ForcedTool;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReader, RewindableFork, SubmissionId};
use serde::{Deserialize, Serialize};

pub(crate) use pending::pending_work_hook;
pub(crate) use progress::{compared, stall_check, Last, Stall};
pub use stack::{End, Layer, LayerKind, Loop, Verdict};
pub(crate) use work_left::read_work;
pub use work_left::{
    extension as work_left_extension, tool_acted, WorkLeftOutcome, WorkLeftRecord,
};

use super::autonomous::{conversation_of, open_doc, read_doc, write_doc};
use crate::settings::Settings;

/// The reminders and forced calls a stack holds when the
/// `directors.stackCap` setting is unset or `0`.
pub const DEFAULT_STACK_CAP: usize = 8;

/// The places the autonomous run keeps on every stack, above the cap of
/// the pushed layers: the stack holds at most `stackCap + 1` layers
/// ([`DirectorLimits::bound`]).
pub const RESERVED_LAYERS: usize = 1;

/// The custom type of the display row that records a forced call that
/// failed (display-only: the user sees it, the model does not).
pub const DIRECTOR_NOTICE_CUSTOM_TYPE: &str = "eukhe.director";

/// The steps (continuations) one run's loop makes when the
/// `directors.maxSteps` setting is unset or `0`.
pub const DEFAULT_MAX_STEPS: u64 = 200;

/// The autonomous continuations in a row with no new work at which the
/// run is asked once for another approach, when the `directors.stallSteps`
/// setting is unset or `0`; twice as many end the run, not done
/// (`crate::durable::autonomous`). The first continuation can be an answer
/// that only states a plan; the second carries the no-progress note that
/// asks for one concrete step; the third shows that the model did not act
/// on that note.
pub const DEFAULT_STALL_STEPS: u64 = 3;

/// Version 1 could hold the removed goal's layer (`{"type":"goal"}`): the
/// migration drops it, and the rest of the stack and the loop stay.
fn migrate_directors(value: &JsonObject, _from: u64) -> Result<DirectorState, CallbackError> {
    let mut value = value.clone();
    let kept: Option<Vec<JsonValue>> = match value.get("stack") {
        Some(JsonValue::Array(stack)) => Some(
            stack
                .iter()
                .filter(|layer| {
                    layer
                        .get("kind")
                        .and_then(|kind| kind.get("type"))
                        .and_then(JsonValue::as_str)
                        != Some("goal")
                })
                .cloned()
                .collect(),
        ),
        _ => None,
    };
    if let Some(kept) = kept {
        value.insert("stack", JsonValue::Array(Arc::new(kept)));
    }
    Ok(from_json(&JsonValue::Object(Arc::new(value)))?)
}

/// The Director stack of one conversation.
pub static DIRECTORS_DOC: RewindableConversationDoc<DirectorState> =
    match RewindableConversationDoc::define(
        DocDefinition {
            kind: "eukhe.directors",
            version: 2,
            initial: DirectorState::default,
            migrate: Some(migrate_directors),
            checkpoint_when: Some(|_, _, _| true),
        },
        RewindableFork::AsOf,
    ) {
        Ok(token) => token,
        Err(_) => panic!("eukhe.directors has a valid version"),
    };

/// `eukhe.directors`: the stack (bottom first), the loop of the
/// conversation's last run, and the work-left Director's last decision.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DirectorState {
    #[serde(default)]
    pub stack: Vec<Layer>,
    #[serde(default, rename = "loop", skip_serializing_if = "Option::is_none")]
    pub run: Option<RunLoop>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub work_left: Option<WorkLeftRecord>,
}

/// The loop of one run: the run's first input, the steps left, and how it
/// ended.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RunLoop {
    /// The first input of the run (`pi.live` `run.inputs[0]`): a run with
    /// another first input starts a new loop.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input: Option<SubmissionId>,
    pub left: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub end: Option<End>,
}

impl DirectorState {
    /// The forced tool of the next request: the topmost forced call the
    /// model has not made yet.
    #[must_use]
    pub fn forced_tool(&self) -> Option<ForcedTool> {
        self.stack.iter().rev().find_map(|layer| match &layer.kind {
            LayerKind::ForceTool {
                tool,
                tries,
                called: false,
                ..
            } => Some(ForcedTool {
                tool: tool.clone(),
                retries: *tries,
            }),
            LayerKind::ForceTool { called: true, .. }
            | LayerKind::Autonomous
            | LayerKind::Reminder { .. } => None,
        })
    }
}

/// The cap of the pushed layers, the global budget of a loop, and the
/// autonomous continuations in a row with no new work that steer the run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DirectorLimits {
    /// The reminders and forced calls the stack may hold.
    pub stack_cap: usize,
    pub max_steps: u64,
    pub stall_steps: u64,
}

impl Default for DirectorLimits {
    fn default() -> Self {
        Self {
            stack_cap: DEFAULT_STACK_CAP,
            max_steps: DEFAULT_MAX_STEPS,
            stall_steps: DEFAULT_STALL_STEPS,
        }
    }
}

impl DirectorLimits {
    /// The layers the whole stack may hold: the pushed layers and the
    /// place of the autonomous run. A decision of the stack gets this cap.
    #[must_use]
    pub fn bound(self) -> usize {
        self.stack_cap.saturating_add(RESERVED_LAYERS)
    }

    /// The limits the `directors` settings give (`0` or unset takes the
    /// default).
    #[must_use]
    pub fn of(settings: &Settings) -> Self {
        let directors = settings.directors.as_ref();
        Self {
            stack_cap: directors
                .and_then(|directors| directors.stack_cap)
                .filter(|cap| *cap > 0)
                .map_or(DEFAULT_STACK_CAP, |cap| {
                    usize::try_from(cap).unwrap_or(usize::MAX)
                }),
            max_steps: directors
                .and_then(|directors| directors.max_steps)
                .filter(|steps| *steps > 0)
                .unwrap_or(DEFAULT_MAX_STEPS),
            stall_steps: directors
                .and_then(|directors| directors.stall_steps)
                .filter(|steps| *steps > 0)
                .unwrap_or(DEFAULT_STALL_STEPS),
        }
    }
}

/// The Director stack of `conversation_id` (empty when it never had one).
///
/// # Errors
///
/// Read failures, or a value that does not decode.
#[tracing::instrument(skip_all)]
pub async fn director_state(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<DirectorState> {
    Ok(read_doc(reader, &DIRECTORS_DOC, conversation_id, cx)
        .await?
        .unwrap_or_default())
}

/// Put `layer` on top of the stack of `conversation_id`, in one commit.
/// Returns the new state. A reminder or a forced call needs room under
/// `stack_cap`; the autonomous run has its own place, one layer.
///
/// # Errors
///
/// The stack holds `stack_cap` pushed layers already, an autonomous layer
/// is on the stack already, or read/commit failures.
#[tracing::instrument(skip_all)]
pub async fn push_director(
    harness: &Harness,
    conversation_id: ConversationId,
    layer: Layer,
    limits: DirectorLimits,
    cx: &Context,
) -> SessionResult<DirectorState> {
    conversation_of(harness, conversation_id, cx)
        .await?
        .commit(
            move |tx| async move {
                let (draft, mut state) = open_doc(&tx, &DIRECTORS_DOC, conversation_id).await?;
                let refusal = if layer.kind.is_pushed() {
                    let pushed = state
                        .stack
                        .iter()
                        .filter(|held| held.kind.is_pushed())
                        .count();
                    (pushed >= limits.stack_cap).then(|| {
                        format!(
                            "The Director stack is full: {} reminders and forced calls (directors.stackCap)",
                            limits.stack_cap
                        )
                    })
                } else {
                    state
                        .stack
                        .iter()
                        .any(|held| held.kind == layer.kind)
                        .then(|| format!("The Director stack holds a {:?} layer already", layer.kind))
                };
                if let Some(refusal) = refusal {
                    return Err(SessionError::error(refusal));
                }
                state.stack.push(layer);
                write_doc(&draft, &state)?;
                Ok(state)
            },
            cx,
        )
        .await
}
