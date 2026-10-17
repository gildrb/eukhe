//! The Director stack (docs/harness.md S5, the model `bend/director.bend`):
//! after each final answer the agent loop asks a stack of Directors what to
//! do. The goal, the autonomous run, a reminder, and a forced tool call
//! are layers ([`LayerKind`]); the top layer decides first ([`decide`]),
//! and the loop of one run has a global budget of steps ([`Loop`]).
//!
//! The stack and the loop of the conversation's last run live in the
//! rewindable `eukhe.directors` document ([`DIRECTORS_DOC`]): each step
//! commits it, a resume reads it back, and a fork or a branch move starts
//! from the stack as of its fork entry. The goal extension's `on_yield`
//! hook runs the steps (`goals/hooks.rs`).

mod stack;

#[cfg(test)]
mod bridge;
#[cfg(test)]
mod tests;

use eukhe_chord::context::Context;
use eukhe_durable::documents::{DocDefinition, RewindableConversationDoc};
use eukhe_durable::harness::types::ForcedTool;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReader, RewindableFork, SubmissionId};
use serde::{Deserialize, Serialize};

pub use stack::{decide, Decision, End, Layer, LayerKind, Loop, Outcome, Verdict};

use super::goals::{conversation_of, open_doc, read_doc, write_doc};
use crate::settings::Settings;

/// The reminders and forced calls a stack holds when the
/// `directors.stackCap` setting is unset or `0`.
pub const DEFAULT_STACK_CAP: usize = 8;

/// The places the goal and the autonomous run keep on every stack, above
/// the cap of the pushed layers: the stack holds at most `stackCap + 2`
/// layers ([`DirectorLimits::bound`]).
pub const RESERVED_LAYERS: usize = 2;

/// The custom type of the display row that records a forced call that
/// failed (display-only: the user sees it, the model does not).
pub const DIRECTOR_NOTICE_CUSTOM_TYPE: &str = "eukhe.director";

/// The steps (continuations) one run's loop makes when the
/// `directors.maxSteps` setting is unset or `0`.
pub const DEFAULT_MAX_STEPS: u64 = 200;

/// The Director stack of one conversation.
pub static DIRECTORS_DOC: RewindableConversationDoc<DirectorState> =
    match RewindableConversationDoc::define(
        DocDefinition {
            kind: "eukhe.directors",
            version: 1,
            initial: DirectorState::default,
            migrate: None,
            checkpoint_when: Some(|_, _, _| true),
        },
        RewindableFork::AsOf,
    ) {
        Ok(token) => token,
        Err(_) => panic!("eukhe.directors has a valid version"),
    };

/// `eukhe.directors`: the stack (bottom first) and the loop of the
/// conversation's last run.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DirectorState {
    #[serde(default)]
    pub stack: Vec<Layer>,
    #[serde(default, rename = "loop", skip_serializing_if = "Option::is_none")]
    pub run: Option<RunLoop>,
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
            | LayerKind::Goal
            | LayerKind::Autonomous
            | LayerKind::Reminder { .. } => None,
        })
    }
}

/// The cap of the pushed layers and the global budget of a loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DirectorLimits {
    /// The reminders and forced calls the stack may hold.
    pub stack_cap: usize,
    pub max_steps: u64,
}

impl Default for DirectorLimits {
    fn default() -> Self {
        Self {
            stack_cap: DEFAULT_STACK_CAP,
            max_steps: DEFAULT_MAX_STEPS,
        }
    }
}

impl DirectorLimits {
    /// The layers the whole stack may hold: the pushed layers and the
    /// places of the goal and the autonomous run. A decision of the stack
    /// gets this cap.
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
/// `stack_cap`; the goal and the autonomous run have their own places, one
/// layer each.
///
/// # Errors
///
/// The stack holds `stack_cap` pushed layers already, a goal or autonomous
/// layer is on the stack already, or read/commit failures.
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
