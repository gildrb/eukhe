//! The daemon's durable withdrawn-input store: one
//! `eukhe.daemon.suspended` document on the main conversation holding
//! the inputs an `abort` withdrew (`suspended`) and the admissions an
//! input-pause lease holds (`held`). The worker's `core` caches both
//! lists; every mutation rewrites the document, so `resume_queue`,
//! `clear_queue`, queue mutations, the pause release, and a worker
//! restart (the supervisor relaunches the worker over the same storage)
//! all read the same durable truth — the old engine kept these rows in
//! its process-local recovery journal, which a crash lost.

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::harness::json::assign_json;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{CheckpointInfo, ConversationId, DocumentReaderExt, LatestFork};
use eukhe_types::pi_ai::UserContent;
use serde::{Deserialize, Serialize};

use super::bridge::{content_preview, QueuedInput, QueuedMode};

/// How one withdrawn input waits (the inbox item's `mode` names).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum WithdrawnMode {
    #[serde(rename = "steer")]
    Steer,
    #[serde(rename = "followUp")]
    FollowUp,
}

impl From<QueuedMode> for WithdrawnMode {
    fn from(mode: QueuedMode) -> Self {
        match mode {
            QueuedMode::Steer => Self::Steer,
            QueuedMode::FollowUp => Self::FollowUp,
        }
    }
}

impl From<WithdrawnMode> for QueuedMode {
    fn from(mode: WithdrawnMode) -> Self {
        match mode {
            WithdrawnMode::Steer => Self::Steer,
            WithdrawnMode::FollowUp => Self::FollowUp,
        }
    }
}

impl From<eukhe_durable::harness::types::WhenBusy> for WithdrawnMode {
    fn from(mode: eukhe_durable::harness::types::WhenBusy) -> Self {
        match mode {
            eukhe_durable::harness::types::WhenBusy::Steer => Self::Steer,
            eukhe_durable::harness::types::WhenBusy::FollowUp
            | eukhe_durable::harness::types::WhenBusy::Reject => Self::FollowUp,
        }
    }
}

/// One withdrawn input: its lane and content. `id` is the withdrawn
/// submission's id when the input had one (an abort withdrew it from the
/// inbox); admissions an input pause held before their submission carry
/// none and preview by content alone.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct WithdrawnInput {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) id: Option<eukhe_durable::types::SubmissionId>,
    pub(crate) mode: WithdrawnMode,
    pub(crate) content: UserContent,
}

impl From<&QueuedInput> for WithdrawnInput {
    fn from(input: &QueuedInput) -> Self {
        Self {
            id: Some(input.id),
            mode: input.mode.into(),
            content: input.content.clone(),
        }
    }
}

impl WithdrawnInput {
    /// The queue-strip projection of this input (the id is not live: the
    /// projection only ever compares identity within one worker life).
    #[must_use]
    pub(crate) fn queued(&self) -> QueuedInput {
        QueuedInput {
            id: self
                .id
                .unwrap_or_else(|| eukhe_durable::types::SubmissionId::from_number(0)),
            mode: self.mode.into(),
            text: content_preview(&self.content),
            content: self.content.clone(),
        }
    }
}

/// The `eukhe.daemon.suspended` document value.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub(crate) struct SuspendedState {
    #[serde(default)]
    pub(crate) suspended: Vec<WithdrawnInput>,
    #[serde(default)]
    pub(crate) held: Vec<WithdrawnInput>,
}

impl SuspendedState {
    /// The queue-strip rows: abort-suspended inputs first, then the
    /// pause-held ones (both lanes interleave by mode in the projection).
    #[must_use]
    pub(crate) fn queued(&self) -> Vec<QueuedInput> {
        self.suspended
            .iter()
            .chain(&self.held)
            .map(WithdrawnInput::queued)
            .collect()
    }
}

/// The document checkpoints when both lists empty, so a cleared queue
/// collapses its history like the inbox does.
fn suspended_checkpoint_when(
    value: &JsonObject,
    _ops: &[eukhe_chord::delta::Op],
    _info: CheckpointInfo,
) -> bool {
    let empty = |key: &str| {
        value
            .get(key)
            .and_then(JsonValue::as_array)
            .is_some_and(<[JsonValue]>::is_empty)
    };
    empty("suspended") && empty("held")
}

/// The conversation-scope `eukhe.daemon.suspended` document (version 1).
static SUSPENDED_DOC: ConversationDoc<SuspendedState> =
    match ConversationDoc::define(
        DocDefinition {
            kind: "eukhe.daemon.suspended",
            version: 1,
            initial: SuspendedState::default,
            migrate: None,
            checkpoint_when: Some(suspended_checkpoint_when),
        },
        LatestFork::Current,
    ) {
        Ok(token) => token,
        Err(_) => panic!("eukhe.daemon.suspended has a valid version"),
    };

/// Read the withdrawn inputs of `conversation_id` (defaults when never
/// written).
///
/// # Errors
///
/// The document cannot be read or decoded.
pub(crate) async fn read_suspended(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<SuspendedState> {
    match harness
        .snapshot(&SUSPENDED_DOC, conversation_id, cx)
        .await?
    {
        Some(value) => from_json(&JsonValue::Object(value)).map_err(SessionError::other),
        None => Ok(SuspendedState::default()),
    }
}

/// Replace the withdrawn inputs of `conversation_id` in one commit.
///
/// # Errors
///
/// The commit fails, or a value does not encode.
pub(crate) async fn write_suspended(
    harness: &Harness,
    conversation_id: ConversationId,
    state: &SuspendedState,
    cx: &Context,
) -> SessionResult<()> {
    let suspended = to_json(&state.suspended).map_err(SessionError::other)?;
    let held = to_json(&state.held).map_err(SessionError::other)?;
    harness
        .commit(
            move |tx| async move {
                let draft = tx.doc(&SUSPENDED_DOC, conversation_id).await?;
                assign_json(&draft, "suspended", &suspended)?;
                assign_json(&draft, "held", &held)?;
                Ok(())
            },
            cx,
        )
        .await
}
