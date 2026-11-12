//! Exactly-once effects (spec O1-O10): the `eukhe.effects` document, the
//! ledger of one conversation's effects whose outcome a restart could not
//! tell.
//!
//! Every effect is journaled where its owner keeps it (a tool call in its
//! task's checkpoints, a provider request in its generation's, a job in its
//! node), and at a restart the owner asks the compiled core what to do
//! with it (`eukhe_bend::rules::once`). An effect the core says to
//! interrupt ended `unknown`: its owner reports it interrupted where the
//! model reads it (a tool result, a notice) and, in the same commit, notes
//! it here ([`note_unknown`]), so any client can list the effects nobody
//! knows the outcome of ([`unknown_effects`]) and settle one after looking
//! ([`resolve_unknown`]). The ledger is durable with the session and never
//! drops an open effect. Clients read it ([`read_unknown_effects`]) and
//! follow it ([`watch_unknown_effects`]); its vocabulary is the shared
//! wire one (`eukhe_types::effects`).

use std::sync::Arc;

use eukhe_chord::context::{await_with_context, Context};
use eukhe_chord::json::{from_json, to_json, JsonValue};
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;
use tokio::task::JoinHandle;

pub use eukhe_types::effects::{EffectKind, EffectResolution, UnknownEffect};

use crate::documents::{ConversationDoc, DocDefinition};
use crate::harness::Harness;
use crate::session::{CommitListener, SessionError, SessionResult, Tx, Unsubscribe};
use crate::types::{
    CommitChange, CommitPublication, ConversationId, DocumentCommitChange, DocumentIdentity,
    LatestFork,
};

/// The resolved effects the ledger keeps for people to read; an open one
/// is never dropped, whatever their number.
pub const RESOLVED_KEPT: usize = 64;

/// The persisted kind of [`EFFECTS_DOC`].
const EFFECTS_DOC_KIND: &str = "eukhe.effects";

/// The ledger: the unknown effects, oldest first.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct EffectsState {
    pub unknown: Vec<UnknownEffect>,
}

/// The `eukhe.effects` document token.
pub static EFFECTS_DOC: ConversationDoc<EffectsState> = match ConversationDoc::define(
    DocDefinition {
        kind: EFFECTS_DOC_KIND,
        version: 1,
        initial: EffectsState::default,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.effects has a valid version"),
};

fn index(at: usize) -> SessionResult<i64> {
    i64::try_from(at).map_err(|_| SessionError::error("An effect ledger index past i64"))
}

/// Note that a restart settled `effect` unknown, in the commit that
/// reports it interrupted. An effect is noted once: a second note of its
/// id changes nothing.
///
/// # Errors
///
/// Document access or draft failures.
pub async fn note_unknown(
    tx: &Tx,
    conversation_id: ConversationId,
    effect: &UnknownEffect,
) -> SessionResult<()> {
    let unknown = tx
        .doc(&EFFECTS_DOC, conversation_id)
        .await?
        .child("unknown")?;
    let held: Vec<UnknownEffect> = from_json(&unknown.value()?)?;
    if held.iter().any(|noted| noted.id == effect.id) {
        return Ok(());
    }
    // The oldest resolved effect makes room; an open one stays.
    let resolved = held
        .iter()
        .filter(|noted| noted.resolution.is_some())
        .count();
    if resolved >= RESOLVED_KEPT {
        if let Some(oldest) = held.iter().position(|noted| noted.resolution.is_some()) {
            unknown.splice(index(oldest)?, 1, Vec::<JsonValue>::new())?;
        }
    }
    unknown.push([to_json(effect)?])?;
    Ok(())
}

/// Settle the open unknown effect `id` as `resolution`: the effect as
/// resolved, or `None` when the ledger holds no open effect of that id.
///
/// # Errors
///
/// Document access or draft failures.
pub async fn resolve_unknown(
    tx: &Tx,
    conversation_id: ConversationId,
    id: &str,
    resolution: EffectResolution,
) -> SessionResult<Option<UnknownEffect>> {
    let unknown = tx
        .doc(&EFFECTS_DOC, conversation_id)
        .await?
        .child("unknown")?;
    let held: Vec<UnknownEffect> = from_json(&unknown.value()?)?;
    let Some(at) = held
        .iter()
        .position(|noted| noted.id == id && noted.resolution.is_none())
    else {
        return Ok(None);
    };
    let resolved = UnknownEffect {
        resolution: Some(resolution),
        ..held[at].clone()
    };
    unknown.splice(index(at)?, 1, [to_json(&resolved)?])?;
    Ok(Some(resolved))
}

/// The unknown effects of the conversation, oldest first, as the commit in
/// flight sees them.
///
/// # Errors
///
/// Document access or draft failures.
pub async fn unknown_effects(
    tx: &Tx,
    conversation_id: ConversationId,
) -> SessionResult<Vec<UnknownEffect>> {
    let unknown = tx
        .doc(&EFFECTS_DOC, conversation_id)
        .await?
        .child("unknown")?;
    Ok(from_json(&unknown.value()?)?)
}

/// The committed unknown effects of the conversation, oldest first (none
/// while the ledger was never written).
///
/// # Errors
///
/// The document cannot be read or decoded.
pub async fn read_unknown_effects(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Vec<UnknownEffect>> {
    match harness.snapshot(&EFFECTS_DOC, conversation_id, cx).await? {
        Some(value) => {
            let state: EffectsState = from_json(&JsonValue::Object(value))?;
            Ok(state.unknown)
        }
        None => Ok(Vec::new()),
    }
}

/// A live stream of one conversation's ledger (see
/// [`watch_unknown_effects`]). Dropping it stops the subscription.
pub struct UnknownEffectUpdates {
    receiver: mpsc::UnboundedReceiver<Vec<UnknownEffect>>,
    unsubscribe: Unsubscribe,
    task: JoinHandle<()>,
}

impl UnknownEffectUpdates {
    /// The next ledger; `None` once the Harness closed or a read failed.
    pub async fn next(&mut self) -> Option<Vec<UnknownEffect>> {
        self.receiver.recv().await
    }
}

impl Drop for UnknownEffectUpdates {
    fn drop(&mut self) {
        self.unsubscribe.unsubscribe();
        self.task.abort();
    }
}

/// Whether `publication` changed the ledger of `conversation_id`.
fn changes_effects(publication: &CommitPublication, conversation_id: ConversationId) -> bool {
    publication.changes.iter().any(|change| match change {
        CommitChange::Document(DocumentCommitChange::Document {
            record,
            conversation_id: owner,
            ..
        }) => record.kind() == EFFECTS_DOC_KIND && *owner == Some(conversation_id),
        CommitChange::Document(DocumentCommitChange::Copy {
            record,
            conversation_id: owner,
            ..
        }) => record.kind() == EFFECTS_DOC_KIND && *owner == conversation_id,
        CommitChange::Conversation(_)
        | CommitChange::Entry(_)
        | CommitChange::Task(_)
        | CommitChange::Submission(_) => false,
    })
}

/// Watch the ledger of `conversation_id`: the committed ledger first, then
/// the ledger after every commit that changed it (an effect noted or
/// resolved). Cancelling `cx` ends the stream.
///
/// # Errors
///
/// The Session is closed.
pub fn watch_unknown_effects(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<UnknownEffectUpdates> {
    let (ticks, mut ticked) = mpsc::unbounded_channel::<()>();
    let listener: CommitListener = Arc::new(move |publication, _| {
        if changes_effects(publication, conversation_id) {
            // A closed receiver means the stream ended; nothing to notify.
            let _ = ticks.send(());
        }
    });
    let unsubscribe = harness.subscribe_commits(listener)?;
    let (sender, receiver) = mpsc::unbounded_channel();
    let reader = harness.clone();
    let cx = cx.clone();
    let task = tokio::spawn(async move {
        let mut last: Option<Vec<UnknownEffect>> = None;
        loop {
            let Ok(effects) = read_unknown_effects(&reader, conversation_id, &cx).await else {
                return;
            };
            if last.as_ref() != Some(&effects) {
                last = Some(effects.clone());
                if sender.send(effects).is_err() {
                    return;
                }
            }
            match await_with_context(ticked.recv(), &cx).await {
                Ok(Some(())) => {}
                Ok(None) | Err(_) => return,
            }
            // Coalesce a burst of commits into one read.
            while ticked.try_recv().is_ok() {}
        }
    });
    Ok(UnknownEffectUpdates {
        receiver,
        unsubscribe,
        task,
    })
}
