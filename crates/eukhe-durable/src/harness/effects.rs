//! Exactly-once effects (spec O1-O13) and irreversible effects (spec
//! I4-I8): the `eukhe.effects` document, one conversation's ledger of the
//! steps whose outcome a restart could not tell and that were not safe to
//! repeat and, in a root session, of the irreversible effects that ran.
//!
//! Every effect is journaled where its owner keeps it (a tool call in its
//! task's checkpoints, a provider request in its generation's, a job in its
//! node), and at a restart the owner settles it itself (spec O13): it looks
//! at the evidence the step declares (a write's files, a git command's
//! refs, a job's exit record), runs again a step safe to repeat, and asks
//! the compiled core (`eukhe_bend::rules::once`). A step the core says to
//! interrupt ended `unknown` and is treated as not run: its owner tells the
//! model where it reads it (a tool result, a notice) and, in the same
//! commit, notes it here ([`note_unknown`]) under the run in flight
//! ([`EffectsState::run`]), whose end-of-run report lists it once. Nothing
//! waits on a person: a client may list the entries
//! ([`unknown_effects`]) and correct one after looking
//! ([`resolve_unknown`]). Clients read the ledger
//! ([`read_unknown_effects`]) and follow it ([`watch_unknown_effects`]);
//! its vocabulary is the shared wire one (`eukhe_types::effects`).
//!
//! A root run's start numbers the run ([`begin_run`], keyed by the run so
//! a replayed start numbers nothing new); each irreversible effect that
//! ran, the root's or a subagent's, is recorded once by its key under the
//! next id `e<N>` ([`record_ran`]); the end of a run reports exactly that
//! run's ([`run_report`]). Clients read the whole list
//! ([`read_ran_effects`]) and follow it ([`watch_ran_effects`]). The
//! numbering and the run's list come from the compiled core
//! (`eukhe_bend::rules::irreversible`).

#[cfg(test)]
mod tests;

use std::sync::Arc;

use eukhe_bend::rules::irreversible::{self, Entry, Recorded};
use eukhe_chord::context::{await_with_context, Context};
use eukhe_chord::json::{from_json, to_json, JsonValue};
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;
use tokio::task::JoinHandle;

pub use eukhe_types::effects::{
    EffectKind, EffectResolution, RanEffect, RanEffectDraft, RunReport, UnknownCause, UnknownEffect,
};

use crate::documents::{ConversationDoc, DocDefinition};
use crate::harness::Harness;
use crate::session::{CommitListener, SessionError, SessionResult, Tx, Unsubscribe};
use crate::types::{
    CommitChange, CommitPublication, ConversationId, DocumentCommitChange, DocumentIdentity,
    LatestFork,
};

/// The corrected entries the ledger keeps for people to read; an
/// uncorrected one is never dropped, whatever their number.
pub const RESOLVED_KEPT: usize = 64;

/// The persisted kind of [`EFFECTS_DOC`].
const EFFECTS_DOC_KIND: &str = "eukhe.effects";

/// The ledger: the steps treated as not run, oldest first, the run of the
/// root session in flight and the key of the run that started it, and
/// the irreversible effects that ran, by id (a ledger written before it
/// had them reads as none).
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EffectsState {
    pub unknown: Vec<UnknownEffect>,
    /// The root session's current run (0: none yet): a step noted now is
    /// listed in that run's end-of-run report.
    #[serde(default)]
    pub run: u64,
    /// The key of the root run [`EffectsState::run`] numbers (its first
    /// input); `None` before the first.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub run_key: Option<String>,
    #[serde(default)]
    pub ran: Vec<RanEffect>,
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

/// Note that a restart treated `effect` as not run, in the commit that
/// tells the model, under the run in flight ([`EffectsState::run`]), so
/// that run's end-of-run report lists it. An effect is noted once: a
/// second note of its id changes nothing.
///
/// # Errors
///
/// Document access or draft failures.
pub async fn note_unknown(
    tx: &Tx,
    conversation_id: ConversationId,
    effect: &UnknownEffect,
) -> SessionResult<()> {
    let doc = tx.doc(&EFFECTS_DOC, conversation_id).await?;
    let state: EffectsState = from_json(&doc.value()?)?;
    if state.unknown.iter().any(|noted| noted.id == effect.id) {
        return Ok(());
    }
    let unknown = doc.child("unknown")?;
    // The oldest corrected entry makes room; an uncorrected one stays.
    let resolved = state
        .unknown
        .iter()
        .filter(|noted| noted.resolution.is_some())
        .count();
    if resolved >= RESOLVED_KEPT {
        if let Some(oldest) = state
            .unknown
            .iter()
            .position(|noted| noted.resolution.is_some())
        {
            unknown.splice(index(oldest)?, 1, Vec::<JsonValue>::new())?;
        }
    }
    let noted = UnknownEffect {
        settled_run: Some(state.run),
        ..effect.clone()
    };
    unknown.push([to_json(&noted)?])?;
    Ok(())
}

/// Correct the uncorrected entry `id` as `resolution` (optional: nothing
/// waits for it): the entry as corrected, or `None` when the ledger holds
/// no uncorrected entry of that id.
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

/// The whole ledger as the commit in flight sees it.
///
/// # Errors
///
/// Document access or draft failures.
pub async fn effects_state(
    tx: &Tx,
    conversation_id: ConversationId,
) -> SessionResult<EffectsState> {
    let ledger = tx.doc(&EFFECTS_DOC, conversation_id).await?;
    Ok(from_json(&ledger.value()?)?)
}

/// Start the root session's run `key` (its first input), in the commit
/// that sees it start: its number (the first is 1). A run is numbered
/// once: beginning the current run's key again (a replayed start after a
/// restart) changes nothing and gives its number.
///
/// # Errors
///
/// Document access or draft failures.
pub async fn begin_run(tx: &Tx, conversation_id: ConversationId, key: &str) -> SessionResult<u64> {
    let ledger = tx.doc(&EFFECTS_DOC, conversation_id).await?;
    let state: EffectsState = from_json(&ledger.value()?)?;
    if state.run_key.as_deref() == Some(key) {
        return Ok(state.run);
    }
    let run = state.run + 1;
    ledger.set("run", to_json(&run)?)?;
    ledger.set("runKey", to_json(&key)?)?;
    Ok(run)
}

/// The number `N` of the id `e<N>`; `None` for any other text.
fn ran_number(id: &str) -> Option<u64> {
    id.strip_prefix('e')?.parse().ok()
}

/// The compiled core's view of the ran list.
fn ran_entries(ran: &[RanEffect]) -> Vec<Entry> {
    ran.iter()
        .filter_map(|effect| {
            Some(Entry {
                n: ran_number(&effect.id)?,
                key: effect.key.clone(),
                run: effect.run,
            })
        })
        .collect()
}

fn core_error(error: &eukhe_bend::Error) -> SessionError {
    SessionError::error(format!("the effect ledger's core call failed: {error}"))
}

/// Record that the irreversible effect `draft` ran, in the root session's
/// run `run`: the effect as recorded, under the next id `e<N>` (never
/// reused). An effect is recorded once: recording its key again (a replay)
/// changes nothing and gives the effect as first recorded.
///
/// # Errors
///
/// Document access or draft failures, or the core call failed.
pub async fn record_ran(
    tx: &Tx,
    conversation_id: ConversationId,
    draft: RanEffectDraft,
    run: u64,
) -> SessionResult<RanEffect> {
    let ledger = tx.doc(&EFFECTS_DOC, conversation_id).await?;
    let state: EffectsState = from_json(&ledger.value()?)?;
    let recorded = irreversible::record(&ran_entries(&state.ran), &draft.key)
        .map_err(|error| core_error(&error))?;
    match recorded {
        Recorded::Known(number) => state
            .ran
            .into_iter()
            .find(|effect| ran_number(&effect.id) == Some(number))
            .ok_or_else(|| SessionError::error("the core named a ran effect the ledger lacks")),
        Recorded::New(number) => {
            let effect = draft.recorded(number, run);
            if !ledger.has("ran")? {
                ledger.set("ran", JsonValue::array())?;
            }
            ledger.child("ran")?.push([to_json(&effect)?])?;
            Ok(effect)
        }
    }
}

/// The end of run `run` of the ledger `state`: the irreversible effects
/// that ran in it, in order, and the unknown effects it treated as not
/// run.
///
/// # Errors
///
/// The core call failed.
pub fn run_report(state: &EffectsState, run: u64) -> SessionResult<RunReport> {
    let numbers = irreversible::this_run(&ran_entries(&state.ran), run)
        .map_err(|error| core_error(&error))?;
    let ran = numbers
        .iter()
        .filter_map(|number| {
            state
                .ran
                .iter()
                .find(|effect| ran_number(&effect.id) == Some(*number))
                .cloned()
        })
        .collect();
    Ok(RunReport {
        ran,
        unknown: eukhe_types::effects::treated_not_run(&state.unknown, run)
            .cloned()
            .collect(),
    })
}

/// The committed ledger of the conversation (empty while it was never
/// written).
///
/// # Errors
///
/// The document cannot be read or decoded.
pub async fn read_effects_state(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<EffectsState> {
    match harness.snapshot(&EFFECTS_DOC, conversation_id, cx).await? {
        Some(value) => Ok(from_json(&JsonValue::Object(value))?),
        None => Ok(EffectsState::default()),
    }
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
    Ok(read_effects_state(harness, conversation_id, cx)
        .await?
        .unknown)
}

/// The committed irreversible effects that ran in the conversation, by id
/// (none while the ledger was never written).
///
/// # Errors
///
/// The document cannot be read or decoded.
pub async fn read_ran_effects(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Vec<RanEffect>> {
    Ok(read_effects_state(harness, conversation_id, cx).await?.ran)
}

/// A live stream of one list of a conversation's ledger (see
/// [`watch_unknown_effects`], [`watch_ran_effects`]). Dropping it stops
/// the subscription.
pub struct LedgerUpdates<T> {
    receiver: mpsc::UnboundedReceiver<Vec<T>>,
    unsubscribe: Unsubscribe,
    task: JoinHandle<()>,
}

/// The stream of the unknown effects.
pub type UnknownEffectUpdates = LedgerUpdates<UnknownEffect>;

/// The stream of the irreversible effects that ran.
pub type RanEffectUpdates = LedgerUpdates<RanEffect>;

impl<T> LedgerUpdates<T> {
    /// The next list; `None` once the Harness closed or a read failed.
    pub async fn next(&mut self) -> Option<Vec<T>> {
        self.receiver.recv().await
    }
}

impl<T> Drop for LedgerUpdates<T> {
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

/// Watch the unknown effects of `conversation_id`: the committed list
/// first, then the list after every commit that changed it (an effect
/// noted or resolved). Cancelling `cx` ends the stream.
///
/// # Errors
///
/// The Session is closed.
pub fn watch_unknown_effects(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<UnknownEffectUpdates> {
    watch_ledger(harness, conversation_id, cx, |ledger| ledger.unknown)
}

/// Watch the irreversible effects that ran in `conversation_id`: the
/// committed list first, then the list after every commit that changed it
/// (an effect recorded). Cancelling `cx` ends the stream.
///
/// # Errors
///
/// The Session is closed.
pub fn watch_ran_effects(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<RanEffectUpdates> {
    watch_ledger(harness, conversation_id, cx, |ledger| ledger.ran)
}

/// Watch the list `pick` takes from the ledger of `conversation_id`: sent
/// first, then again each time a commit changed it.
fn watch_ledger<T>(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
    pick: fn(EffectsState) -> Vec<T>,
) -> SessionResult<LedgerUpdates<T>>
where
    T: Clone + PartialEq + Send + 'static,
{
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
        let mut sent: Option<Vec<T>> = None;
        loop {
            let Ok(ledger) = read_effects_state(&reader, conversation_id, &cx).await else {
                return;
            };
            let list = pick(ledger);
            if sent.as_ref() != Some(&list) {
                sent = Some(list.clone());
                if sender.send(list).is_err() {
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
    Ok(LedgerUpdates {
        receiver,
        unsubscribe,
        task,
    })
}
