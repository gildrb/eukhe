//! The `eukhe.workflow.batches` conversation document: every writing
//! batch of the conversation's workflow and factory runs, keyed by its
//! lend key (`<owner>:<first agent>`). Running batches hold their files:
//! a new batch takes only paths none of them holds.

use eukhe_bend::rules::agent_tree::Patch;
use eukhe_chord::json::{from_json, to_json};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::session::{SessionResult, Tx};
use eukhe_durable::types::{ConversationId, LatestFork};
use eukhe_types::pi_ai::IndexMap;
use serde::{Deserialize, Serialize};

use super::batch::{plan, Batch, BatchRefusal, Outcome};
use super::tree::Facts;

/// The batches of one conversation, by key.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Batches {
    pub(crate) batches: IndexMap<String, Batch>,
}

pub(crate) static BATCHES_DOC: ConversationDoc<Batches> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.workflow.batches",
        version: 1,
        initial: Batches::default,
        migrate: None,
        checkpoint_when: None,
    },
    // Batches belong to the conversation whose runs started them; a fork
    // starts without any.
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.workflow.batches has a valid version"),
};

/// The batches of `conversation_id` inside a commit.
pub(crate) async fn tx_batches(tx: &Tx, conversation_id: ConversationId) -> SessionResult<Batches> {
    let doc = tx.doc(&BATCHES_DOC, conversation_id).await?;
    Ok(from_json(&doc.value()?)?)
}

/// Drop batch `key` inside a commit (its nodes could not be lent).
pub(crate) async fn tx_remove_batch(
    tx: &Tx,
    conversation_id: ConversationId,
    key: &str,
) -> SessionResult<()> {
    tx.doc(&BATCHES_DOC, conversation_id)
        .await?
        .child("batches")?
        .delete(key.to_owned())?;
    Ok(())
}

/// Write batch `key` inside a commit.
pub(crate) async fn tx_put_batch(
    tx: &Tx,
    conversation_id: ConversationId,
    key: &str,
    batch: &Batch,
) -> SessionResult<()> {
    tx.doc(&BATCHES_DOC, conversation_id)
        .await?
        .child("batches")?
        .set(key.to_owned(), to_json(batch)?)?;
    Ok(())
}

impl Batches {
    /// Plan the batch of `agents` (ordinal and scope, in call order) in
    /// the session's `facts`, beside every running batch.
    ///
    /// # Errors
    ///
    /// The batch's refusal.
    pub(crate) fn admit(
        &self,
        facts: &Facts,
        agents: &[(u32, Vec<String>)],
    ) -> Result<Batch, BatchRefusal> {
        let running: Vec<&Batch> = self
            .batches
            .values()
            .filter(|batch| !batch.settled())
            .collect();
        plan(facts.room.clone(), &facts.write_scope, &running, agents)
    }
}

/// Record agent `ordinal`'s end in batch `key` inside a commit; whether
/// the batch settled with it.
pub(crate) async fn tx_end(
    tx: &Tx,
    conversation_id: ConversationId,
    key: &str,
    ordinal: u32,
    outcome: Outcome,
    patch: Patch,
) -> SessionResult<bool> {
    let Some(batch) = tx_batches(tx, conversation_id)
        .await?
        .batches
        .shift_remove(key)
    else {
        return Ok(false);
    };
    let ended = batch.ended(ordinal, outcome, patch);
    tx_put_batch(tx, conversation_id, key, &ended).await?;
    Ok(ended.settled())
}

/// Cancel every batch of `keys` that did not settle, inside a commit.
pub(crate) async fn tx_cancel(
    tx: &Tx,
    conversation_id: ConversationId,
    keys: &[String],
) -> SessionResult<()> {
    let batches = tx_batches(tx, conversation_id).await?;
    for key in keys {
        if let Some(batch) = batches.batches.get(key) {
            if !batch.settled() {
                let cancelled = Batch {
                    cancelled: true,
                    ..batch.clone()
                };
                tx_put_batch(tx, conversation_id, key, &cancelled).await?;
            }
        }
    }
    Ok(())
}
