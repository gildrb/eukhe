//! Acceptance updates for the attached surfaces (the `acceptance_update`
//! event): the acceptance of one conversation as every surface reads it,
//! emitted first at subscription and then after every commit that changes
//! its `eukhe.acceptance` document, deduplicated by value.

use std::sync::Arc;

use eukhe_chord::context::{await_with_context, Context};
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{CommitListener, SessionResult, Unsubscribe};
use eukhe_durable::types::{
    CommitChange, CommitPublication, ConversationId, DocumentCommitChange, DocumentIdentity,
};
use eukhe_types::acceptance::AcceptanceState;
use tokio::sync::mpsc;
use tokio::task::JoinHandle;

use super::docs::ACCEPTANCE_DOC_KIND;
use super::ops::acceptance_state;

/// A live stream of one conversation's acceptance updates. Dropping it
/// stops the subscription.
pub struct AcceptanceUpdates {
    receiver: mpsc::UnboundedReceiver<AcceptanceState>,
    unsubscribe: Unsubscribe,
    task: JoinHandle<()>,
}

impl AcceptanceUpdates {
    /// The next changed acceptance; `None` once the Harness closed or a
    /// read failed.
    pub async fn next(&mut self) -> Option<AcceptanceState> {
        self.receiver.recv().await
    }
}

impl Drop for AcceptanceUpdates {
    fn drop(&mut self) {
        self.unsubscribe.unsubscribe();
        self.task.abort();
    }
}

/// Whether `publication` changed the acceptance document of
/// `conversation_id`.
fn changes_acceptance(publication: &CommitPublication, conversation_id: ConversationId) -> bool {
    publication.changes.iter().any(|change| match change {
        CommitChange::Document(DocumentCommitChange::Document {
            record,
            conversation_id: owner,
            ..
        }) => record.kind() == ACCEPTANCE_DOC_KIND && *owner == Some(conversation_id),
        CommitChange::Document(DocumentCommitChange::Copy {
            record,
            conversation_id: owner,
            ..
        }) => record.kind() == ACCEPTANCE_DOC_KIND && *owner == conversation_id,
        CommitChange::Conversation(_)
        | CommitChange::Entry(_)
        | CommitChange::Task(_)
        | CommitChange::Submission(_) => false,
    })
}

/// Watch the acceptance of `conversation_id`: the current state first,
/// then every change. Cancelling `cx` ends the stream.
///
/// # Errors
///
/// The Session is closed.
pub fn watch_acceptance_updates(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<AcceptanceUpdates> {
    let (ticks, mut ticked) = mpsc::unbounded_channel::<()>();
    let listener: CommitListener = Arc::new(move |publication, _| {
        if changes_acceptance(publication, conversation_id) {
            // A closed receiver means the stream ended; nothing to notify.
            let _ = ticks.send(());
        }
    });
    let unsubscribe = harness.subscribe_commits(listener)?;
    let (sender, receiver) = mpsc::unbounded_channel();
    let reader = harness.clone();
    let cx = cx.clone();
    let task = tokio::spawn(async move {
        let mut last: Option<AcceptanceState> = None;
        loop {
            let Ok(state) = acceptance_state(&reader, conversation_id, &cx).await else {
                return;
            };
            if last.as_ref() != Some(&state) {
                last = Some(state.clone());
                if sender.send(state).is_err() {
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
    Ok(AcceptanceUpdates {
        receiver,
        unsubscribe,
        task,
    })
}
