//! Loop updates for the attached surfaces (the `loop_update` event): the
//! status of one conversation's loop, emitted first at subscription and
//! then after every commit that changes its `eukhe.loop` document,
//! deduplicated (a commit that writes the same status emits nothing).

use std::sync::Arc;

use eukhe_chord::context::{await_with_context, Context};
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{CommitListener, SessionResult, Unsubscribe};
use eukhe_durable::types::{
    CommitChange, CommitPublication, ConversationId, DocumentCommitChange, DocumentIdentity,
};
use eukhe_types::loop_mode::LoopStatus;
use tokio::sync::mpsc;
use tokio::task::JoinHandle;

use super::docs::LOOP_DOC_KIND;
use super::loop_status;

/// A live stream of one conversation's loop updates. Dropping it stops
/// the subscription.
pub struct LoopUpdates {
    receiver: mpsc::UnboundedReceiver<LoopStatus>,
    unsubscribe: Unsubscribe,
    task: JoinHandle<()>,
}

impl LoopUpdates {
    /// The next changed status; `None` once the Harness closed or a read
    /// failed.
    pub async fn next(&mut self) -> Option<LoopStatus> {
        self.receiver.recv().await
    }
}

impl Drop for LoopUpdates {
    fn drop(&mut self) {
        self.unsubscribe.unsubscribe();
        self.task.abort();
    }
}

/// Whether `publication` changed the loop document of `conversation_id`.
fn changes_loop(publication: &CommitPublication, conversation_id: ConversationId) -> bool {
    publication.changes.iter().any(|change| match change {
        CommitChange::Document(DocumentCommitChange::Document {
            record,
            conversation_id: owner,
            ..
        }) => record.kind() == LOOP_DOC_KIND && *owner == Some(conversation_id),
        CommitChange::Document(DocumentCommitChange::Copy {
            record,
            conversation_id: owner,
            ..
        }) => record.kind() == LOOP_DOC_KIND && *owner == conversation_id,
        CommitChange::Conversation(_)
        | CommitChange::Entry(_)
        | CommitChange::Task(_)
        | CommitChange::Submission(_) => false,
    })
}

/// Watch the loop of `conversation_id`: the current status first, then
/// every change. Cancelling `cx` ends the stream.
///
/// # Errors
///
/// The Session is closed.
pub fn watch_loop_updates(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<LoopUpdates> {
    let (ticks, mut ticked) = mpsc::unbounded_channel::<()>();
    let listener: CommitListener = Arc::new(move |publication, _| {
        if changes_loop(publication, conversation_id) {
            // A closed receiver means the stream ended; nothing to notify.
            let _ = ticks.send(());
        }
    });
    let unsubscribe = harness.subscribe_commits(listener)?;
    let (sender, receiver) = mpsc::unbounded_channel();
    let reader = harness.clone();
    let cx = cx.clone();
    let task = tokio::spawn(async move {
        let mut last: Option<LoopStatus> = None;
        loop {
            let Ok(status) = loop_status(&reader, conversation_id, &cx).await else {
                return;
            };
            if last.as_ref() != Some(&status) {
                last = Some(status.clone());
                if sender.send(status).is_err() {
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
    Ok(LoopUpdates {
        receiver,
        unsubscribe,
        task,
    })
}
