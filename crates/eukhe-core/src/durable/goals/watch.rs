//! Goal updates for the attached surfaces (the `goal_update` event): the
//! served goal of one conversation, emitted first at subscription and then
//! after every commit that changes its `eukhe.goal` document, deduplicated
//! by `crate::goals::goal_update_dedupe_projection` (the goal's age ticking
//! alone never re-emits).

use eukhe_chord::context::{await_with_context, Context};
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{CommitListener, SessionResult, Unsubscribe};
use eukhe_durable::types::{
    CommitChange, CommitPublication, ConversationId, DocumentCommitChange, DocumentIdentity,
};
use std::sync::Arc;
use tokio::sync::mpsc;
use tokio::task::JoinHandle;

use super::ops::goal_state;
use crate::goals::{goal_update_dedupe_projection, GoalState};

const GOAL_DOC_KIND: &str = "eukhe.goal";

/// A live stream of one conversation's goal updates. Dropping it stops the
/// subscription.
pub struct GoalUpdates {
    receiver: mpsc::UnboundedReceiver<GoalState>,
    unsubscribe: Unsubscribe,
    task: JoinHandle<()>,
}

impl GoalUpdates {
    /// The next changed goal; `None` once the Harness closed or a read
    /// failed.
    pub async fn next(&mut self) -> Option<GoalState> {
        self.receiver.recv().await
    }
}

impl Drop for GoalUpdates {
    fn drop(&mut self) {
        self.unsubscribe.unsubscribe();
        self.task.abort();
    }
}

/// Whether `publication` changed the goal document of `conversation_id`.
fn changes_goal(publication: &CommitPublication, conversation_id: ConversationId) -> bool {
    publication.changes.iter().any(|change| match change {
        CommitChange::Document(DocumentCommitChange::Document {
            record,
            conversation_id: owner,
            ..
        }) => record.kind() == GOAL_DOC_KIND && *owner == Some(conversation_id),
        CommitChange::Document(DocumentCommitChange::Copy {
            record,
            conversation_id: owner,
            ..
        }) => record.kind() == GOAL_DOC_KIND && *owner == conversation_id,
        CommitChange::Conversation(_)
        | CommitChange::Entry(_)
        | CommitChange::Task(_)
        | CommitChange::Submission(_) => false,
    })
}

/// Watch the goal of `conversation_id`: the current goal first, then every
/// change. Cancelling `cx` ends the stream.
///
/// # Errors
///
/// The Session is closed.
pub fn watch_goal_updates(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<GoalUpdates> {
    let (ticks, mut ticked) = mpsc::unbounded_channel::<()>();
    let listener: CommitListener = Arc::new(move |publication, _| {
        if changes_goal(publication, conversation_id) {
            // A closed receiver means the stream ended; nothing to notify.
            let _ = ticks.send(());
        }
    });
    let unsubscribe = harness.subscribe_commits(listener)?;
    let (sender, receiver) = mpsc::unbounded_channel();
    let reader = harness.clone();
    let cx = cx.clone();
    let task = tokio::spawn(async move {
        let mut last: Option<GoalState> = None;
        loop {
            let Ok(goal) = goal_state(&reader, conversation_id, &cx).await else {
                return;
            };
            let unchanged = last.as_ref().is_some_and(|last| {
                goal_update_dedupe_projection(last) == goal_update_dedupe_projection(&goal)
            });
            if !unchanged {
                last = Some(goal.clone());
                if sender.send(goal).is_err() {
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
    Ok(GoalUpdates {
        receiver,
        unsubscribe,
        task,
    })
}
