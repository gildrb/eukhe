//! Shared reads of the autonomous extension, the acceptance verifier, the
//! loop mode and the Director stack.

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_durable::harness::{Conversation, Harness, InboxItem, InboxState, INBOX_DOC};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReader};
use eukhe_types::budget::BudgetReport;

use super::docs::read_doc;
use crate::durable::budget::BudgetGate;

/// The session budget's report (`None`: no budget), read on a blocking
/// thread.
///
/// # Errors
///
/// The read did not finish (the runtime is shutting down).
pub async fn budget_report(budget: &Arc<BudgetGate>) -> SessionResult<Option<BudgetReport>> {
    let gate = Arc::clone(budget);
    tokio::task::spawn_blocking(move || gate.report())
        .await
        .map_err(SessionError::other)
}

/// The conversation `conversation_id` of `harness`.
///
/// # Errors
///
/// Read failures, or no such conversation.
pub(crate) async fn conversation_of(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Conversation> {
    harness
        .conversation(conversation_id, cx)
        .await?
        .ok_or_else(|| {
            SessionError::error(format!("Conversation {conversation_id} does not exist"))
        })
}

/// Whether queued user input owns the next boundary (old
/// `session_input_queued`).
///
/// # Errors
///
/// Read failures.
pub(crate) async fn user_input_queued(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<bool> {
    let inbox: InboxState = read_doc(reader, &INBOX_DOC, conversation_id, cx)
        .await?
        .unwrap_or_default();
    Ok(inbox.items.iter().any(|item| match item {
        InboxItem::Steer { .. } | InboxItem::FollowUp { .. } => true,
        InboxItem::Write { .. } => false,
    }))
}
