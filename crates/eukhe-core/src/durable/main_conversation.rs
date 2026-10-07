//! The session's main conversation: the one the user talks to. It starts as
//! the root; forks and tree navigation move it by committing the
//! `eukhe.session` document in the same commit that creates or selects the
//! conversation.

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::documents::{DocDefinition, SessionDoc};
use eukhe_durable::harness::json::assign_json;
use eukhe_durable::harness::{Conversation, Harness};
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::types::{ConversationId, DocumentReaderExt, ROOT_CONVERSATION_ID};
use serde::{Deserialize, Serialize};

/// The `eukhe.session` document value: `{main?}`; absent `main` is the root.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SessionState {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub main: Option<ConversationId>,
}

/// The session-scope `eukhe.session` document (version 1).
pub static SESSION_DOC: SessionDoc<SessionState> = match SessionDoc::define(DocDefinition {
    kind: "eukhe.session",
    version: 1,
    initial: SessionState::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.session has a valid version"),
};

/// Make `conversation_id` the session's main conversation, inside `tx`.
///
/// # Errors
///
/// The document cannot be acquired or written.
pub async fn set_main_conversation(tx: &Tx, conversation_id: ConversationId) -> SessionResult<()> {
    let draft = tx.doc(&SESSION_DOC, ()).await?;
    let value = eukhe_chord::json::to_json(&conversation_id).map_err(SessionError::other)?;
    assign_json(&draft, "main", &value)?;
    Ok(())
}

/// The id of the session's main conversation (the root when unset).
///
/// # Errors
///
/// The document cannot be read or decoded.
pub async fn main_conversation_id(
    harness: &Harness,
    cx: &Context,
) -> SessionResult<ConversationId> {
    let Some(value) = harness.snapshot(&SESSION_DOC, (), cx).await? else {
        return Ok(ROOT_CONVERSATION_ID);
    };
    let state: SessionState = from_json(&JsonValue::Object(value)).map_err(SessionError::other)?;
    Ok(state.main.unwrap_or(ROOT_CONVERSATION_ID))
}

/// The session's main conversation.
///
/// # Errors
///
/// The document cannot be read, or names a conversation that does not
/// exist.
pub async fn main_conversation(harness: &Harness, cx: &Context) -> SessionResult<Conversation> {
    let id = main_conversation_id(harness, cx).await?;
    harness
        .conversation(id, cx)
        .await?
        .ok_or_else(|| SessionError::error(format!("Main conversation {id} does not exist")))
}
