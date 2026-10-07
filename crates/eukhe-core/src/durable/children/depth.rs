//! The session's runtime RLM depth bound (`set_rlm_max_depth`): kept in the
//! `eukhe.rlm.max-depth` conversation document so the bound a user set
//! survives a restart (the old engine kept an `rlm_max_depth_state` custom
//! row and re-seeded from it).

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReader, DocumentReaderExt, LatestFork};
use serde::{Deserialize, Serialize};

/// The override of one conversation.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct MaxDepthState {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) max_depth: Option<u32>,
}

pub(crate) static MAX_DEPTH_DOC: ConversationDoc<MaxDepthState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.rlm.max-depth",
        version: 1,
        initial: MaxDepthState::default,
        migrate: None,
        checkpoint_when: None,
    },
    // A fork starts from the session's configured bound.
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.rlm.max-depth has a valid version"),
};

/// The runtime depth bound of `conversation_id`, when one was set.
///
/// # Errors
///
/// Document read failures.
pub async fn read_max_depth_override(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Option<u32>> {
    match reader.snapshot(&MAX_DEPTH_DOC, conversation_id, cx).await? {
        None => Ok(None),
        Some(value) => {
            let state: MaxDepthState = from_json(&JsonValue::Object(value))?;
            Ok(state.max_depth)
        }
    }
}

/// Set (or, with `None`, clear) the runtime depth bound of
/// `conversation_id` in its own commit.
///
/// # Errors
///
/// A missing conversation or a failed commit.
pub async fn set_max_depth_override(
    harness: &Harness,
    conversation_id: ConversationId,
    max_depth: Option<u32>,
    cx: &Context,
) -> SessionResult<()> {
    let conversation = harness
        .conversation(conversation_id, cx)
        .await?
        .ok_or_else(|| {
            SessionError::error(format!("Conversation {conversation_id} does not exist"))
        })?;
    conversation
        .commit(
            move |tx| async move {
                let draft = tx.doc(&MAX_DEPTH_DOC, conversation_id).await?;
                match max_depth {
                    Some(max_depth) => draft.set("maxDepth", to_json(&max_depth)?)?,
                    None => draft.delete("maxDepth")?,
                }
                Ok(())
            },
            cx,
        )
        .await
}
