//! The RPC handlers' reads of the live durable session: the main
//! conversation's live and inbox documents, its fork-aware history, its
//! context as wire `AgentMessage` JSON, and its resolved model.

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_core::durable::EukheSession;
use eukhe_durable::harness::types::Agent;
use eukhe_durable::harness::{
    Conversation, ConversationEntryQuery, Harness, InboxState, LiveState, INBOX_DOC, LIVE_DOC,
};
use eukhe_durable::types::{ConversationId, DocumentReaderExt, EntryRecord};
use eukhe_types::pi_ai::{Model, UserContent, UserContentBlock};
use serde_json::Value;

use crate::worker::durable_host::wire_messages::transcript_messages;

/// Entries read per history page.
const HISTORY_PAGE: usize = 256;

/// The context the RPC handlers run their durable operations under: the
/// connection never cancels an admitted operation (the TS handlers await
/// their session calls to completion).
pub(crate) fn rpc_context() -> Context {
    BACKGROUND_CONTEXT.clone()
}

/// The `pi.live` document of `conversation_id` (the initial state when
/// absent).
pub(crate) async fn live_state(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> Result<LiveState, String> {
    match harness
        .snapshot(&LIVE_DOC, conversation_id, cx)
        .await
        .map_err(|error| error.to_string())?
    {
        Some(value) => from_json(&JsonValue::Object(value)).map_err(|error| error.to_string()),
        None => Ok(LiveState::default()),
    }
}

/// The `pi.inbox` document of `conversation_id` (empty when absent).
pub(crate) async fn inbox_state(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> Result<InboxState, String> {
    match harness
        .snapshot(&INBOX_DOC, conversation_id, cx)
        .await
        .map_err(|error| error.to_string())?
    {
        Some(value) => from_json(&JsonValue::Object(value)).map_err(|error| error.to_string()),
        None => Ok(InboxState::default()),
    }
}

/// Whether a run is active on `conversation_id` (`pi.live.run`).
pub(crate) async fn is_busy(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> Result<bool, String> {
    Ok(live_state(harness, conversation_id, cx)
        .await?
        .run
        .is_some())
}

/// The fork-aware history of `conversation`, oldest first.
pub(crate) async fn history_entries(
    conversation: &Conversation,
    cx: &Context,
) -> Result<Vec<EntryRecord>, String> {
    let mut entries = Vec::new();
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(ConversationEntryQuery::default(), HISTORY_PAGE, cursor, cx)
            .await
            .map_err(|error| error.to_string())?;
        entries.extend(page.items);
        match page.next {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    entries.reverse();
    Ok(entries)
}

/// The active context of `conversation` as wire `AgentMessage` JSON (TS
/// `session.state.messages`).
pub(crate) async fn context_messages(
    conversation: &Conversation,
    cx: &Context,
) -> Result<Vec<Value>, String> {
    let view = conversation
        .context(cx)
        .await
        .map_err(|error| error.to_string())?;
    Ok(transcript_messages(&view.entries))
}

/// The main conversation's resolved agent.
pub(crate) async fn main_agent(session: &EukheSession, cx: &Context) -> Result<Agent, String> {
    session
        .main()
        .agent(cx)
        .await
        .map_err(|error| error.to_string())
}

/// The catalog model the agent's model reference names, when it resolves.
pub(crate) fn agent_model(session: &EukheSession, agent: &Agent) -> Option<Model> {
    let model = agent.model.as_ref()?;
    session
        .deps()
        .models
        .get_model(&model.provider, &model.model_id)
}

/// One queued input's text preview: its text blocks joined by a space
/// (the TS action-preview shape; images contribute nothing).
pub(crate) fn content_preview(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.as_str()),
                UserContentBlock::Image(_) => None,
            })
            .collect::<Vec<_>>()
            .join(" "),
    }
}

/// The concatenated text blocks of the last assistant message in
/// `messages` (TS `getLastAssistantText`); `None` without one.
pub(crate) fn last_assistant_text(messages: &[Value]) -> Option<String> {
    let message = messages
        .iter()
        .rev()
        .find(|message| message.get("role").and_then(Value::as_str) == Some("assistant"))?;
    Some(
        message
            .get("content")
            .and_then(Value::as_array)
            .map(|blocks| {
                blocks
                    .iter()
                    .filter(|block| block.get("type").and_then(Value::as_str) == Some("text"))
                    .filter_map(|block| block.get("text").and_then(Value::as_str))
                    .collect::<String>()
            })
            .unwrap_or_default(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::pi_ai::{ImageContent, TextContent};
    use serde_json::json;

    #[test]
    fn previews_join_text_blocks() {
        let content = UserContent::Blocks(vec![
            UserContentBlock::Text(TextContent::new("look")),
            UserContentBlock::Image(ImageContent {
                data: "aGk=".to_string(),
                mime_type: "image/png".to_string(),
            }),
            UserContentBlock::Text(TextContent::new("here")),
        ]);
        assert_eq!(content_preview(&content), "look here");
        assert_eq!(content_preview(&UserContent::Text("plain".into())), "plain");
    }

    #[test]
    fn last_assistant_text_concatenates_text_blocks() {
        let messages = vec![
            json!({ "role": "assistant", "content": [{ "type": "text", "text": "old" }] }),
            json!({ "role": "user", "content": "hi" }),
            json!({ "role": "assistant", "content": [
                { "type": "thinking", "thinking": "hm" },
                { "type": "text", "text": "a" },
                { "type": "text", "text": "b" },
            ] }),
            json!({ "role": "toolResult", "content": [] }),
        ];
        assert_eq!(last_assistant_text(&messages), Some("ab".to_string()));
        assert_eq!(last_assistant_text(&messages[1..2]), None);
    }
}
