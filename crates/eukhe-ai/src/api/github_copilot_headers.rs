//! Port of `api/github-copilot-headers.ts`.

use eukhe_types::pi_ai::{IndexMap, Message, UserContent, UserContentBlock};

/// Copilot `X-Initiator`: `"agent"` when the last message is not a user
/// message (a follow-up after assistant/tool messages), else `"user"`.
#[must_use]
pub fn infer_copilot_initiator(messages: &[Message]) -> &'static str {
    match messages.last() {
        Some(last) if !matches!(last, Message::User(_)) => "agent",
        Some(_) | None => "user",
    }
}

fn has_image(blocks: &[UserContentBlock]) -> bool {
    blocks
        .iter()
        .any(|block| matches!(block, UserContentBlock::Image(_)))
}

/// Whether any user or tool-result message carries an image (Copilot
/// requires `Copilot-Vision-Request` then).
#[must_use]
pub fn has_copilot_vision_input(messages: &[Message]) -> bool {
    messages.iter().any(|message| match message {
        Message::User(user) => match &user.content {
            UserContent::Blocks(blocks) => has_image(blocks),
            UserContent::Text(_) => false,
        },
        Message::ToolResult(result) => has_image(&result.content),
        Message::System(_) | Message::Assistant(_) => false,
    })
}

/// Per-request Copilot headers, in TS insertion order.
#[must_use]
pub fn build_copilot_dynamic_headers(
    messages: &[Message],
    has_images: bool,
) -> IndexMap<String, String> {
    let mut headers = IndexMap::new();
    headers.insert(
        "X-Initiator".to_owned(),
        infer_copilot_initiator(messages).to_owned(),
    );
    headers.insert("Openai-Intent".to_owned(), "conversation-edits".to_owned());
    if has_images {
        headers.insert("Copilot-Vision-Request".to_owned(), "true".to_owned());
    }
    headers
}
