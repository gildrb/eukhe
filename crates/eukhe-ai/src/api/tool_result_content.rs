//! The blocks a tool result sends to Anthropic Messages and Bedrock
//! Converse: Anthropic refuses a `tool_result` marked `is_error` that
//! carries an image block ("all content must be type `text` if `is_error`
//! is true"), and the result stays in the transcript, so every later
//! request of the session would fail. The compiled core decides each block
//! (`eukhe_bend::rules::tool_result`, `laws/tool_result.bend`): an error
//! result's images go as the text line `[image omitted: error result]`,
//! its text blocks as they are; a successful result keeps every block.

use std::borrow::Cow;

use eukhe_bend::rules::tool_result::{self, Block, Sent};
use eukhe_types::pi_ai::{TextContent, UserContentBlock};

/// The blocks a tool result with `content` sends, in order: a block kept
/// is borrowed, a block sent as a line is a new text block.
pub(crate) fn sent_blocks(
    content: &[UserContentBlock],
    is_error: bool,
) -> Vec<Cow<'_, UserContentBlock>> {
    let kinds: Vec<Block> = content
        .iter()
        .map(|block| match block {
            UserContentBlock::Text(_) => Block::Text,
            UserContentBlock::Image(_) => Block::Image,
        })
        .collect();
    // One answer per block: the rule refuses a reply of another count.
    content
        .iter()
        .zip(tool_result::sent(is_error, &kinds))
        .map(|(block, sent)| match sent {
            Sent::Keep => Cow::Borrowed(block),
            Sent::Line(line) => Cow::Owned(UserContentBlock::Text(TextContent::new(line))),
        })
        .collect()
}
