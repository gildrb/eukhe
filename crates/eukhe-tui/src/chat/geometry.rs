//! Shared chat framing decisions.
use super::{AssistantMessage, Detail, MessageBlock};
use crate::markdown::MarkdownStyle;
use crate::theme::{Theme, ThemeColor};

pub(super) fn user_mask(text: &str) -> crate::prompt_highlight::PromptTokenMask {
    let (command_end, include_bare_separator) =
        crate::prompt_highlight::user_message_command_span(text);
    crate::prompt_highlight::PromptTokenMask::new(text, command_end, include_bare_separator)
}

pub(super) fn visible_blocks(message: &AssistantMessage, detail: Detail) -> Vec<&MessageBlock> {
    message
        .blocks
        .iter()
        .filter(|block| match block {
            MessageBlock::Thinking(text) => detail.show_thinking() && !text.trim().is_empty(),
            MessageBlock::Text(text) => !text.trim().is_empty(),
        })
        .collect()
}

pub(super) fn trailing_space(
    message: &AssistantMessage,
    has_visible_content: bool,
    preceded_by_tool_activity: bool,
) -> bool {
    message.has_tool_calls && (has_visible_content || message.aborted || !preceded_by_tool_activity)
}

/// The cache tag the dim thinking block renders under.
pub(super) const THINKING_CACHE_TAG: &str = "dim";

pub(super) fn thinking_style(md: &MarkdownStyle, theme: &Theme) -> MarkdownStyle {
    let mut md = md.clone();
    let dim = theme.fg_style(ThemeColor::Dim);
    // TS `getThinkingMarkdownTheme` replaces `highlightCode` with uniform
    // dim lines: the thinking code blocks never highlight.
    md.syntax = None;
    md.body = dim;
    md.heading = dim;
    md.link = dim;
    md.link_url = dim;
    md.code = dim;
    md.code_block = dim;
    md.code_block_border = dim;
    md.quote = dim;
    md.quote_border = dim;
    md.hr = dim;
    md.list_bullet = dim;
    md
}
