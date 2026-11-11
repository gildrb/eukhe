//! Shared chat framing decisions.
use super::{AssistantMessage, Detail, MessageBlock};
use crate::markdown::MarkdownStyle;
use crate::style::Modifier;
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

/// A rendered markdown row with nothing visible on it: the blank rows
/// markdown puts between blocks, which the dense thinking block drops.
pub(super) fn is_blank_row(line: &[crate::Span]) -> bool {
    line.iter().all(|span| span.content.trim().is_empty())
}

/// The cache tag the thinking block renders under.
pub(super) const THINKING_CACHE_TAG: &str = "thinking";

/// The thinking block's style: the theme's `thinkingText` colour, italic,
/// on every markdown element, so reasoning never reads as answer text.
pub(super) fn thinking_style(md: &MarkdownStyle, theme: &Theme) -> MarkdownStyle {
    let mut md = md.clone();
    let thinking = theme
        .fg_style(ThemeColor::ThinkingText)
        .add_modifier(Modifier::ITALIC);
    // The thinking code blocks never highlight: one quiet style throughout.
    md.syntax = None;
    md.body = thinking;
    md.heading = thinking;
    md.link = thinking;
    md.link_url = thinking;
    md.code = thinking;
    md.code_block = thinking;
    md.code_block_border = thinking;
    md.quote = thinking;
    md.quote_border = thinking;
    md.hr = thinking;
    md.list_bullet = thinking;
    md
}
