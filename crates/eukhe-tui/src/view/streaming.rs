//! A streaming assistant entry's render state. Text arrives a few times a
//! second while frames run at the spinner's pace, so most frames see the
//! message unchanged: those replay its last render whole, and a frame that
//! needs only the rows on screen copies only those.

use super::AgentView;
use crate::chat::{render_assistant, AssistantMessage, Detail};
use crate::markdown::MarkdownBlockCache;
use crate::Line;

/// One streaming entry's caches: the per-block cache (settled blocks
/// replay while the final block grows) and the last full render.
#[derive(Default)]
pub(super) struct StreamingRender {
    blocks: MarkdownBlockCache,
    last: Option<LastRender>,
}

/// A full render and every input it was rendered from.
struct LastRender {
    message: AssistantMessage,
    detail: Detail,
    theme_generation: u64,
    code_block_indent: String,
    width: usize,
    preceded_by_tool_activity: bool,
    rows: Vec<Line>,
}

impl AgentView {
    /// Hand the rows of the streaming assistant `message` at `index` to
    /// `read`, re-rendering only when an input changed since the last
    /// frame.
    pub(super) fn with_streaming_rows<R>(
        &self,
        index: usize,
        message: &AssistantMessage,
        width: usize,
        read: impl FnOnce(&[Line]) -> R,
    ) -> R {
        let preceded_by_tool_activity =
            index > 0 && Self::is_compact_neighbor(&self.chat[index - 1]);
        let theme_generation = self.theme.generation();
        let mut caches = self.md_caches.borrow_mut();
        let state = caches.entry(index).or_default();
        let current = state.last.as_ref().is_some_and(|last| {
            last.width == width
                && last.detail == self.detail
                && last.theme_generation == theme_generation
                && last.preceded_by_tool_activity == preceded_by_tool_activity
                && last.code_block_indent == self.code_block_indent
                && last.message == *message
        });
        if !current {
            state.last = None;
        }
        let last = state.last.get_or_insert_with(|| LastRender {
            rows: render_assistant(
                message,
                self.detail,
                &self.theme,
                &self.code_block_indent,
                width,
                preceded_by_tool_activity,
                &mut state.blocks,
            ),
            message: message.clone(),
            detail: self.detail,
            theme_generation,
            code_block_indent: self.code_block_indent.clone(),
            width,
            preceded_by_tool_activity,
        });
        read(&last.rows)
    }
}
