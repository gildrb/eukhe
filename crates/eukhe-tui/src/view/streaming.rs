//! A streaming assistant entry's render state. Text arrives a few times a
//! second while frames run at the spinner's pace, so most frames see the
//! message unchanged: those replay its last render whole, and a frame that
//! needs only the rows on screen copies only those.
//!
//! The text shows at a pace (`crate::pace`, docs/interface.md S8 rule 2):
//! each frame reveals part of what arrived, and a message that stopped
//! streaming stays live until all of it shows.

use super::AgentView;
use crate::chat::{
    render_assistant, AssistantLead, AssistantMessage, ChatEntry, Detail, MessageBlock,
};
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
    lead: AssistantLead,
    rows: Vec<Line>,
}

/// The characters of `message` that render at `detail`: its text, and
/// its thinking when the detail level shows it.
fn visible_chars(message: &AssistantMessage, detail: Detail) -> usize {
    message
        .blocks
        .iter()
        .map(|block| match block {
            MessageBlock::Thinking(text) if detail.show_thinking() => text.chars().count(),
            MessageBlock::Thinking(_) => 0,
            MessageBlock::Text(text) => text.chars().count(),
        })
        .sum()
}

impl AgentView {
    /// One frame of every pace (model `pace.step`): each assistant entry
    /// not in scrollback that streams (or did and still has a backlog)
    /// takes the characters that arrived since the last frame, then
    /// reveals one paced step. A detail change (Ctrl+O) that shows or
    /// hides thinking is no arrival: each pace keeps its place in the
    /// message, so the text on screen stays. The loader row a reveal
    /// held up after the turn ended goes down with the frame that shows
    /// the last of the text.
    pub(super) fn advance_paces(&mut self) {
        let (from, to) = (self.pace_detail, self.detail);
        self.pace_detail = to;
        for index in self.ledger.committed()..self.chat.len() {
            let ChatEntry::Assistant(message) = &self.chat[index] else {
                continue;
            };
            let arrived = visible_chars(message, to);
            let pace = match self.paces.entry(index) {
                std::collections::hash_map::Entry::Occupied(slot) => slot.into_mut(),
                std::collections::hash_map::Entry::Vacant(slot) if message.streaming => {
                    slot.insert(crate::pace::Pace::default())
                }
                std::collections::hash_map::Entry::Vacant(_) => continue,
            };
            if from != to {
                // The count of `chars` characters visible at `from`, in
                // characters visible at `to`: a block hidden at `from`
                // and shown at `to` counts whole when it sits before the
                // place, and a block shown at `from` only counts at `to`
                // when `to` shows it.
                pace.recount(|chars| {
                    let mut left = chars;
                    let mut count = 0;
                    for block in &message.blocks {
                        if left == 0 {
                            break;
                        }
                        let (len, shows_from, shows_to) = match block {
                            MessageBlock::Thinking(text) => (
                                text.chars().count(),
                                from.show_thinking(),
                                to.show_thinking(),
                            ),
                            MessageBlock::Text(text) => (text.chars().count(), true, true),
                        };
                        match (shows_from, shows_to) {
                            (true, shows_to) => {
                                let take = len.min(left);
                                left -= take;
                                if shows_to {
                                    count += take;
                                }
                            }
                            (false, true) => count += len,
                            (false, false) => {}
                        }
                    }
                    count
                });
            }
            match arrived.checked_sub(pace.recv()) {
                Some(more) => pace.chunk(more),
                None => pace.shrink_to(arrived),
            }
            pace.frame(self.pace_rate);
        }
        if !self.is_pacing() {
            self.loader_held_by_pace = None;
        }
    }

    /// Whether the pace of the entry at `index` has all its text on
    /// screen (an entry never paced has).
    pub(super) fn pace_drained(&self, index: usize) -> bool {
        self.paces.get(&index).is_none_or(|pace| pace.drained())
    }

    /// The part of `message` (the entry at `index`) its pace shows:
    /// `None` when it shows all of it. The cut keeps the blocks in order
    /// and holds the error row back until the text is all on screen.
    pub(super) fn paced_message(
        &self,
        index: usize,
        message: &AssistantMessage,
    ) -> Option<AssistantMessage> {
        let pace = self.paces.get(&index).filter(|pace| !pace.drained())?;
        let mut left = pace.shown();
        let mut blocks = Vec::with_capacity(message.blocks.len());
        for block in &message.blocks {
            let (text, shows) = match block {
                MessageBlock::Thinking(text) => (text, self.detail.show_thinking()),
                MessageBlock::Text(text) => (text, true),
            };
            if !shows {
                blocks.push(block.clone());
                continue;
            }
            if left == 0 {
                break;
            }
            let cut: String = text.chars().take(left).collect();
            left -= cut.chars().count();
            blocks.push(match block {
                MessageBlock::Thinking(_) => MessageBlock::Thinking(cut),
                MessageBlock::Text(_) => MessageBlock::Text(cut),
            });
        }
        Some(AssistantMessage {
            blocks,
            has_tool_calls: message.has_tool_calls,
            streaming: true,
            error: None,
            aborted: false,
        })
    }

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
        let lead = self.assistant_lead(index, message);
        let theme_generation = self.theme.generation();
        let mut caches = self.md_caches.borrow_mut();
        let state = caches.entry(index).or_default();
        let current = state.last.as_ref().is_some_and(|last| {
            last.width == width
                && last.detail == self.detail
                && last.theme_generation == theme_generation
                && last.lead == lead
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
                lead,
                &mut state.blocks,
            ),
            message: message.clone(),
            detail: self.detail,
            theme_generation,
            code_block_indent: self.code_block_indent.clone(),
            width,
            lead,
        });
        read(&last.rows)
    }
}
