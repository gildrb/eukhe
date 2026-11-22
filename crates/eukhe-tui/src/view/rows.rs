//! The per-entry transcript row builders: the leading-blank rules and
//! `render_entry` -- the one producer of a chat entry's rows. A turn
//! reads as steps (owner ruling 2026-11-21, replacing the 2026-09 "one
//! dense trace" rule): one blank row between the user header and the
//! first step, between steps (a step is an assistant message's thinking
//! and text, then its tool rows), before the reply, and before the
//! footer; none inside a step.

use super::AgentView;
use crate::chat::{render_assistant, render_text_rows, render_user_block, ChatEntry};
use crate::theme::ThemeColor;
use crate::Line;

impl AgentView {
    /// The blank row before a tool row (tool card, agent message, shell
    /// completion) at `index`: a step's tool rows follow its assistant
    /// message and each other directly, and a tool row that opens a step
    /// (after a non-turn row, at the top, or after an assistant message
    /// that renders nothing) leads with one. An assistant message always
    /// leads with its own (`render_assistant`).
    pub(super) fn conversation_leading(&self, index: usize) -> bool {
        match index.checked_sub(1).map(|above| &self.chat[above]) {
            Some(ChatEntry::Assistant(message)) => !message.renders_rows(),
            Some(preceding) => !Self::is_compact_neighbor(preceding),
            None => true,
        }
    }

    /// Lay out one chat entry's transcript rows (the only producer of
    /// entry rows).
    pub(super) fn render_entry(
        &self,
        index: usize,
        entry: &ChatEntry,
        width: usize,
        first: bool,
    ) -> Vec<Line> {
        let detail = self.detail;
        match entry {
            ChatEntry::Status { text, kind } => {
                let style = match kind {
                    crate::chat::StatusKind::Info => self.theme.fg_style(ThemeColor::Dim),
                    crate::chat::StatusKind::Warning => self.theme.fg_style(ThemeColor::Warning),
                    crate::chat::StatusKind::Error => self.theme.fg_style(ThemeColor::Error),
                };
                let mut rows = Vec::new();
                rows.push(Vec::new());
                let body = render_text_rows(text, style, width);
                // A long informational row (a settled job's notice) folds
                // to its head; a warning or an error never folds.
                let foldable = matches!(kind, crate::chat::StatusKind::Info);
                rows.extend(crate::chat::fold_rows(
                    body,
                    foldable,
                    detail,
                    &self.theme,
                    width,
                    1,
                ));
                rows
            }
            ChatEntry::User { text } => {
                let mut rows = Vec::new();
                // TS `addMessageToChat` separates a user submission from
                // the components above it with `Spacer(1)` -- EXCEPT the
                // skill invocation's own argument text, which joins the
                // card below it without a spacer.
                let follows_skill_card =
                    index > 0 && matches!(self.chat[index - 1], ChatEntry::SkillInvocation(_));
                if !first && !follows_skill_card {
                    rows.push(Vec::new());
                }
                rows.extend(render_user_block(
                    text,
                    &self.theme,
                    &self.code_block_indent,
                    width,
                ));
                rows
            }
            ChatEntry::SlashCommand { text } => {
                // The echo row leads with a spacer when the chat is not
                // empty (TS adds `Spacer(1)` before the component).
                let mut rows = Vec::new();
                if !first {
                    rows.push(Vec::new());
                }
                rows.extend(crate::chat_slash::render_slash_command(
                    text,
                    &self.theme,
                    width,
                ));
                rows
            }
            ChatEntry::CompactionSummary {
                summary,
                tokens_before,
                custom_instructions,
            } => {
                // TS `addMessageToChat` conversation spacing: the summary
                // follows the previous component with `Spacer(1)` when not
                // first (in the rebuilt transcript it trails the kept
                // tail's echo row).
                let mut rows = Vec::new();
                if !first {
                    rows.push(Vec::new());
                }
                rows.extend(crate::compaction_row::render_compaction_summary(
                    summary,
                    *tokens_before,
                    custom_instructions.as_deref(),
                    // TS `applyChatExpansion` fans `toolOutputExpanded`
                    // out to every `ExpandableEventMessage` in the chat;
                    // `CompactionSummaryMessageComponent` renders the
                    // collapsed `EventSummary` until the Ctrl+O cycle
                    // reaches detail `all`.
                    detail.tool_output_expanded(),
                    &self.theme,
                    width,
                ));
                rows
            }
            ChatEntry::Assistant(message) => {
                // A streaming message renders through its per-entry state
                // (`streaming`): the block cache (TS's per-component
                // `blockCache`) replays settled blocks, the last render
                // replays whole while the message is unchanged. A message
                // whose pace still holds text back renders the part that
                // shows. A settled message's blocks are final, so its
                // rendered rows live once in the entry layout and the
                // cached copy is dropped (a resumed large session's
                // duplicate copy was the TUI's biggest single retained
                // allocation in the tui-memory census); any later
                // re-render rebuilds the same rows from the message's own
                // text.
                match (self.paced_message(index, message), message.streaming) {
                    (Some(shown), true | false) => {
                        self.with_streaming_rows(index, &shown, width, <[Line]>::to_vec)
                    }
                    (None, true) => {
                        self.with_streaming_rows(index, message, width, <[Line]>::to_vec)
                    }
                    (None, false) => {
                        self.md_caches.borrow_mut().remove(&index);
                        let mut settled = crate::markdown::MarkdownBlockCache::default();
                        render_assistant(
                            message,
                            detail,
                            &self.theme,
                            &self.code_block_indent,
                            width,
                            &mut settled,
                        )
                    }
                }
            }
            ChatEntry::Tool(card) => {
                // The leading blank row follows the turn rule
                // (`conversation_leading`): consecutive tool rows and
                // tool rows under an assistant message stay flush.
                let mut rows: Vec<Line> = Vec::new();
                if self.conversation_leading(index) {
                    rows.push(Vec::new());
                }
                rows.extend(crate::tool_card::render_tool_card(
                    card,
                    self.pulse_frame,
                    detail,
                    &self.theme,
                    width,
                    self.show_images,
                ));
                rows
            }
            ChatEntry::BashExecution(card) => {
                // TS `BashExecutionComponent` mounts with `Spacer(1)`
                // unless it follows an agent-message component
                // (`suppressLeadingSpace`, decided at mount time).
                let mut rows: Vec<Line> = Vec::new();
                if !card.suppress_leading_space {
                    rows.push(Vec::new());
                }
                // TS `keyText("tui.select.cancel")`: every key of the
                // binding joins the hint ("Esc/Ctrl+C").
                let cancel_hint = self.editor.keybindings().key_text("tui.select.cancel");
                rows.extend(crate::bash_card::render_bash_execution(
                    card,
                    self.pulse_frame,
                    detail.tool_output_expanded(),
                    &cancel_hint,
                    &self.theme,
                    width,
                ));
                rows
            }
            ChatEntry::AgentMessage(row) => crate::custom_message::render::render_agent_message(
                row,
                detail,
                &self.theme,
                width,
                self.conversation_leading(index),
            ),
            // TS `addMessageToChat`'s user case: `Spacer(1)` when the chat
            // is non-empty, then the card (the conversation-spacing scan the
            // agent-message rows use does not apply -- the TS user case is
            // the plain children-count check).
            ChatEntry::SkillInvocation(row) => {
                crate::custom_message::skill_invocation::render_skill_invocation(
                    row,
                    detail,
                    &self.theme,
                    width,
                    !first,
                )
            }
            // Injected rows above one turn group: only the first leads
            // with a blank row.
            ChatEntry::InjectedPrompt(row) => {
                crate::custom_message::injected_prompt::render_injected_prompt(
                    row,
                    detail,
                    &self.theme,
                    width,
                    !matches!(
                        index.checked_sub(1).map(|above| &self.chat[above]),
                        Some(ChatEntry::InjectedPrompt(_))
                    ),
                )
            }
            ChatEntry::ShellCompletion(row) => {
                crate::custom_message::render::render_shell_completion(
                    row,
                    detail,
                    &self.theme,
                    width,
                    self.conversation_leading(index),
                )
            }
            ChatEntry::RefinementOutcome(row) => {
                crate::custom_message::refinement::render_refinement_outcome(
                    row,
                    detail,
                    &self.theme,
                    width,
                )
            }
            ChatEntry::CustomPanel(row) => {
                crate::custom_message::render::render_custom_panel(row, &self.theme, width)
            }
            ChatEntry::ChatView(view) => {
                crate::chat_view_block::render_chat_view(view, detail, &self.theme, width, !first)
            }
            ChatEntry::Swarm(row) => {
                crate::swarm_block::render_swarm_row(row, detail, &self.theme, width, !first)
            }
            // The footer stands one blank row below the turn it closes.
            ChatEntry::TurnFooter(usage) => {
                let mut rows = vec![Vec::new()];
                rows.extend(crate::turn_usage::render_turn_footer(
                    usage,
                    &self.theme,
                    width,
                ));
                rows
            }
        }
    }
}
