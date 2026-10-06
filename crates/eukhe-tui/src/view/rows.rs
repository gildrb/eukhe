//! The per-entry transcript row builders: the assistant message spacing
//! classification (TS `getSpacingContent`), the leading-space scan (TS
//! `shouldAddLeadingSpace`), and `render_entry` -- the one producer of a
//! chat entry's rows.

use super::AgentView;
use crate::chat::{render_assistant, render_text_rows, render_user_block, ChatEntry};
use crate::theme::ThemeColor;
use crate::Line;

/// TS `getSpacingContent`: an assistant message's conversation-spacing
/// classification at the current detail level.
enum SpacingContent {
    Visible,
    ToolOnly,
    Hidden,
}

impl AgentView {
    /// TS `createConversationSpacing.shouldAddLeadingSpace` for one
    /// spacing-driven custom row (agent message, shell completion): scan
    /// back over entries that contribute no rows at this detail level
    /// (hidden thinking-only and tool-only assistant messages), then apply
    /// the trailing-space and compact-neighbor rules. `expanded` follows
    /// the TS `shouldAddLeadingSpace(expanded)` call shape.
    pub(super) fn conversation_leading(&self, index: usize, expanded: bool) -> bool {
        let mut idx = index;
        let mut tool_separator = false;
        while idx > 0 {
            idx -= 1;
            match &self.chat[idx] {
                ChatEntry::Assistant(message) => {
                    match self.assistant_spacing_content(message) {
                        SpacingContent::Hidden => {}
                        SpacingContent::ToolOnly => {
                            tool_separator = true;
                        }
                        SpacingContent::Visible => {
                            // TS `hasTrailingSpace` on the visible body
                            // (`precededByToolActivity` is the full compact
                            // set: a tool call, agent message, bash
                            // execution, or shell completion).
                            let preceded_by_tool =
                                idx > 0 && Self::is_compact_neighbor(&self.chat[idx - 1]);
                            if tool_separator
                                || message.has_trailing_space(self.detail, preceded_by_tool)
                            {
                                return false;
                            }
                            // An assistant message is never a compact
                            // neighbor; the collapsed and expanded rules
                            // both add the leading blank here.
                            return true;
                        }
                    }
                }
                preceding => {
                    if tool_separator && !Self::is_compact_neighbor(preceding) {
                        return false;
                    }
                    if expanded {
                        return true;
                    }
                    return !Self::is_compact_neighbor(preceding);
                }
            }
        }
        // The scan exhausted the transcript (only hidden or tool-only
        // assistant rows): TS keeps the tool separator with a trailing
        // space (no leading blank); with nothing preceding at all, the
        // expanded form sits flush against the top of the chat while the
        // collapsed form still leads with a blank
        // (`!isCompactAgentMessageNeighbor(undefined)`).
        if tool_separator {
            return false;
        }
        !expanded
    }

    /// TS `getSpacingContent`: an assistant message's contribution to
    /// conversation spacing at the current detail level.
    fn assistant_spacing_content(&self, message: &crate::chat::AssistantMessage) -> SpacingContent {
        let visible_body = message.blocks.iter().any(|block| match block {
            crate::chat::MessageBlock::Thinking(text) => {
                self.detail.show_thinking() && !text.trim().is_empty()
            }
            crate::chat::MessageBlock::Text(text) => !text.trim().is_empty(),
        });
        if visible_body || message.aborted || (message.error.is_some() && !message.has_tool_calls) {
            return SpacingContent::Visible;
        }
        if message.has_tool_calls {
            SpacingContent::ToolOnly
        } else {
            SpacingContent::Hidden
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
        preceded_by_tool_activity: bool,
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
                rows.extend(render_text_rows(text, style, width));
                rows
            }
            ChatEntry::StatusLinks(links) => {
                let style = self.theme.fg_style(ThemeColor::Dim);
                let link = if crate::hyperlinks::hyperlinks_enabled() {
                    crate::soft_wrap::Link::Hyperlink
                } else {
                    crate::soft_wrap::Link::Plain
                };
                let mut rows = vec![Vec::new()];
                for entry in links {
                    // The label is the block's indent, so the link stays one
                    // logical line the terminal selects and copies whole;
                    // process-supplied text never carries controls.
                    let indent = format!(" {} ", entry.label);
                    let url = crate::menu_panel::scrub_controls(&entry.url).replace('\n', "");
                    let mut block = crate::soft_wrap::rows(&indent, &url, style, width, link);
                    // The label reads in the note's tone, like the link.
                    if let Some(span) = block
                        .first_mut()
                        .and_then(|row| row.iter_mut().find(|span| span.content == indent))
                    {
                        span.style = style;
                    }
                    rows.extend(block);
                }
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
                // The per-entry block cache (TS's per-component
                // `blockCache`): settled blocks of the streaming message
                // replay instead of re-rendering on every frame -- the
                // cache exists for the streaming case. A settled
                // message's blocks are final, so its rendered rows live
                // once in the entry layout and the block-cache copy is
                // dropped (a resumed large session's duplicate copy was
                // the TUI's biggest single retained allocation in the
                // tui-memory census); any later re-render rebuilds the
                // same rows from the message's own text.
                if message.streaming {
                    let mut caches = self.md_caches.borrow_mut();
                    let cache = caches.entry(index).or_default();
                    render_assistant(
                        message,
                        detail,
                        &self.theme,
                        &self.code_block_indent,
                        width,
                        preceded_by_tool_activity,
                        cache,
                    )
                } else {
                    self.md_caches.borrow_mut().remove(&index);
                    let mut settled = crate::markdown::MarkdownBlockCache::default();
                    render_assistant(
                        message,
                        detail,
                        &self.theme,
                        &self.code_block_indent,
                        width,
                        preceded_by_tool_activity,
                        &mut settled,
                    )
                }
            }
            ChatEntry::Tool(card) => {
                // TS `ToolExecutionComponent`: the leading spacer rides on
                // `createConversationSpacing(...).shouldAddLeadingSpace`
                // (the same spacing the assistant and agent-message rows
                // use; consecutive tool cards stay flush).
                let mut rows: Vec<Line> = Vec::new();
                if self.conversation_leading(index, detail.tool_output_expanded()) {
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
                self.conversation_leading(index, detail.tool_output_expanded()),
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
            ChatEntry::InjectedPrompt(row) => {
                crate::custom_message::injected_prompt::render_injected_prompt(
                    row,
                    detail,
                    &self.theme,
                    width,
                )
            }
            ChatEntry::ShellCompletion(row) => {
                crate::custom_message::render::render_shell_completion(
                    row,
                    detail,
                    &self.theme,
                    width,
                    self.conversation_leading(index, detail.tool_output_expanded()),
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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chat::StatusLink;
    use crate::theme::{ColorMode, Theme};

    const PREVIEW: &str = "https://pi.dev/session/#0123456789abcdef0123456789abcdef";
    const GIST: &str = "https://gist.github.com/testuser/0123456789abcdef0123456789abcdef";
    const WIDTH: usize = 24;

    fn share_view() -> AgentView {
        let mut view = AgentView::new(Theme::builtin("eukhe", ColorMode::TrueColor));
        view.push_entry(ChatEntry::User {
            text: "/share".to_string(),
        });
        view.push_entry(ChatEntry::StatusLinks(vec![
            StatusLink {
                label: "Share URL:".to_string(),
                url: PREVIEW.to_string(),
            },
            StatusLink {
                label: "Gist:".to_string(),
                url: GIST.to_string(),
            },
        ]));
        view
    }

    /// The `/share` links narrower than the terminal stay one logical
    /// line each: in the rows, in the painted bytes (history and live go
    /// through the inline writer), and in a fullscreen window.
    #[test]
    fn share_links_never_break_at_a_narrow_width() {
        let _global = crate::inline_term::live_area_lock();
        for hyperlinks in [false, true] {
            crate::hyperlinks::set_hyperlinks_override(Some(hyperlinks));
            let mut view = share_view();
            let frame = view.compose(WIDTH, 40);
            let rows: Vec<Line> = frame.history.iter().chain(&frame.live).cloned().collect();
            let logical = crate::soft_wrap::logical_lines(&rows);
            assert!(
                logical.contains(&format!(" Share URL: {PREVIEW}")),
                "{logical:?}"
            );
            assert!(logical.contains(&format!(" Gist: {GIST}")), "{logical:?}");

            let mut out = Vec::new();
            crate::inline_term::InlineTerminal::new(40)
                .paint(
                    &mut out,
                    crate::inline_term::InlineFrame {
                        history: &frame.history,
                        live: &frame.live,
                        cursor: None,
                    },
                )
                .unwrap();
            let painted = crate::ansi::strip_ansi(&String::from_utf8(out).unwrap());
            assert!(!painted.contains('\x1b'), "{painted:?}");
            assert!(
                painted.contains(&format!(" Share URL: {PREVIEW}")),
                "{painted:?}"
            );
            assert!(painted.contains(&format!(" Gist: {GIST}")), "{painted:?}");

            let mut view = share_view();
            view.screen_mode = crate::screen_mode::ScreenMode::Fullscreen;
            let window = crate::soft_wrap::logical_lines(&view.compose_fullscreen(WIDTH, 40).live);
            assert!(window.contains(&format!(" Gist: {GIST}")), "{window:?}");
        }
        crate::hyperlinks::set_hyperlinks_override(None);
    }
}
