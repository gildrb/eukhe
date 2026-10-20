//! Interactive agent view: the chat surface composed for the inline
//! terminal. Settled chat entries move into scrollback (history) once;
//! the live area below holds the unsettled entries, the transcript tail
//! (pending bash cards, loaders), toasts, and the dock (the borderless
//! composer and the status line, or the open panel). The session loop
//! folds events into the view; this module owns the composition.

use crate::chat::{ChatEntry, CompactionState, Detail, WorkingState};
use crate::chrome::ChromeState;
use crate::editor::Editor;
use crate::session::TranscriptItem;
use crate::theme::Theme;

#[cfg(test)]
mod bridge;
pub(crate) mod editor_surface;
mod frame;
mod layout;
pub(crate) mod ledger;
mod panels;
mod rows;
pub(crate) mod stack;
mod streaming;
mod viewport;

pub use frame::{ChatFrame, FrameStart, TranscriptBreak};
pub use viewport::{ScrollAmount, ScrollRequest};

pub struct AgentView {
    pub theme: Theme,
    /// The chat markdown fenced-code indent (`markdown.codeBlockIndent`,
    /// TS `getMarkdownThemeWithSettings`; default two spaces).
    pub code_block_indent: String,
    pub editor: Editor,
    pub chrome: ChromeState,
    /// Queued input parked behind the running turn (steering/follow-up
    /// lanes); renders as the dim strip above the prompt dock.
    pub queued: crate::queued::QueuedMessages,
    /// The queue item selected for browsing/edit (TS `QueueSelection`):
    /// while set, the dim browse header renders above the editor.
    pub queue_selected: Option<crate::queued::QueueSelectionItem>,
    pub chat: Vec<ChatEntry>,
    /// In-flight bash cards held ABOVE the execution indicator while the
    /// agent streams (TS `pendingMessagesContainer` +
    /// `pendingBashComponents`): a `bash_start` during an active turn
    /// mounts here and flushes into the transcript when the turn ends.
    pub pending_bash: Vec<crate::bash_card::BashExecutionCard>,
    pub detail: Detail,
    pub working: Option<WorkingState>,
    /// A compaction run in flight (TS `autoCompactionLoader`): replaces the
    /// working loader from `compaction_start` to `compaction_end`.
    pub compaction: Option<CompactionState>,
    /// The compaction loader's generation: bumped on every
    /// `compaction_start`, so a backgrounded abort outcome addresses the
    /// exact loader it was sent for -- a late failure for a settled run
    /// never clears a newer run's loader.
    pub compaction_generation: u64,
    /// Animation frame for spinners and the working icon.
    pub pulse_frame: usize,
    /// When the current working loader started (elapsed label).
    pub working_since: Option<std::time::Instant>,
    /// An active provider auto-retry (replaces the working loader while
    /// the retry loop waits, TS `retryLoader`).
    pub retry: Option<crate::chat::RetryState>,
    /// The first-run onboarding pane (TS `runStartupOnboarding`): while
    /// set, it owns the whole frame.
    pub onboarding: Option<crate::onboarding::OnboardingScreen>,
    /// The `/model` inline picker (TS `ModelSelectorComponent` seam):
    /// while set, it owns the whole frame like the onboarding pane.
    pub model_picker: Option<crate::model_picker::ModelPicker>,
    /// The `/tree` selector (owns the frame while open).
    pub tree_selector: Option<crate::tree_selector::TreeSelector>,
    /// A pending confirm: the Yes/No selector over the editor dock.
    pub confirm: Option<crate::confirm::ConfirmPanel>,
    /// The `/login` / `/logout` provider selector (TS
    /// `OAuthSelectorComponent` inline): owns the frame while open.
    pub provider_auth: Option<crate::provider_auth::ProviderAuthSelector>,
    /// The inline auth panel (TS `LoginDialogComponent` +
    /// `PrimeTeamSelectorComponent`): owns the frame while a login flow
    /// drives it through the panel channel.
    pub auth_panel: Option<crate::auth_panel::AuthPanel>,
    /// The `/fork` user-message selector.
    pub fork_selector: Option<crate::user_message_selector::UserMessageSelector>,
    /// The `/effort` inline picker (TS `ThinkingSelectorComponent` seam):
    /// while set, it owns the whole frame like the model picker.
    pub effort_picker: Option<crate::effort_picker::EffortPicker>,
    /// The `/workflow-size` picker, while open.
    pub workflow_size_picker: Option<crate::workflow_size_picker::WorkflowSizePicker>,
    /// The `/mcp` inline connections view (the MCP surface's own
    /// picker): while set, it owns the editor dock like the model
    /// picker.
    pub mcp_view: Option<crate::mcp_view::McpView>,
    /// The factory page: while set, it owns the editor dock like the
    /// inline pickers (one panel per live factory run) -- the activity
    /// dock's factory group's destination.
    pub factory_view: Option<crate::factory_view::FactoryView>,
    /// The `/workflows` page, while open.
    pub workflow_view: Option<crate::workflow_view::WorkflowView>,
    /// The `/heartbeats` inline management view (TS
    /// `HeartbeatManagerComponent`, inline-picker style): while set, it
    /// owns the editor dock like the `/model` and `/effort` pickers.
    pub heartbeats_picker: Option<crate::heartbeats_picker::HeartbeatsPicker>,
    /// The read-only goal panel (the dock's `Pursuing goal` row): while
    /// `Some`, the panel owns the frame exactly like the docked pickers.
    pub goal_panel: Option<crate::goal_surface::GoalPanel>,
    /// The dedicated bash view (the dock's Bash group's destination):
    /// while set, it owns the editor dock like the inline pickers.
    pub bash_view: Option<crate::bash_view::BashView>,
    /// The `/reload` box (TS `handleReloadCommand`'s `reloadBox`): a
    /// bordered note that replaces the editor while the reload travels.
    pub reload_box: Option<String>,
    /// The side-question pane (TS `sideQuestionContainer`): mounted above
    /// the prompt dock (below the queue strip) while a side conversation
    /// is open; `None` is the main-thread state.
    pub side_pane: Option<crate::side_question::SideQuestionPane>,
    /// The `/settings` inline menu (TS `SettingsSelectorComponent`):
    /// mounted in the editor dock like the tree and fork selectors.
    pub settings_menu: Option<crate::settings_menu::SettingsMenu>,
    /// The read-only info panel (the operator's 2026-09-26 directive:
    /// the `/context`-family client info displays render as the docked
    /// popup panel instead of flooding the transcript): while set, it
    /// owns the editor dock like the `/model` and `/effort` pickers.
    pub info_panel: Option<crate::info_panel::InfoPanel>,
    /// The `/memory` tree (the chat memory's dated, expandable lines):
    /// while set, it owns the editor dock like the info panel.
    pub memory_tree: Option<crate::memory_tree::MemoryTreeView>,
    /// The `terminal.showImages` setting (TS `getShowImages`, default
    /// true): image blocks render their metadata rows when set, their
    /// `[Image: ...]` text placeholders otherwise.
    pub show_images: bool,
    /// The `showHardwareCursor` setting (TS default false): the hardware
    /// cursor is positioned at the focused caret for IME on every frame
    /// either way, but only shown when this is set -- TS keeps the
    /// terminal's own cursor hidden by default so frame paints never drag
    /// a visible cursor across the pane (`positionHardwareCursor` and the
    /// paint tail move it while hidden).
    pub show_hardware_cursor: bool,
    /// `terminal.showSpeed` (default true): the status line shows the
    /// generation speed.
    pub show_speed: bool,
    /// The brand splash never renders while set: a chat that opens or
    /// rebinds directly into a non-empty transcript suppresses it (TS
    /// mounts the chat over an already-attached connection, so its first
    /// visible frame is the content). Every empty chat keeps it (TS
    /// `BrandSplashHeader` is the new chat's header, `quietStartup` and
    /// the onboarding `getHidden` are TS's own suppression gates).
    pub splash_suppressed: bool,
    /// The `quietStartup` setting: the brand splash never renders.
    pub quiet_startup: bool,
    /// Rows of the terminal the editor and the live area lay out against.
    terminal_rows: u16,
    /// Cursor cell within the last dock render: (dock row, column).
    dock_cursor: Option<(usize, usize)>,
    /// Each chat entry's state on the inline terminal: active, final, or
    /// committed (in scrollback). Committed rows are never written again.
    ledger: ledger::Ledger,
    /// What the inline terminal holds of this transcript: nothing yet,
    /// a replaced transcript's rows, or this one's.
    scrollback: frame::Scrollback,
    /// The shape the fullscreen window's cached rows were rendered at;
    /// `None` before the first fullscreen frame.
    fullscreen_shape: Option<frame::RenderShape>,
    /// The pace of each assistant entry seen streaming and not yet in
    /// scrollback: the characters of its text that arrived and that
    /// show (`crate::pace`).
    paces: std::collections::HashMap<usize, crate::pace::Pace>,
    /// The detail level the paces last counted at: a change shows or
    /// hides thinking, and the paces recount (`advance_paces`).
    pace_detail: Detail,
    /// How fast a frame reveals streamed text (`terminal.streamPace`).
    pub pace_rate: crate::pace::PaceRate,
    /// Per-streaming-assistant-entry render state (`streaming`): the
    /// markdown block cache (TS `Markdown.blockCache`, one per component
    /// instance) replays settled blocks while the final one grows, and
    /// the last render replays whole while the message is unchanged.
    /// `RefCell` because rendering borrows the chat immutably. Dropped
    /// when the message settles.
    md_caches: std::cell::RefCell<std::collections::HashMap<usize, streaming::StreamingRender>>,
    /// The ephemeral action toasts (auto-dismiss rows in the live area;
    /// a sanctioned divergence from TS -- see `toast`).
    pub toasts: crate::toast::Toasts,
    /// Inline or fullscreen: the surface paints [`AgentView::compose`] or
    /// [`AgentView::compose_fullscreen`] frames.
    pub screen_mode: crate::screen_mode::ScreenMode,
    /// The fullscreen transcript window.
    viewport: viewport::Viewport,
}

/// Clip the editor selection to one rendered chunk (view.rs): the
/// selection's (line, col) bounds become a char range within `text` -- the
/// chunk of `source_line` starting at `source_start`. `None` when the
/// selection does not touch this chunk. Lines fully inside the selection
/// highlight whole; the boundary lines clip at the selection's columns.
fn chunk_selection(
    selection: Option<((usize, usize), (usize, usize))>,
    source_line: usize,
    source_start: usize,
    text: &str,
) -> Option<(usize, usize)> {
    let ((start_line, start_col), (end_line, end_col)) = selection?;
    if source_line < start_line || source_line > end_line {
        return None;
    }
    let chunk_chars = text.chars().count();
    // The start column is a source-line column (it converts to the
    // chunk's coordinates); a fully-covered line selects to the chunk's
    // end directly, and the END line's column converts like the start.
    let lo = if source_line == start_line {
        start_col.saturating_sub(source_start)
    } else {
        0
    };
    let hi = if source_line == end_line {
        end_col.saturating_sub(source_start)
    } else {
        chunk_chars
    };
    let hi = hi.min(chunk_chars);
    let lo = lo.min(chunk_chars);
    (lo < hi).then_some((lo, hi))
}

impl AgentView {
    /// TS `isCompactAgentMessageNeighbor`: agent messages, tool calls (the
    /// ipython cells included), bash executions, and shell completions
    /// render flush against each other -- the set both the leading-space
    /// scan and `precededByToolActivity` compact decisions use.
    pub(super) fn is_compact_neighbor(entry: &ChatEntry) -> bool {
        matches!(
            entry,
            ChatEntry::Tool(_)
                | ChatEntry::AgentMessage(_)
                | ChatEntry::ShellCompletion(_)
                | ChatEntry::BashExecution(_)
        )
    }

    /// One paste routed by the open overlay, the key dispatch's order:
    /// the overlay's own input takes it, the input-less overlays consume
    /// it, and the bare dock's editor takes it when nothing is open.
    /// Returns whether an overlay took or consumed the paste.
    pub fn route_paste(&mut self, text: &str) -> bool {
        if let Some(picker) = self.model_picker.as_mut() {
            picker.paste(text);
            return true;
        }
        if let Some(picker) = self.effort_picker.as_mut() {
            picker.paste(text);
            return true;
        }
        if let Some(picker) = self.workflow_size_picker.as_mut() {
            picker.paste(text);
            return true;
        }
        if let Some(mcp) = self.mcp_view.as_mut() {
            mcp.paste(text);
            return true;
        }
        if let Some(selector) = self.tree_selector.as_mut() {
            selector.paste(text);
            return true;
        }
        if let Some(auth) = self.provider_auth.as_mut() {
            auth.paste(text);
            return true;
        }
        if let Some(menu) = self.settings_menu.as_mut() {
            menu.paste(text);
            return true;
        }
        // The input-less frame owners (the key dispatch's same set): the
        // heartbeats picker, the bash view, the read-only goal and info
        // panels, the `/memory` tree, the fork selector, the pending
        // confirm, the reload box,
        // and the auth panel (its own channel
        // drives it). None of them leaves a paste to the editor behind.
        if self.heartbeats_picker.is_some()
            || self.bash_view.is_some()
            || self.goal_panel.is_some()
            || self.info_panel.is_some()
            || self.memory_tree.is_some()
            || self.fork_selector.is_some()
            || self.confirm.is_some()
            || self.reload_box.is_some()
            || self.auth_panel.is_some()
        {
            return true;
        }
        false
    }

    #[must_use]
    pub fn new(theme: Theme) -> Self {
        Self {
            theme,
            code_block_indent: "  ".to_string(),
            editor: Editor::new(),
            chrome: ChromeState::default(),
            queued: crate::queued::QueuedMessages::default(),
            queue_selected: None,
            chat: Vec::new(),
            pending_bash: Vec::new(),
            // A chat starts at the collapsed conversation-detail level
            // (operator directive 2026-09-28): every activity item
            // renders exactly as `details` does, with only the thinking
            // blocks hidden; Ctrl+O keeps cycling overview -> details
            // -> all, so the first press reveals the thinking.
            detail: Detail::Overview,
            working: None,
            compaction: None,
            compaction_generation: 0,
            pulse_frame: 0,
            working_since: None,
            retry: None,
            onboarding: None,
            model_picker: None,
            tree_selector: None,
            confirm: None,
            provider_auth: None,
            auth_panel: None,
            fork_selector: None,
            effort_picker: None,
            workflow_size_picker: None,
            mcp_view: None,
            factory_view: None,
            workflow_view: None,
            heartbeats_picker: None,
            goal_panel: None,
            bash_view: None,
            reload_box: None,
            side_pane: None,
            settings_menu: None,
            info_panel: None,
            memory_tree: None,
            show_images: true,
            show_hardware_cursor: false,
            show_speed: true,
            splash_suppressed: false,
            quiet_startup: false,
            terminal_rows: 24,
            dock_cursor: None,
            ledger: ledger::Ledger::default(),
            scrollback: frame::Scrollback::Empty,
            fullscreen_shape: None,
            paces: std::collections::HashMap::new(),
            pace_detail: Detail::Overview,
            pace_rate: crate::pace::PaceRate::DEFAULT,
            md_caches: std::cell::RefCell::new(std::collections::HashMap::new()),
            toasts: crate::toast::Toasts::default(),
            screen_mode: crate::screen_mode::ScreenMode::Inline,
            viewport: viewport::Viewport::default(),
        }
    }

    /// The terminal height the pickers size themselves against.
    pub fn terminal_rows(&self) -> u16 {
        self.terminal_rows
    }

    pub fn set_terminal_rows(&mut self, rows: u16) {
        self.terminal_rows = rows;
    }

    /// Append one chat component.
    pub fn push_entry(&mut self, entry: ChatEntry) {
        self.chat.push(entry);
    }

    /// The number of chat entries (the status-row in-place update checks
    /// whether its own row is still the transcript's last entry).
    pub fn chat_len(&self) -> usize {
        self.chat.len()
    }

    /// Pop the LAST chat entry (the retry-episode collapse: the superseded
    /// failed attempt's error row leaves the chat when its retry replaces
    /// it -- SANCTIONED DIVERGENCE from TS, operator ruling 2026-09-23).
    /// The settled predicate keeps such a row live, so the pop never
    /// reaches scrollback in practice; if it does, the scrollback keeps
    /// the row as written.
    pub fn pop_chat_entry(&mut self) -> Option<ChatEntry> {
        let index = self.chat.len().checked_sub(1)?;
        self.ledger.truncate(index);
        self.paces.remove(&index);
        self.viewport.forget_from(index);
        self.md_caches.borrow_mut().remove(&index);
        self.chat.pop()
    }

    /// Replace the text and tone of the status entry at `index` (TS
    /// `showStatus` updates its previous status row in place when nothing
    /// followed it). Returns `false` when the entry is not a status row.
    pub fn update_status_row(
        &mut self,
        index: usize,
        text: &str,
        kind: crate::chat::StatusKind,
    ) -> bool {
        let Some(ChatEntry::Status {
            text: slot,
            kind: kind_slot,
        }) = self.chat.get_mut(index)
        else {
            return false;
        };
        *slot = text.to_string();
        *kind_slot = kind;
        self.mark_entry_stale(index);
        true
    }

    /// Show one live `memory_update`: folded into the transcript's last
    /// entry when that is a memory row of the same kind (a burst of
    /// compactor progress reads as one row that grows in place), else a
    /// new row.
    pub fn push_memory_update(&mut self, update: eukhe_types::daemon::MemoryUpdate) {
        let last = self.chat.len().checked_sub(1);
        if let Some(index) = last {
            if let Some(ChatEntry::MemoryUpdate(row)) = self.chat.get_mut(index) {
                let Some(update) = crate::memory_block::fold_memory_update(row, update) else {
                    self.mark_entry_stale(index);
                    return;
                };
                self.chat.push(ChatEntry::MemoryUpdate(Box::new(update)));
                return;
            }
        }
        self.chat.push(ChatEntry::MemoryUpdate(Box::new(update)));
    }

    /// Append a replay transcript item (mapped onto chat components).
    ///
    /// A tool result completes the pending tool card with the same id
    /// (TS `buildConversationComponents` folds results onto their call
    /// components, never a new row); a result without a pending card keeps
    /// its standalone card so the row never disappears.
    pub fn push(&mut self, item: TranscriptItem) {
        if let TranscriptItem::ToolResult {
            tool_call_id,
            tool_name,
            text,
            content,
            details,
            is_error,
        } = &item
        {
            let pending = self.chat.iter().rposition(|entry| {
                matches!(entry, ChatEntry::Tool(card) if card.id == *tool_call_id && card.result.is_none())
            });
            if let Some(index) = pending {
                // The matched card's result settles IN PLACE.
                if let Some(ChatEntry::Tool(card)) = self.chat.get_mut(index) {
                    card.started = true;
                    // Replayed cards never saw the live execution: the
                    // timing collapses to the rebuild instant, matching
                    // the snapshot path.
                    let now = std::time::Instant::now();
                    card.started_at = Some(now);
                    card.ended_at = Some(now);
                    card.result = Some(crate::chat::ToolResultView {
                        content: if content.is_empty() {
                            vec![serde_json::json!({ "type": "text", "text": text })]
                        } else {
                            content.clone()
                        },
                        details: details.clone(),
                        is_error: *is_error,
                    });
                    card.result_partial = false;
                }
                self.mark_entry_stale(index);
                return;
            }
            let view = crate::chat::ToolResultView {
                content: if content.is_empty() {
                    vec![serde_json::json!({ "type": "text", "text": text })]
                } else {
                    content.clone()
                },
                details: details.clone(),
                is_error: *is_error,
            };
            self.push_entry(ChatEntry::Tool(Box::new(crate::chat::ToolCallCard {
                id: tool_call_id.clone(),
                name: tool_name.clone(),
                args: serde_json::Value::Null,
                started: true,
                result: Some(view),
                ..Default::default()
            })));
            return;
        }
        // TS `bash_start`/`addMessageToChat` suppress the component's
        // leading spacer only against an agent-message row.
        let mut entry = item_to_entry(item);
        if let ChatEntry::BashExecution(card) = &mut entry {
            card.suppress_leading_space =
                matches!(self.chat.last(), Some(ChatEntry::AgentMessage(_)));
        }
        self.push_entry(entry);
    }

    /// Drop the whole transcript (a fresh snapshot rebuild re-renders
    /// every row). The rebuilt chat is a new transcript (`why` says
    /// which). The scrollback keeps the old one as written: when it has
    /// entries there, the next frame writes one separator row naming the
    /// break, and the new transcript commits below it. A scrollback that
    /// holds only the splash (the opening frame before the session
    /// attached) gets no separator.
    pub fn clear_chat(&mut self, why: frame::TranscriptBreak) {
        let replaced = match self.scrollback {
            frame::Scrollback::Replaced(_) => true,
            frame::Scrollback::Empty | frame::Scrollback::Written => self.ledger.committed() > 0,
        };
        if replaced {
            self.scrollback = frame::Scrollback::Replaced(why);
        }
        self.ledger = ledger::Ledger::default();
        self.paces.clear();
        self.viewport.forget_from(0);
        self.viewport.stale = true;
        self.chat.clear();
        self.md_caches.borrow_mut().clear();
        // A rebuilt transcript has no pending hold (TS
        // `resetCurrentSessionRenderState` clears `pendingBashComponents`).
        self.pending_bash.clear();
    }

    /// Note that one chat entry's content changed (streamed blocks,
    /// tool-card state, an attached error row). An active entry takes the
    /// change with the next frame. A committed entry keeps the rows it
    /// has in scrollback: the inline terminal does not show the change
    /// (the fullscreen window renders the entry again).
    pub fn mark_entry_stale(&mut self, index: usize) {
        self.ledger.grow(index, 1);
        self.viewport.forget(index);
    }

    /// The terminal changed size. The inline scrollback stays as it is
    /// (the inline terminal redraws only its live area); the fullscreen
    /// window paints again in full with the next frame.
    pub fn note_resize(&mut self) {
        self.viewport.stale = true;
    }

    /// Whether streamed text still waits to show: the frame loop keeps
    /// drawing frames until it is all on screen.
    #[must_use]
    pub fn is_pacing(&self) -> bool {
        self.paces.values().any(|pace| !pace.drained())
    }

    /// The Ctrl+O cycle (`app.tools.expand`, TS
    /// `toggleToolOutputExpansion` + `applyChatExpansion`): step the
    /// conversation level. The live area and the rows committed from now
    /// on use it; the scrollback keeps its rows.
    pub(crate) fn cycle_detail(&mut self) {
        self.detail = self.detail.next();
    }
}

/// Map a replay transcript item onto a chat component.
fn item_to_entry(item: TranscriptItem) -> ChatEntry {
    match item {
        TranscriptItem::UserMessage { text } => ChatEntry::User { text },
        TranscriptItem::SystemNote { text } => ChatEntry::Status {
            text,
            kind: crate::chat::StatusKind::Info,
        },
        TranscriptItem::Assistant {
            blocks,
            has_tool_calls,
        } => ChatEntry::Assistant(Box::new(crate::chat::AssistantMessage {
            blocks,
            has_tool_calls,
            streaming: false,
            error: None,
            aborted: false,
        })),
        TranscriptItem::ToolCall {
            id,
            name,
            arguments,
        } => ChatEntry::Tool(Box::new(crate::chat::ToolCallCard {
            id,
            name,
            args: serde_json::from_str(&arguments).unwrap_or(serde_json::Value::Null),
            started: false,
            ..Default::default()
        })),
        // A replayed tool result reaches the view through
        // [`AgentView::push`], which folds it onto its pending tool card;
        // this arm keeps a standalone card for any unmatched result.
        TranscriptItem::ToolResult {
            tool_call_id,
            tool_name,
            text,
            content,
            details,
            is_error,
        } => ChatEntry::Tool(Box::new(crate::chat::ToolCallCard {
            id: tool_call_id,
            name: tool_name,
            args: serde_json::Value::Null,
            started: true,
            result: Some(crate::chat::ToolResultView {
                content: if content.is_empty() {
                    vec![serde_json::json!({ "type": "text", "text": text })]
                } else {
                    content
                },
                details,
                is_error,
            }),
            ..Default::default()
        })),
        TranscriptItem::BashExecution {
            command,
            output,
            exit_code,
            cancelled,
            omitted,
            artifact,
            excluded,
        } => {
            // TS `addMessageToChat`'s `bashExecution` case: the same
            // component the live events render, completed over the
            // recorded output.
            let mut card = crate::bash_card::BashExecutionCard::settled(&command, excluded);
            card.append_output(&output);
            card.set_complete(exit_code, cancelled, omitted, artifact);
            ChatEntry::BashExecution(Box::new(card))
        }
        TranscriptItem::ModelChange { model_id, .. } => ChatEntry::Status {
            text: format!("Model: {model_id}"),
            kind: crate::chat::StatusKind::Info,
        },
        TranscriptItem::CustomRow { entry } => entry,
    }
}

#[cfg(test)]
mod screen_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod chunk_selection_tests {
    use super::chunk_selection;

    /// A fully-covered line highlights to the chunk's own end (the
    /// chunk-local length), not `chunk length - source start` -- wrapped
    /// continuations keep their highlight (Bugbot round-1 fix).
    #[test]
    fn wrapped_chunks_on_fully_covered_lines_highlight_to_their_end() {
        let sel = Some(((0, 10), (2, 5)));
        // A wrapped continuation chunk of line 1 (source cols 20..30).
        let range = chunk_selection(sel, 1, 20, "wrapped text");
        assert_eq!(range, Some((0, 12)), "the whole chunk highlights");
        // The selection's ending line converts its source column.
        let range = chunk_selection(sel, 2, 0, "abcde");
        assert_eq!(range, Some((0, 5)));
        // A chunk the selection ends before does not highlight.
        let range = chunk_selection(sel, 2, 6, "fgh");
        assert_eq!(range, None);
        // The starting line clips at its start column: a chunk that
        // begins exactly where the selection does is fully covered, and a
        // chunk the selection starts AFTER stays clear.
        let range = chunk_selection(sel, 0, 0, "01234567890123456789");
        assert_eq!(range, Some((10, 20)));
        let range = chunk_selection(sel, 0, 10, "0123456789");
        assert_eq!(
            range,
            Some((0, 10)),
            "the selection starts at this chunk's start"
        );
        let range = chunk_selection(sel, 0, 5, "01234");
        assert_eq!(range, None, "the selection starts after this chunk ends");
    }
}
