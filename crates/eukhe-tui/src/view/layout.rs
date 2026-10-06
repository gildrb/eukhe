//! The transcript rows: the settled predicate that decides when an entry
//! moves into scrollback, one entry's rows at its position, and the
//! transcript tail (pending bash cards, loaders, side pane).

use super::AgentView;
use crate::chat::{render_loader, ChatEntry};
use crate::chrome::render_splash;
use crate::Line;

impl AgentView {
    /// Whether the entry at `index` can no longer change, so its rows can
    /// move into scrollback. Never true for content still streaming or
    /// running. Two tail rows stay live while they are the last entry,
    /// because they change in place then: a status row (TS `showStatus`
    /// rewrites it when nothing followed it) and a failed attempt's
    /// error row (a retry pops it).
    pub(super) fn entry_settled(&self, index: usize) -> bool {
        let last = index + 1 == self.chat.len();
        match &self.chat[index] {
            ChatEntry::Status { .. } => !last,
            ChatEntry::User { .. }
            | ChatEntry::SlashCommand { .. }
            | ChatEntry::CompactionSummary { .. }
            | ChatEntry::SkillInvocation(_)
            | ChatEntry::AgentMessage(_)
            | ChatEntry::ShellCompletion(_)
            | ChatEntry::InjectedPrompt(_)
            | ChatEntry::RefinementOutcome(_)
            | ChatEntry::CustomPanel(_)
            | ChatEntry::ChatView(_) => true,
            ChatEntry::Assistant(message) => {
                !message.streaming
                    && (!last || !crate::snapshot::is_superseded_attempt_row(&self.chat[index]))
            }
            // A cell whose final result carries a still-running background
            // shell is settled: its result never changes again.
            ChatEntry::Tool(card) => !matches!(
                crate::tool_card::panel_status(card),
                crate::tool_card::PanelStatus::Queued | crate::tool_card::PanelStatus::Running
            ),
            ChatEntry::BashExecution(card) => !card.running,
        }
    }

    /// One entry's rows at its transcript position (the spacing rules
    /// read the entries before it).
    pub(super) fn render_entry_at(&self, index: usize, width: usize) -> Vec<Line> {
        // TS `precededByToolActivity` = `isCompactAgentMessageNeighbor` of
        // the previous row: a tool call, agent message, bash execution, or
        // shell completion all count.
        let preceded_by_tool_activity =
            index > 0 && Self::is_compact_neighbor(&self.chat[index - 1]);
        self.render_entry(
            index,
            &self.chat[index],
            width,
            index == 0,
            preceded_by_tool_activity,
        )
    }

    /// The whole transcript as rows: splash, every entry, the tail (the
    /// test and replay-dump form; the surface composes through
    /// `compose`).
    pub fn render_transcript(&mut self, width: usize) -> Vec<Line> {
        if let (Some(working), Some(since)) = (&mut self.working, self.working_since) {
            working.elapsed_secs = since.elapsed().as_secs();
        }
        let mut rows = self.render_history(width);
        rows.extend(self.render_transcript_tail(width));
        rows
    }

    /// The splash and every entry: the rows inline mode leaves in
    /// scrollback, which a fullscreen exit prints to the normal screen.
    pub(crate) fn render_history(&self, width: usize) -> Vec<Line> {
        let mut rows = if self.splash_suppressed {
            Vec::new()
        } else {
            render_splash(&self.chrome, &self.theme, width)
        };
        for index in 0..self.chat.len() {
            rows.extend(self.render_entry_at(index, width));
        }
        rows
    }

    pub(super) fn render_transcript_tail(&self, width: usize) -> Vec<Line> {
        let mut tail: Vec<Line> = Vec::new();
        // In-flight bash output for the current turn renders ABOVE the
        // execution indicator (TS `pendingMessagesContainer` sits between
        // the chat rows and the status area) and flushes into the
        // transcript when the turn settles.
        if !self.pending_bash.is_empty() {
            // TS `keyText("tui.select.cancel")`: every key of the
            // binding joins the hint ("Esc/Ctrl+C").
            let cancel_hint = self.editor.keybindings().key_text("tui.select.cancel");
            for card in &self.pending_bash {
                tail.push(Vec::new());
                tail.extend(crate::bash_card::render_bash_execution(
                    card,
                    self.pulse_frame,
                    self.detail.tool_output_expanded(),
                    &cancel_hint,
                    &self.theme,
                    width,
                ));
            }
        }
        // While the provider retry loop waits, its countdown loader owns
        // the status area (TS `stopWorkingLoader` + `retryLoader`); a
        // compaction run owns it next (TS `startCompactionLoader`); the
        // working loader renders only when neither is active.
        if let Some(retry) = &self.retry {
            tail.extend(crate::chat::render_retry(
                retry,
                self.pulse_frame,
                &self.theme,
                width,
            ));
        } else if let Some(compaction) = &self.compaction {
            let cancel_hint = self
                .editor
                .keybindings()
                .first_key("app.clear")
                .map_or_else(
                    || "Ctrl+C".to_string(),
                    |key| crate::keybindings::format_key_text(&key),
                );
            tail.extend(crate::compaction_row::render_compaction_loader(
                compaction,
                self.pulse_frame,
                &cancel_hint,
                &self.theme,
                width,
            ));
            // The live streamed-summary block (the operator's "stream
            // the compacted summary" feature): under the loader row, the
            // expanded view renders the summary as the compaction model
            // generates it -- one delta at a time -- nested on the branch
            // grammar like the expanded summary row that settles it.
            tail.extend(crate::compaction_row::render_compaction_stream(
                compaction,
                self.detail.tool_output_expanded(),
                &self.theme,
                width,
            ));
        } else if let Some(working) = &self.working {
            tail.extend(render_loader(working, self.pulse_frame, &self.theme, width));
        }
        // The side-question pane (TS `sideQuestionContainer`): a scroll-area
        // component under the status area, not a dock row -- it hugs the
        // transcript tail, so the frame's slack (a short transcript against
        // a bottom-pinned dock) lands between the pane and the editor like
        // TS, never inside the pane. TS mounts the pane behind a `Spacer(1)`
        // (`sideQuestionContainer.addChild(new Spacer(1))`), so one blank
        // row precedes the component's own leading blank.
        if let Some(pane) = &self.side_pane {
            tail.push(Vec::new());
            tail.extend(pane.render(
                &self.theme,
                self.pulse_frame,
                self.detail.tool_output_expanded(),
                &self.editor.keybindings().key_text("tui.select.cancel"),
                width,
            ));
        }
        tail
    }
}
