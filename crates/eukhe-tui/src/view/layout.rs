//! The transcript rows: the settled predicate that decides when an entry
//! moves into scrollback, one entry's rows at its position, and the
//! transcript tail (pending bash cards, loaders, side pane).

use super::AgentView;
use crate::activity::{AgentActivity, TurnPhase};
use crate::chat::{render_loader, ChatEntry};
use crate::chrome::render_splash;
use crate::Line;

impl AgentView {
    /// Whether the entry at `index` can no longer change, so its rows can
    /// move into scrollback. Never true for content still streaming or
    /// running. Two tail rows stay live while they are the last entry,
    /// because they change in place then: a status row (TS `showStatus`
    /// rewrites it when nothing followed it) and a failed reply's error
    /// row -- a retry pops an error-only attempt, and a retry episode's
    /// outcome row retires the error of a reply that streamed text before
    /// it failed (`apply.rs` `RetryOutcomeRow`). A frame between the
    /// failure and that row must not commit the error row the row then
    /// replaces: committed rows are never written again.
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
            | ChatEntry::ChatView(_)
            | ChatEntry::Swarm(_) => true,
            // A message settles once it stopped streaming and its pace
            // shows all its text; a failed one only once an entry
            // follows it.
            ChatEntry::Assistant(message) => {
                !message.streaming
                    && self.pace_drained(index)
                    && (!last || message.error.is_none() || message.aborted)
            }
            // A cell whose final result carries a still-running background
            // shell is settled: its result never changes again.
            ChatEntry::Tool(card) => !matches!(
                crate::tool_card::panel_status(card),
                crate::element::Status::Queued | crate::element::Status::Running
            ),
            ChatEntry::BashExecution(card) => !card.running,
        }
    }

    /// One entry's rows at its transcript position (the spacing rules
    /// read the entries before it).
    pub(super) fn render_entry_at(&self, index: usize, width: usize) -> Vec<Line> {
        self.render_entry(index, &self.chat[index], width, index == 0)
    }

    /// The last `rows` rows of the entry at `index` (the live area's
    /// clip): a streaming or paced message copies only those from its
    /// last render, any other entry renders whole and drops the rows
    /// above.
    pub(super) fn render_entry_tail(&self, index: usize, width: usize, rows: usize) -> Vec<Line> {
        if let ChatEntry::Assistant(message) = &self.chat[index] {
            let tail = |all: &[Line]| all[all.len().saturating_sub(rows)..].to_vec();
            match (self.paced_message(index, message), message.streaming) {
                (Some(shown), true | false) => {
                    return self.with_streaming_rows(index, &shown, width, tail);
                }
                (None, true) => return self.with_streaming_rows(index, message, width, tail),
                (None, false) => {}
            }
        }
        let mut all = self.render_entry_at(index, width);
        all.drain(..all.len().saturating_sub(rows));
        all
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

    /// The newest `rows` rows of the transcript (the entries, then the
    /// tail), rendering only the entries those rows reach: the worker
    /// pane shows another session's tail this way (`crate::worker_pane`).
    pub(crate) fn render_last_rows(&mut self, width: usize, rows: usize) -> Vec<Line> {
        if let (Some(working), Some(since)) = (&mut self.working, self.working_since) {
            working.elapsed_secs = since.elapsed().as_secs();
        }
        let tail = self.render_transcript_tail(width);
        let mut count = tail.len();
        let mut blocks = vec![tail];
        for index in (0..self.chat.len()).rev() {
            if count >= rows {
                break;
            }
            let entry = self.render_entry_tail(index, width, rows - count);
            count += entry.len();
            blocks.push(entry);
        }
        let mut out: Vec<Line> = blocks.into_iter().rev().flatten().collect();
        out.drain(..out.len().saturating_sub(rows));
        out
    }

    /// The brand splash rows: none under `quietStartup` or while the chat
    /// opened straight into content.
    pub(super) fn splash_rows(&self, width: usize) -> Vec<Line> {
        if self.splash_suppressed || self.quiet_startup {
            return Vec::new();
        }
        render_splash(&self.chrome, &self.theme, width)
    }

    /// The splash and every entry: the rows inline mode leaves in
    /// scrollback, which a fullscreen exit prints to the normal screen.
    pub(crate) fn render_history(&self, width: usize) -> Vec<Line> {
        let mut rows = self.splash_rows(width);
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
        // The indicator row above the composer follows the session's
        // activity (`crate::activity`): a running turn always shows one
        // loader row with its elapsed time -- the retry countdown while
        // the provider retry loop waits (TS `stopWorkingLoader` +
        // `retryLoader`), the compaction loader while a compaction runs
        // (TS `startCompactionLoader`), the working loader otherwise
        // (held up past the turn's end while its answer's text still
        // shows at its pace) -- and a quota-parked session names its
        // wake time instead of reading as idle. Background work rides
        // the dock's counts.
        match self.activity() {
            AgentActivity::Working { .. } => {
                let elapsed = self.loader_row().map_or(0, |working| working.elapsed_secs);
                if let Some(retry) = &self.retry {
                    tail.extend(crate::chat::render_retry(
                        retry,
                        elapsed,
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
                        elapsed,
                        self.pulse_frame,
                        &cancel_hint,
                        &self.theme,
                        width,
                    ));
                    // The live streamed-summary block (the operator's
                    // "stream the compacted summary" feature): under the
                    // loader row, the expanded view renders the summary as
                    // the compaction model generates it -- one delta at a
                    // time -- nested on the branch grammar like the
                    // expanded summary row that settles it.
                    tail.extend(crate::compaction_row::render_compaction_stream(
                        compaction,
                        self.detail.tool_output_expanded(),
                        &self.theme,
                        width,
                    ));
                } else if let Some(working) = self.loader_row() {
                    tail.extend(render_loader(working, self.pulse_frame, &self.theme, width));
                }
            }
            AgentActivity::Parked(park) => {
                tail.push(Vec::new());
                tail.extend(crate::chat::render_text_rows(
                    &format!(
                        "{} {}",
                        crate::glyphs::WARN,
                        crate::activity::park_label(&park, crate::agents_view_state::now_ms())
                    ),
                    self.theme.fg_style(crate::theme::ThemeColor::Warning),
                    width,
                ));
            }
            AgentActivity::Background { .. } | AgentActivity::Idle => {}
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

    /// This session at a glance, the input of the [`crate::activity`]
    /// mapping: a turn runs while its loader, a retry, or a compaction is
    /// up (a retry or a compaction overlays the loader's phase; the loader
    /// stays up while its answer's text still shows at its pace); between
    /// turns a quota park, then the dock's running background work, else
    /// idle.
    #[must_use]
    pub fn activity(&self) -> AgentActivity {
        let phase = match (&self.retry, &self.compaction, self.loader_row()) {
            (Some(_), _, _) => Some(TurnPhase::Retrying),
            (None, Some(_), _) => Some(TurnPhase::Compacting),
            (None, None, Some(working)) => Some(working.phase),
            (None, None, None) => None,
        };
        if let Some(phase) = phase {
            return AgentActivity::Working {
                phase,
                since: self.working_since.unwrap_or_else(std::time::Instant::now),
            };
        }
        if let Some(park) = &self.quota_park {
            return AgentActivity::Parked(park.clone());
        }
        let tasks = self.chrome.activity.as_ref().map_or(0, |dock| {
            dock.subagents_running_direct
                + dock.subagents_running_nested
                + dock.bash_running
                + dock.factory_runs
                + dock.workflow_runs
        });
        if tasks > 0 {
            AgentActivity::Background { tasks }
        } else {
            AgentActivity::Idle
        }
    }
}
