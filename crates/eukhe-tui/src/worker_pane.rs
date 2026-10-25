//! The live worker pane (docs/interface.md, "Worker pane"): the main
//! session's worker shown next to the main chat, without leaving it.
//!
//! The pane is a watch attach (`clientKind: "watch"`) of the worker on the
//! main connection: the worker's snapshot seeds a transcript of its own,
//! and its events fold into it live (text as it streams, tool cards as
//! they run and settle, the rows main forwarded). A watch takes none of
//! the worker's approvals and never holds its kernel, so showing the pane
//! changes nothing about how the worker runs. The rows render through a
//! nested [`AgentView`], the same row renderers the main chat uses.
//!
//! Where the pane sits: a right split when the terminal is at least
//! [`SPLIT_MIN_WIDTH`] columns wide, otherwise a strip of
//! [`STRIP_ROWS`] rows under the transcript; the full view gives it the
//! whole transcript area. The inline screen mode commits finished rows to
//! the terminal's scrollback at full width, so there the pane is always
//! the strip.

use eukhe_types::daemon::{StreamUpdate, WorkerRunState};

use crate::activity::TurnPhase;
use crate::chat::{ChatEntry, ToolResultView, WorkingState};
use crate::snapshot::{attach_data_from_response, reconstruct, TurnUpdate};
use crate::style::Modifier;
use crate::theme::{Theme, ThemeColor};
use crate::view::AgentView;
use crate::width::{pad_line, truncate_line};
use crate::{Line, Span};

/// The narrowest terminal the pane splits to the right in.
pub const SPLIT_MIN_WIDTH: usize = 140;

/// The rows the bottom strip takes (header included), at most half the
/// transcript area.
pub const STRIP_ROWS: usize = 12;

/// Events kept while the watch attach travels: the snapshot answers
/// later, and the events past its cursor apply on top of it.
const ATTACH_BUFFER_MAX: usize = 4096;

/// How the pane shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PaneMode {
    /// Not on screen (the watch stays attached; Alt+W shows it again).
    Hidden,
    /// Beside the main chat: a right split or a bottom strip.
    Docked,
    /// The whole transcript area (Esc returns to docked).
    Full,
}

/// Where a docked or full pane lands in a frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Placement {
    /// No pane in this frame.
    None,
    /// A column of `width` on the right, one separator column before it.
    Right { width: usize },
    /// A strip of `rows` under the main transcript.
    Bottom { rows: usize },
    /// The pane takes the whole transcript area.
    Full,
}

/// Where the pane goes in a `width` x `rows` transcript area. `split`
/// says whether the screen can split columns (fullscreen; the inline mode
/// cannot).
#[must_use]
pub fn placement(mode: PaneMode, width: usize, rows: usize, split: bool) -> Placement {
    match mode {
        PaneMode::Hidden => Placement::None,
        PaneMode::Full => Placement::Full,
        PaneMode::Docked if split && width >= SPLIT_MIN_WIDTH => Placement::Right {
            width: width * 2 / 5,
        },
        PaneMode::Docked => Placement::Bottom {
            rows: STRIP_ROWS.min(rows / 2),
        },
    }
}

/// The watch attach's progress.
#[derive(Debug)]
enum Attach {
    /// The attach travels: events wait here, in arrival order, with
    /// their sequence.
    Pending(Vec<(u64, TurnUpdate)>),
    /// The snapshot landed: events past `sequence` apply.
    Live { sequence: u64 },
    /// The attach failed: the pane says why.
    Failed(String),
}

/// One worker's live pane.
pub struct WorkerPane {
    /// The worker's active session id (the events' `activeSessionId`).
    pub active_session_id: String,
    /// The worker's display name.
    pub name: String,
    /// The worker's run state, from main's roster row.
    pub state: WorkerRunState,
    pub mode: PaneMode,
    attach: Attach,
    /// The worker's rows and their renderers.
    view: Box<AgentView>,
    /// The assistant entry the next streamed frame updates.
    streaming_index: Option<usize>,
}

impl WorkerPane {
    /// A pane for the worker `active_session_id`, its watch attach on the
    /// way.
    #[must_use]
    pub fn new(
        active_session_id: String,
        name: String,
        state: WorkerRunState,
        theme: Theme,
    ) -> Self {
        let mut view = Box::new(AgentView::new(theme));
        view.splash_suppressed = true;
        Self {
            active_session_id,
            name,
            state,
            mode: PaneMode::Docked,
            attach: Attach::Pending(Vec::new()),
            view,
            streaming_index: None,
        }
    }

    /// The watch attach answered: the snapshot's rows replace the pane's,
    /// then the events that arrived past its cursor apply.
    pub fn attached(&mut self, result: Result<serde_json::Value, String>) {
        let snapshot = result.and_then(|data| {
            let data = attach_data_from_response(data).map_err(|error| format!("{error:#}"))?;
            reconstruct(&data).map_err(|error| error.to_string())
        });
        let rebuilt = match snapshot {
            Ok(rebuilt) => rebuilt,
            Err(error) => {
                self.attach = Attach::Failed(error);
                return;
            }
        };
        let buffered = match std::mem::replace(
            &mut self.attach,
            Attach::Live {
                sequence: rebuilt.last_event_sequence,
            },
        ) {
            Attach::Pending(buffered) => buffered,
            Attach::Live { .. } | Attach::Failed(_) => Vec::new(),
        };
        self.view.chat = rebuilt.chat;
        self.streaming_index = None;
        self.view.working = None;
        if rebuilt.turn_running {
            self.loader(TurnPhase::Requesting);
        }
        for (sequence, update) in buffered {
            self.apply(sequence, update);
        }
    }

    /// One worker event, with its event sequence (`0` when the frame
    /// carried none).
    pub fn apply(&mut self, sequence: u64, update: TurnUpdate) {
        match &mut self.attach {
            Attach::Pending(buffered) => {
                if buffered.len() < ATTACH_BUFFER_MAX {
                    buffered.push((sequence, update));
                }
                return;
            }
            Attach::Live { sequence: seen } => {
                if sequence != 0 {
                    if sequence <= *seen {
                        return;
                    }
                    *seen = sequence;
                }
            }
            Attach::Failed(_) => return,
        }
        self.fold(update);
    }

    /// Fold one live update into the rows (the main chat's live fold,
    /// narrowed to what the pane shows: the rows, tool cards and the
    /// loader; no queue, no speed, no retry countdown).
    fn fold(&mut self, update: TurnUpdate) {
        match update {
            TurnUpdate::RunStarted | TurnUpdate::TurnStarted => {
                self.loader(TurnPhase::Requesting);
            }
            TurnUpdate::UserMessage(text) => self.view.push_entry(ChatEntry::User { text }),
            TurnUpdate::CustomRow(entry) | TurnUpdate::RetryOutcomeRow(entry) => {
                self.view.push_entry(entry);
            }
            TurnUpdate::AssistantMessage {
                message,
                streaming,
                stream_event,
            } => self.assistant(&message, streaming, stream_event.as_ref()),
            TurnUpdate::ToolExecutionStart {
                tool_call_id,
                tool_name,
                args,
            } => {
                crate::snapshot::apply_tool_execution_start(
                    &mut self.view,
                    &tool_call_id,
                    &tool_name,
                    args,
                );
                self.loader(TurnPhase::RunningTool);
            }
            TurnUpdate::ToolExecutionUpdate {
                tool_call_id,
                partial,
            } => self.tool_result(&tool_call_id, ToolResultView::new(&partial, false), true),
            TurnUpdate::ToolExecutionEnd {
                tool_call_id,
                result,
                is_error,
            } => {
                self.tool_result(&tool_call_id, ToolResultView::new(&result, is_error), false);
                self.loader(TurnPhase::Requesting);
            }
            TurnUpdate::TurnEnded { .. } => self.streaming_index = None,
            TurnUpdate::Idle => {
                self.streaming_index = None;
                self.view.stop_loader();
            }
            TurnUpdate::AgentRelay(relay) => self.view.push_entry(ChatEntry::Swarm(Box::new(
                crate::swarm_block::SwarmRow::Relay(relay),
            ))),
            TurnUpdate::SessionInfoChanged { .. }
            | TurnUpdate::ServiceTierChanged { .. }
            | TurnUpdate::AutoRetryStart { .. }
            | TurnUpdate::AutoRetryEnd { .. }
            | TurnUpdate::CompactionStart { .. }
            | TurnUpdate::CompactionSummaryDelta { .. }
            | TurnUpdate::CompactionEnd { .. }
            | TurnUpdate::ChatTurnWait { .. }
            | TurnUpdate::PromptProgress(_)
            | TurnUpdate::MemoryUpdate(_)
            | TurnUpdate::GoalUpdate(_)
            | TurnUpdate::QueueUpdated(_)
            | TurnUpdate::BashStart { .. }
            | TurnUpdate::BashOutput { .. }
            | TurnUpdate::BashEnd { .. }
            | TurnUpdate::StatusUpdate => {}
        }
    }

    /// An assistant frame: the open message updates in place, a new one
    /// opens at `message_start`; its tool calls become cards; a failed
    /// final frame shows its error row.
    fn assistant(
        &mut self,
        message: &eukhe_types::ai::AssistantMessage,
        streaming: bool,
        stream_event: Option<&StreamUpdate>,
    ) {
        let (blocks, tool_calls) = crate::snapshot::assistant_message_parts(message);
        if matches!(stream_event, Some(StreamUpdate::Start)) {
            self.streaming_index = None;
        }
        let error = if streaming {
            None
        } else {
            crate::snapshot::assistant_error_row(message, &tool_calls)
        };
        let has_tool_calls = !tool_calls.is_empty();
        let open = self
            .streaming_index
            .filter(|index| matches!(self.view.chat.get(*index), Some(ChatEntry::Assistant(_))));
        match open {
            Some(index) => {
                if let Some(ChatEntry::Assistant(entry)) = self.view.chat.get_mut(index) {
                    entry.blocks = blocks;
                    entry.has_tool_calls = has_tool_calls;
                    entry.streaming = streaming;
                    if let Some(error) = &error {
                        entry.error = Some(error.text.clone());
                        entry.aborted = error.aborted;
                    }
                }
                self.view.mark_entry_stale(index);
            }
            None if !blocks.is_empty() || error.is_some() => {
                self.view.push_entry(ChatEntry::Assistant(Box::new(
                    crate::chat::AssistantMessage {
                        blocks,
                        has_tool_calls,
                        streaming,
                        error: error.as_ref().map(|error| error.text.clone()),
                        aborted: error.as_ref().is_some_and(|error| error.aborted),
                    },
                )));
                self.streaming_index = Some(self.view.chat.len() - 1);
            }
            None => {}
        }
        for (id, name, args) in &tool_calls {
            crate::snapshot::apply_streamed_tool_card(&mut self.view, id, name, args);
        }
        if streaming {
            self.loader(TurnPhase::Writing);
        } else {
            self.streaming_index = None;
        }
    }

    /// A (partial or final) result lands on the newest card of its call.
    fn tool_result(&mut self, tool_call_id: &str, result: ToolResultView, partial: bool) {
        let Some(index) = self.view.chat.iter().rposition(
            |entry| matches!(entry, ChatEntry::Tool(card) if card.id == tool_call_id && !card.aborted),
        ) else {
            return;
        };
        if let Some(ChatEntry::Tool(card)) = self.view.chat.get_mut(index) {
            card.result = Some(result);
            card.result_partial = partial;
            if !partial {
                card.ended_at = Some(std::time::Instant::now());
            }
        }
        self.view.mark_entry_stale(index);
    }

    /// The pane's loader at `phase`: an up loader keeps its clock.
    fn loader(&mut self, phase: TurnPhase) {
        match &mut self.view.working {
            Some(working) => working.phase = phase,
            None => self.view.start_loader(
                WorkingState {
                    phase,
                    message: None,
                    download: false,
                    tokens: 0,
                    elapsed_secs: 0,
                },
                std::time::Instant::now(),
            ),
        }
    }

    /// The worker works now: its loader is up (the frame loop animates
    /// while it is).
    #[must_use]
    pub fn working(&self) -> bool {
        self.view.working.is_some()
    }

    /// The pane's rows: a header naming the worker and its state, then
    /// the newest rows of its transcript, exactly `rows` rows of `width`.
    pub(crate) fn render(&mut self, look: &PaneLook<'_>, width: usize, rows: usize) -> Vec<Line> {
        if rows == 0 || width == 0 {
            return Vec::new();
        }
        let theme = look.theme;
        self.view.pulse_frame = look.pulse_frame;
        self.view.detail = look.detail;
        let mut out = vec![self.header(theme, look.hint)];
        let body_rows = rows - 1;
        let body = match &self.attach {
            Attach::Pending(_) => vec![vec![Span::styled(
                " attaching to the worker...",
                theme.fg_style(ThemeColor::Dim),
            )]],
            Attach::Failed(error) => vec![vec![Span::styled(
                format!(" the worker pane could not attach: {error}"),
                theme.fg_style(ThemeColor::Error),
            )]],
            Attach::Live { .. } => self.view.render_last_rows(width, body_rows),
        };
        out.extend(body.into_iter().take(body_rows));
        out.resize_with(rows, Vec::new);
        out.into_iter()
            .map(|line| pad_line(truncate_line(&line, width, crate::glyphs::ELLIPSIS), width))
            .collect()
    }

    /// ` worker - running  <hint>`.
    fn header(&self, theme: &Theme, hint: &str) -> Line {
        let (state, color) = match self.state {
            WorkerRunState::Running => ("running", ThemeColor::Success),
            WorkerRunState::Paused => ("paused", ThemeColor::Warning),
            WorkerRunState::Idle => ("idle", ThemeColor::Muted),
            WorkerRunState::Stopped => ("stopped", ThemeColor::Dim),
        };
        vec![
            Span::raw(" "),
            Span::styled(
                self.name.clone(),
                theme
                    .fg_style(ThemeColor::Accent)
                    .add_modifier(Modifier::BOLD),
            ),
            Span::styled(crate::glyphs::SEP, theme.fg_style(ThemeColor::Dim)),
            Span::styled(state, theme.fg_style(color)),
            Span::styled(format!("  {hint}"), theme.fg_style(ThemeColor::Dim)),
        ]
    }
}

/// What a pane render takes from the main view.
pub(crate) struct PaneLook<'a> {
    pub(crate) theme: &'a Theme,
    pub(crate) pulse_frame: usize,
    pub(crate) detail: crate::chat::Detail,
    /// The keys the header names (`Alt+W: hide - Alt+Shift+W: full`).
    pub(crate) hint: &'a str,
}

/// `view`'s worker pane as `rows` rows of `width` (none without a pane).
pub(crate) fn pane_rows(view: &mut AgentView, width: usize, rows: usize) -> Vec<Line> {
    let Some(mut pane) = view.worker_pane.take() else {
        return Vec::new();
    };
    let kb = view.editor.keybindings();
    let hint = match pane.mode {
        PaneMode::Full => format!(
            "{}: back",
            kb.first_key("app.input.clear").map_or_else(
                || "Esc".to_string(),
                |key| crate::keybindings::format_key_text(&key)
            )
        ),
        PaneMode::Docked | PaneMode::Hidden => format!(
            "{}: hide - {}: full",
            kb.key_text("app.worker.toggle"),
            kb.key_text("app.worker.full")
        ),
    };
    let look = PaneLook {
        theme: &view.theme,
        pulse_frame: view.pulse_frame,
        detail: view.detail,
        hint: &hint,
    };
    let out = pane.render(&look, width, rows);
    view.worker_pane = Some(pane);
    out
}

/// The main rows (each padded to `main_width`) with the pane's rows to
/// their right, a dim separator column between them.
pub(crate) fn beside(
    main: Vec<Line>,
    pane: Vec<Line>,
    main_width: usize,
    theme: &Theme,
) -> Vec<Line> {
    let rows = main.len().max(pane.len());
    let mut pane = pane.into_iter();
    let mut main = main.into_iter();
    (0..rows)
        .map(|_| {
            let mut line = pad_line(
                truncate_line(
                    &main.next().unwrap_or_default(),
                    main_width,
                    crate::glyphs::ELLIPSIS,
                ),
                main_width,
            );
            line.push(Span::styled(
                crate::glyphs::BAR,
                theme.fg_style(ThemeColor::Dim),
            ));
            line.extend(pane.next().unwrap_or_default());
            line
        })
        .collect()
}

#[cfg(test)]
mod tests;
