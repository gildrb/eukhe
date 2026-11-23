//! The status-row concern: the note/toast/error-row rendering family
//! (TS `showStatus`/`showError`) and the tray rebuild.
use super::{AgentView, ChatEntry, SessionUi, StatusKind};
use crate::glyphs::WARN;

impl SessionUi {
    /// One `loop_update` session event: store the status and sync the
    /// status line's loop label. (The loop reports its start and its end
    /// in transcript rows of its own.)
    pub(super) fn apply_loop_update(
        &mut self,
        status: eukhe_types::loop_mode::LoopStatus,
        view: &mut AgentView,
    ) {
        if self.loop_view.apply_update(status) {
            self.sync_activity_dock(view);
        }
    }

    /// Re-apply the refreshed context usage to the chrome state.
    pub(crate) fn rebuild_tray(&mut self, view: &mut AgentView) {
        view.chrome.context = self.context;
        view.chrome.budget.clone_from(&self.budget);
        view.chrome.memory = self.memory;
        view.chrome.verification = self.verification;
        view.chrome.session_name.clone_from(&self.session_name);
        self.dirty = true;
    }

    pub(crate) fn note(&mut self, text: &str, view: &mut AgentView) {
        self.note_as(text, StatusKind::Info, view);
    }

    /// Show an ephemeral action toast (the top-right auto-dismiss overlay;
    /// a sanctioned divergence from TS -- see `toast`): the confirmation
    /// never lands in the transcript, and the frame repaints so the
    /// overlay appears at once (its expiry repaints it away).
    pub(crate) fn toast(&mut self, text: &str, view: &mut AgentView) {
        view.toasts.push(text);
        self.dirty = true;
    }

    /// A plain appended dim row (TS `chatContainer.addChild(new
    /// Markdown/Text(...))` -- `/name` and `/rlm-max-depth` report rows):
    /// unlike `note` it never rewrites the previous status in place, so
    /// back-to-back rows stack like the TS plain rows.
    pub(crate) fn plain_row(&mut self, text: &str, view: &mut AgentView) {
        view.push_entry(ChatEntry::Status {
            text: text.to_string(),
            kind: StatusKind::Info,
        });
        self.last_status_index = None;
        self.dirty = true;
    }

    /// TS `showStatus` with a tone: the same back-to-back in-place rewrite
    /// as [`Self::note`], with the row's kind following the TS tone.
    pub(crate) fn note_as(&mut self, text: &str, kind: StatusKind, view: &mut AgentView) {
        // TS `showStatus`: a status emitted back-to-back (nothing else
        // reached the chat since the previous one) rewrites the previous
        // status row in place instead of appending a new one.
        let updated_in_place = match self.last_status_index {
            Some(index) if index + 1 == view.chat_len() => {
                view.update_status_row(index, text, kind.clone())
            }
            _ => false,
        };
        if !updated_in_place {
            view.push_entry(ChatEntry::Status {
                text: text.to_string(),
                kind,
            });
            self.last_status_index = Some(view.chat_len() - 1);
        }
        self.dirty = true;
    }

    /// The TS `showError` row: `! Error: <message>` in the error color.
    pub(crate) fn error_row(&mut self, message: &str, view: &mut AgentView) {
        view.push_entry(ChatEntry::Status {
            text: format!("{WARN} Error: {message}"),
            kind: StatusKind::Error,
        });
        self.dirty = true;
    }

    /// One warning row per problem (a missing or invalid theme, a
    /// registered theme file that failed to load, a `binds.cfg` that could
    /// not be read).
    pub(crate) fn warning_rows(&mut self, warnings: &[String], view: &mut AgentView) {
        for warning in warnings {
            view.push_entry(ChatEntry::Status {
                text: format!("Warning: {warning}"),
                kind: StatusKind::Warning,
            });
            self.last_status_index = None;
            self.dirty = true;
        }
    }
}
