//! Irreversible effects and per-prompt snapshots in the session view: the
//! end-of-run notice (`run_report`), the ledger `/effects` lists, `/undo`
//! and `/diff [all]`. The texts are `eukhe_types`' (`ledger_text`,
//! `undo_text`, `diff_text`), the ones every surface shows.

use eukhe_types::effects::{ledger_text, RanEffectsReply};
use eukhe_types::undo::{diff_text, undo_text, DiffScope, TurnDiffReply, UndoReply};

use super::{
    AgentView, DaemonCommand, Duration, Map, SessionUi, StatusKind, UI_REQUEST_TIMEOUT_MS,
};

/// What `/diff` compares with, from the text after it (any ASCII case):
/// `None` for a word it does not take.
fn diff_scope(args: &str) -> Option<DiffScope> {
    match args.trim() {
        "" => Some(DiffScope::Turn),
        word if word.eq_ignore_ascii_case("all") => Some(DiffScope::All),
        _ => None,
    }
}

impl SessionUi {
    /// The end-of-run message of a root run: one notice holding the whole
    /// text.
    pub(super) fn push_run_report(&mut self, text: &str, view: &mut AgentView) {
        view.push_entry(super::ChatEntry::Status {
            text: text.to_owned(),
            kind: StatusKind::Warning,
        });
        self.last_status_index = None;
        self.dirty = true;
    }

    /// `/effects`' first part: the session's ledger of irreversible
    /// effects that ran.
    pub(super) async fn list_ran_effects(&mut self, view: &mut AgentView) {
        let listed = self
            .bounded_request(
                Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
                DaemonCommand::GetRanEffects {
                    id: None,
                    active_session_id: self.active_session_id.clone(),
                    rest: Map::default(),
                },
            )
            .await
            .and_then(|data| {
                serde_json::from_value::<RanEffectsReply>(data).map_err(anyhow::Error::from)
            });
        match listed {
            Ok(RanEffectsReply { effects }) => self.plain_row(&ledger_text(&effects), view),
            Err(error) => self.error_row(&format!("{error:#}"), view),
        }
    }

    /// `/undo`: restore the workspace to the start of the newest prompt not
    /// undone; the reply names what it restored and the irreversible
    /// effects of that prompt's run it could not take back.
    pub(super) async fn handle_undo_command(&mut self, args: &str, view: &mut AgentView) {
        if !args.trim().is_empty() {
            self.note_as("Usage: /undo", StatusKind::Warning, view);
            return;
        }
        let undone = self
            .bounded_request(
                Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
                DaemonCommand::UndoTurn {
                    id: None,
                    active_session_id: self.active_session_id.clone(),
                    rest: Map::default(),
                },
            )
            .await
            .and_then(|data| {
                serde_json::from_value::<UndoReply>(data).map_err(anyhow::Error::from)
            });
        match undone {
            Ok(reply) => self.plain_row(undo_text(&reply).trim_end(), view),
            Err(error) => self.error_row(&format!("{error:#}"), view),
        }
    }

    /// `/diff [all]`: what changed since the last prompt started, or since
    /// the session's first prompt.
    pub(super) async fn handle_diff_command(&mut self, args: &str, view: &mut AgentView) {
        let Some(scope) = diff_scope(args) else {
            self.note_as("Usage: /diff [all]", StatusKind::Warning, view);
            return;
        };
        let diffed = self
            .bounded_request(
                Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
                DaemonCommand::GetTurnDiff {
                    id: None,
                    active_session_id: self.active_session_id.clone(),
                    scope,
                    rest: Map::default(),
                },
            )
            .await
            .and_then(|data| {
                serde_json::from_value::<TurnDiffReply>(data).map_err(anyhow::Error::from)
            });
        match diffed {
            Ok(reply) => self.plain_row(diff_text(&reply).trim_end(), view),
            Err(error) => self.error_row(&format!("{error:#}"), view),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diff_takes_no_word_or_all() {
        assert_eq!(
            ["", " all ", "ALL", "since"].map(diff_scope),
            [
                Some(DiffScope::Turn),
                Some(DiffScope::All),
                Some(DiffScope::All),
                None
            ]
        );
    }
}
