//! Irreversible effects in the session view: the end-of-run notice
//! (`run_report`) and the ledger `/effects` lists. The texts are
//! `eukhe_types`' (`run_report_text`, `ledger_text`), the ones every
//! surface shows.

use eukhe_types::effects::{ledger_text, RanEffectsReply};

use super::{
    AgentView, DaemonCommand, Duration, Map, SessionUi, StatusKind, UI_REQUEST_TIMEOUT_MS,
};

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
}
