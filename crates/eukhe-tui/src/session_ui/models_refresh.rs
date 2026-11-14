//! `/models refresh`: the daemon asks the signed-in providers for their
//! model lists (`refresh_models`); the answer's report lines show as notes
//! and its catalog replaces the picker catalog, so the added models are
//! selectable at once. The request runs in the background: its answer
//! lands on the catalog channel ([`CatalogLanding`]).

use super::{AgentView, CatalogLanding, DaemonCommand, Map, ModelCatalogUpdate, SessionUi, Value};

/// The report lines of a `refresh_models` answer.
fn report_lines(answer: &Value) -> Vec<String> {
    answer
        .get("lines")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect()
}

impl SessionUi {
    /// Start a refresh of the signed-in providers' model lists.
    pub(super) fn start_models_refresh(&mut self, view: &mut AgentView) {
        self.note("Refreshing model lists...", view);
        let client = self.client.clone();
        let active_session_id = self.active_session_id.clone();
        let landings = self.catalog_updates.clone();
        tokio::spawn(async move {
            let landing = match client
                .request_ok(DaemonCommand::RefreshModels {
                    id: None,
                    active_session_id,
                    providers: Vec::new(),
                    rest: Map::default(),
                })
                .await
            {
                Ok(answer) => CatalogLanding::Refreshed {
                    lines: report_lines(&answer),
                    catalog: ModelCatalogUpdate::of_answer(&answer),
                },
                Err(error) => CatalogLanding::RefreshFailed(format!("{error:#}")),
            };
            let _ = landings.send(landing);
        });
    }

    /// Fold what landed on the catalog channel: a fetched catalog, a
    /// refresh's catalog and report lines, or a refresh's error row.
    pub(crate) fn apply_catalog_landing(&mut self, landing: CatalogLanding, view: &mut AgentView) {
        match landing {
            CatalogLanding::Fetched(update) => self.apply_model_catalog(update, view),
            CatalogLanding::Refreshed { lines, catalog } => {
                self.apply_model_catalog(catalog, view);
                for line in lines {
                    self.note(&line, view);
                }
            }
            CatalogLanding::RefreshFailed(error) => self.error_row(&error, view),
        }
    }
}
