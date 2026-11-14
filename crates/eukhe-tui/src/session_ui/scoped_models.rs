//! The `/scoped-models` concern: open the selector over the signed-in
//! providers' models and the session's scope, apply each change to the
//! session (`set_scoped_models`, the list the model-cycle keys step
//! through), and save the scope to the `enabledModels` setting on the
//! save key.
use std::collections::HashMap;

use super::model_picker::picker_viewport_rows;
use super::UI_REQUEST_TIMEOUT_MS;
use super::{
    key_event_to_id, AgentView, DaemonCommand, Duration, KeyEvent, Map, Result, SessionUi,
};
use crate::scoped_models::{Scope, ScopedModelsAction, ScopedModelsSelector};
use eukhe_types::ai::{CatalogModel, Model};
use serde_json::{json, Value};

/// The models of the signed-in providers, in catalog order.
fn available_models(
    catalog: &[CatalogModel],
    configured: &std::collections::HashSet<String>,
) -> Vec<Model> {
    catalog
        .iter()
        .filter(|entry| configured.contains(&entry.model.provider))
        .map(|entry| entry.model.clone())
        .collect()
}

/// The session's scope from its connection state: the `provider/id` keys
/// in order and the thinking level an entry pins.
fn session_scope(state: Option<&Value>) -> (Scope, HashMap<String, String>) {
    let entries: Vec<(String, Option<String>)> = state
        .and_then(|state| state.get("scopedModels"))
        .and_then(Value::as_array)
        .map(|entries| {
            entries
                .iter()
                .filter_map(|entry| {
                    let model = entry.get("model")?;
                    let key = format!(
                        "{}/{}",
                        model.get("provider")?.as_str()?,
                        model.get("id")?.as_str()?
                    );
                    let level = entry
                        .get("thinkingLevel")
                        .and_then(Value::as_str)
                        .map(str::to_string);
                    Some((key, level))
                })
                .collect()
        })
        .unwrap_or_default();
    let levels = entries
        .iter()
        .filter_map(|(key, level)| Some((key.clone(), level.clone()?)))
        .collect();
    let keys: Vec<String> = entries.into_iter().map(|(key, _)| key).collect();
    let scope = if keys.is_empty() {
        Scope::All
    } else {
        Scope::Only(keys)
    };
    (scope, levels)
}

/// The `set_scoped_models` entries of `keys`: each `{ model: { provider,
/// id }, thinkingLevel? }`.
fn scoped_entries(keys: &[String], levels: &HashMap<String, String>) -> Vec<Value> {
    keys.iter()
        .filter_map(|key| {
            let (provider, id) = key.split_once('/')?;
            let mut entry = json!({ "model": { "provider": provider, "id": id } });
            if let Some(level) = levels.get(key) {
                entry["thinkingLevel"] = json!(level);
            }
            Some(entry)
        })
        .collect()
}

/// The `enabledModels` patterns of `scope`: none for no scope, else each
/// key with the level it pins (`provider/id:level`).
fn setting_patterns(scope: &Scope, levels: &HashMap<String, String>) -> Vec<String> {
    match scope {
        Scope::All => Vec::new(),
        Scope::Only(keys) => keys
            .iter()
            .map(|key| match levels.get(key) {
                Some(level) => format!("{key}:{level}"),
                None => key.clone(),
            })
            .collect(),
    }
}

impl SessionUi {
    /// Open `/scoped-models` on the session's scope. A stale catalog
    /// refreshes from the daemon in the background and lands in the open
    /// selector.
    pub(super) async fn open_scoped_models(&mut self, view: &mut AgentView) {
        if self.model_refresh_due(false) {
            self.spawn_model_catalog_refresh();
        }
        let state = self.connection_state(view).await;
        let (scope, levels) = session_scope(state.as_ref());
        view.scoped_models = Some(ScopedModelsSelector::new(
            available_models(&self.model_catalog, &self.model_configured_providers),
            scope,
            levels,
            picker_viewport_rows(view.terminal_rows()),
        ));
        self.dirty = true;
    }

    /// A landed catalog refresh reaches an open selector.
    pub(super) fn update_scoped_models_catalog(&self, view: &mut AgentView) {
        if let Some(selector) = view.scoped_models.as_mut() {
            selector.update_models(available_models(
                &self.model_catalog,
                &self.model_configured_providers,
            ));
        }
    }

    /// One key press while `/scoped-models` is open.
    pub(super) async fn handle_scoped_models_key(
        &mut self,
        key: KeyEvent,
        view: &mut AgentView,
    ) -> Result<()> {
        let Some(id) = key_event_to_id(&key) else {
            return Ok(());
        };
        if id == "ctrl+c" {
            self.exit_guard.note_ctrl_c_handled();
        }
        let action = view
            .scoped_models
            .as_mut()
            .map(|selector| selector.handle_key(&id, view.editor.keybindings()));
        match action {
            Some(ScopedModelsAction::None) | None => {}
            Some(ScopedModelsAction::Close) => view.scoped_models = None,
            Some(ScopedModelsAction::Changed(scope)) => self.apply_scope(&scope, view).await,
            Some(ScopedModelsAction::Save(scope)) => self.save_scope(&scope, view),
        }
        self.dirty = true;
        Ok(())
    }

    /// Apply `scope` to the session: the cycle keys step through it now.
    async fn apply_scope(&mut self, scope: &Scope, view: &mut AgentView) {
        let Some(entries) = view.scoped_models.as_ref().map(|selector| {
            scoped_entries(&selector.session_keys(scope), selector.pinned_levels())
        }) else {
            return;
        };
        let applied = self
            .bounded_request(
                Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
                DaemonCommand::SetScopedModels {
                    id: None,
                    active_session_id: self.active_session_id.clone(),
                    scoped_models: Value::Array(entries),
                    rest: Map::default(),
                },
            )
            .await;
        if let Err(error) = applied {
            self.error_row(&format!("{error:#}"), view);
        }
    }

    /// Save `scope` to the `enabledModels` setting.
    fn save_scope(&mut self, scope: &Scope, view: &mut AgentView) {
        let Some(settings) = self.client_settings.clone() else {
            self.error_row("Settings are not available in this client", view);
            return;
        };
        let Some(patterns) = view
            .scoped_models
            .as_ref()
            .map(|selector| setting_patterns(scope, selector.pinned_levels()))
        else {
            return;
        };
        match settings.set_enabled_models(&patterns) {
            Ok(()) => {
                if let Some(selector) = view.scoped_models.as_mut() {
                    selector.mark_saved();
                }
                self.note("Model scope saved to settings", view);
            }
            Err(error) => self.error_row(&format!("{error:#}"), view),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The session state's scoped list reads as the scope and its pinned
    /// levels; the entries and the setting patterns carry the levels
    /// back.
    #[test]
    fn scope_round_trips_with_levels() {
        let state = json!({ "scopedModels": [
            { "model": { "provider": "anthropic", "id": "claude-haiku-5-5" }, "thinkingLevel": "low" },
            { "model": { "provider": "openai-codex", "id": "gpt-6-sol" } }
        ]});
        let (scope, levels) = session_scope(Some(&state));
        let keys = vec![
            "anthropic/claude-haiku-5-5".to_string(),
            "openai-codex/gpt-6-sol".to_string(),
        ];
        assert_eq!(scope, Scope::Only(keys.clone()));
        assert_eq!(
            scoped_entries(&keys, &levels),
            vec![
                json!({ "model": { "provider": "anthropic", "id": "claude-haiku-5-5" }, "thinkingLevel": "low" }),
                json!({ "model": { "provider": "openai-codex", "id": "gpt-6-sol" } }),
            ]
        );
        assert_eq!(
            setting_patterns(&scope, &levels),
            vec!["anthropic/claude-haiku-5-5:low", "openai-codex/gpt-6-sol"]
        );
        assert_eq!(session_scope(Some(&json!({}))).0, Scope::All);
        assert!(setting_patterns(&Scope::All, &levels).is_empty());
    }
}
