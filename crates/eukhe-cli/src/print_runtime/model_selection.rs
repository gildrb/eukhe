//! The headless (print/json/RPC) startup model: a flagged `--model`, else
//! the TS `findInitialModel` chain every other mode runs - the `--models`
//! scope, the saved settings default, the featured default, the first
//! authenticated model.

use eukhe_types::ai::Model;

use crate::mode::{RuntimeConfig, SessionOptions};

/// The headless session's startup model.
///
/// # Errors
///
/// Returns the resolver's message when a flagged model does not resolve,
/// or when the catalog holds no model at all.
pub(super) fn select_model(
    registry: &eukhe_core::models::ModelRegistry,
    config: &RuntimeConfig,
    session: &SessionOptions,
) -> Result<Model, String> {
    let available: Vec<Model> = registry.get_available().into_iter().cloned().collect();
    let Some(model_name) = config.model.as_deref() else {
        let all: Vec<Model> = registry.get_all().to_vec();
        let settings =
            eukhe_core::settings::SettingsManager::create(&config.cwd, &config.agent_dir);
        let scoped = config
            .models
            .as_deref()
            .map(|patterns| {
                eukhe_core::models::resolve_model_scope_from_models(patterns, &available)
            })
            .unwrap_or_default();
        return eukhe_core::models::find_initial_model(&eukhe_core::models::InitialModelOptions {
            cli_provider: None,
            cli_model: None,
            scoped_models: &scoped,
            is_continuing: session.resume.is_some()
                || session.continue_recent
                || session.fork.is_some(),
            default_provider: settings.get_default_provider(),
            default_model_id: settings.get_default_model(),
            all_models: &all,
            available_models: &available,
        })
        // No authenticated model: the run-start auth check names the
        // missing credential for the catalog's first model.
        .or_else(|| all.first().cloned())
        .ok_or_else(|| {
            "No models available. Check your installation or add models to models.json.".to_string()
        });
    };
    let resolved =
        eukhe_core::models::resolve_cli_model(config.provider.as_deref(), model_name, &available);
    if let Some(error) = resolved.error {
        return Err(error);
    }
    resolved
        .model
        .ok_or_else(|| "No matching model found.".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The regression: with no `--model` flag the headless runtime skipped
    /// the saved `defaultProvider`/`defaultModel` and, with no featured
    /// default authenticated, fell to the catalog's first model
    /// (`amazon-bedrock`), failing the first print run with "No AWS
    /// credentials available for Bedrock".
    #[test]
    fn the_saved_default_model_serves_an_unflagged_headless_run() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");
        std::fs::write(
            agent_dir.join("settings.json"),
            serde_json::json!({
                "defaultProvider": "anthropic",
                "defaultModel": "claude-sonnet-4-5",
            })
            .to_string(),
        )
        .expect("settings");
        std::fs::write(
            agent_dir.join("auth.json"),
            serde_json::json!({ "anthropic": { "type": "api_key", "key": "sk-test" } }).to_string(),
        )
        .expect("auth");
        let registry = eukhe_core::models::ModelRegistry::create(
            eukhe_core::auth::AuthStorage::create(&agent_dir),
            agent_dir.join("models.json"),
        );
        let config = RuntimeConfig {
            cwd: dir.path().to_path_buf(),
            agent_dir,
            ..RuntimeConfig::default()
        };
        let model =
            select_model(&registry, &config, &SessionOptions::default()).expect("startup model");
        assert_eq!(
            (model.provider.as_str(), model.id.as_str()),
            ("anthropic", "claude-sonnet-4-5")
        );
    }
}
