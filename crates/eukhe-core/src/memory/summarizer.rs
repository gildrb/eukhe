//! The compactor's model, resolved from settings on every call so a
//! settings change applies without a restart: `memory.model`
//! (`provider/model-id`), else `auxiliaryModel`, else the default model, at
//! the `memory.thinking` effort (default medium). The `allowedModels` pin
//! applies like everywhere else; an unusable model fails the call (the
//! owner reports it and retries) instead of silently picking another one.

use std::path::{Path, PathBuf};

use eukhe_types::ai::{Context, Model, ModelThinkingLevel};

use super::compactor::{Summarizer, SummarizerFuture};

/// The `session_id` of every compactor request: providers key prompt-cache
/// routing on it, and the compactor's `<chat>` prefix is shared across
/// calls.
const COMPACTOR_SESSION: &str = "chat-memory-compactor";

/// The settings-backed compactor model.
#[derive(Debug, Clone)]
pub struct SettingsSummarizer {
    agent_dir: PathBuf,
}

impl SettingsSummarizer {
    /// Resolve against the settings, auth and models of `agent_dir`.
    #[must_use]
    pub fn new(agent_dir: PathBuf) -> SettingsSummarizer {
        SettingsSummarizer { agent_dir }
    }
}

impl Summarizer for SettingsSummarizer {
    fn complete(&self, context: Context) -> SummarizerFuture {
        let agent_dir = self.agent_dir.clone();
        Box::pin(async move {
            // Resolution reads settings and auth from disk and may refresh
            // an OAuth token with a blocking request: off the executor.
            let target = tokio::task::spawn_blocking(move || resolve(&agent_dir))
                .await
                .map_err(|error| anyhow::anyhow!("compactor model resolution failed: {error}"))??;
            let options = eukhe_ai::types::SimpleStreamOptions {
                base: eukhe_ai::types::StreamOptions {
                    api_key: target.api_key,
                    headers: target.headers.map(|headers| headers.into_iter().collect()),
                    session_id: Some(COMPACTOR_SESSION.to_string()),
                    ..Default::default()
                },
                reasoning: Some(target.thinking),
                thinking_budgets: None,
            };
            eukhe_ai::complete_simple(&target.model, &context, Some(options))
                .await
                .map_err(|error| anyhow::anyhow!("compactor model call failed: {error:?}"))
        })
    }
}

struct Target {
    model: Model,
    api_key: Option<String>,
    headers: Option<std::collections::BTreeMap<String, String>>,
    thinking: ModelThinkingLevel,
}

fn resolve(agent_dir: &Path) -> anyhow::Result<Target> {
    // The agent dir doubles as the cwd: the compactor serves every
    // project, so no project's settings may steer it.
    let settings = crate::settings::SettingsManager::create(agent_dir, agent_dir);
    let selector = settings
        .get_memory_model()
        .or_else(|| {
            settings
                .get_auxiliary_model()
                .map(str::trim)
                .filter(|model| !model.is_empty())
                .map(str::to_string)
        })
        .or_else(|| {
            let provider = settings.get_default_provider()?;
            let model = settings.get_default_model()?;
            Some(format!("{provider}/{model}"))
        })
        .ok_or_else(|| {
            anyhow::anyhow!(
                "no model for the memory compactor: set memory.model (provider/model-id) in settings.json"
            )
        })?;
    if let Some(allowlist) = settings.get_allowed_models() {
        if !crate::models::model_allowed(&selector, &allowlist) {
            anyhow::bail!("the memory compactor model {selector} is outside allowedModels");
        }
    }
    let auth = crate::auth::AuthStorage::create(agent_dir);
    let mut registry = crate::models::ModelRegistry::create(auth, agent_dir.join("models.json"));
    registry.load_private_authorization_from_cache();
    let model =
        crate::models::resolver::find_exact_model_reference_match(&selector, registry.get_all())
            .cloned()
            .ok_or_else(|| {
                anyhow::anyhow!("the memory compactor model {selector} is not in the model catalog")
            })?;
    let resolved = registry.get_api_key_and_headers(&model, model.headers.as_ref());
    if !resolved.ok {
        anyhow::bail!(
            "no credentials for the memory compactor model {selector}: {}",
            resolved.error.as_deref().unwrap_or("run /login")
        );
    }
    Ok(Target {
        model,
        api_key: resolved.api_key,
        headers: resolved.headers,
        thinking: settings.get_memory_thinking().model_level(),
    })
}
