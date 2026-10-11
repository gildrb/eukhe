//! The compactor's model, resolved from settings on every call so a
//! settings change applies without a restart: `memory.model`
//! (`provider/model-id`), else `auxiliaryModel`, else the default model —
//! the agent's startup chain (saved default, featured default, first model
//! with credentials) — at the `memory.thinking` effort (default medium).
//! The `allowedModels` pin applies like everywhere else; an unusable model
//! fails the call (the owner reports it and retries) instead of silently
//! picking another one. The request runs through the durable model
//! collection ([`crate::durable::create_models`]), which serves the
//! registered pi-ai models only.

use std::path::{Path, PathBuf};

use eukhe_pi_ai::models::ModelsSimpleStreamOptions;
use eukhe_pi_ai::types::{SimpleStreamOptions, StreamOptions};
use eukhe_types::ai::{AssistantMessage, Context, Model, ModelThinkingLevel};
use eukhe_types::pi_ai;

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
            let context: pi_ai::Context = convert(&context)
                .map_err(|error| anyhow::anyhow!("compactor context conversion failed: {error}"))?;
            let mut options: ModelsSimpleStreamOptions = SimpleStreamOptions {
                stream: StreamOptions {
                    session_id: Some(COMPACTOR_SESSION.to_string()),
                    ..StreamOptions::default()
                },
                reasoning: reasoning(target.thinking),
                ..SimpleStreamOptions::default()
            }
            .into();
            options.options.stream.request.api_key = target.api_key;
            options.options.stream.request.headers = target.headers.map(|headers| {
                headers
                    .into_iter()
                    .map(|(name, value)| (name, Some(value)))
                    .collect()
            });
            let reply = target
                .models
                .complete_simple(&target.model, context, options)
                .await;
            convert::<_, AssistantMessage>(&reply)
                .map_err(|error| anyhow::anyhow!("compactor reply conversion failed: {error}"))
        })
    }
}

/// One wire shape into the other (the old-ai and pi-ai message types
/// share the TS JSON form).
fn convert<From: serde::Serialize, Into: serde::de::DeserializeOwned>(
    value: &From,
) -> serde_json::Result<Into> {
    serde_json::from_value(serde_json::to_value(value)?)
}

/// The pi-ai reasoning option of a thinking level (`off` sends none).
fn reasoning(level: ModelThinkingLevel) -> Option<pi_ai::ThinkingLevel> {
    match level {
        ModelThinkingLevel::Off => None,
        ModelThinkingLevel::Minimal => Some(pi_ai::ThinkingLevel::Minimal),
        ModelThinkingLevel::Low => Some(pi_ai::ThinkingLevel::Low),
        ModelThinkingLevel::Medium => Some(pi_ai::ThinkingLevel::Medium),
        ModelThinkingLevel::High => Some(pi_ai::ThinkingLevel::High),
        ModelThinkingLevel::Xhigh => Some(pi_ai::ThinkingLevel::Xhigh),
        ModelThinkingLevel::Max => Some(pi_ai::ThinkingLevel::Max),
    }
}

struct Target {
    models: eukhe_pi_ai::models::Models,
    model: pi_ai::Model,
    api_key: Option<String>,
    headers: Option<std::collections::BTreeMap<String, String>>,
    thinking: ModelThinkingLevel,
}

fn resolve(agent_dir: &Path) -> anyhow::Result<Target> {
    // The agent dir doubles as the cwd: the compactor serves every
    // project, so no project's settings may steer it.
    let settings = crate::settings::SettingsManager::create(agent_dir, agent_dir);
    let explicit = settings.get_memory_model().or_else(|| {
        settings
            .get_auxiliary_model()
            .map(str::trim)
            .filter(|model| !model.is_empty())
            .map(str::to_string)
    });
    let auth = crate::auth::AuthStorage::create(agent_dir);
    let mut registry = crate::models::ModelRegistry::create(auth, agent_dir.join("models.json"));
    let (selector, model) = if let Some(selector) = explicit {
        let model = crate::models::resolver::find_exact_model_reference_match(
            &selector,
            registry.get_all(),
        )
        .cloned()
        .ok_or_else(|| {
            anyhow::anyhow!("the memory compactor model {selector} is not in the model catalog")
        })?;
        (selector, model)
    } else {
        // The default model: the same chain that picks the agent's model
        // when no flag or session pins one.
        let all: Vec<Model> = registry.get_all().to_vec();
        let available: Vec<Model> = registry.get_available().into_iter().cloned().collect();
        let options = crate::models::InitialModelOptions {
            cli_provider: None,
            cli_model: None,
            scoped_models: &[],
            is_continuing: false,
            default_provider: settings.get_default_provider(),
            default_model_id: settings.get_default_model(),
            all_models: &all,
            available_models: &available,
        };
        let model = crate::models::find_initial_model(&options).ok_or_else(|| {
            anyhow::anyhow!(
                "no model for the memory compactor: {} Or set memory.model (provider/model-id) in settings.json.",
                crate::models::initial_model_unavailable_message(&options)
            )
        })?;
        (format!("{}/{}", model.provider, model.id), model)
    };
    if let Some(allowlist) = settings.get_allowed_models() {
        if !crate::models::model_allowed(&selector, &allowlist) {
            anyhow::bail!(
                "the memory compactor model {selector} is outside allowedModels: set memory.model to an allowed model"
            );
        }
    }
    let resolved = registry.get_api_key_and_headers(&model, model.headers.as_ref());
    if !resolved.ok {
        anyhow::bail!(
            "no credentials for the memory compactor model {selector}: {}",
            resolved.error.as_deref().unwrap_or("run /login")
        );
    }
    let models = crate::durable::create_models(agent_dir).map_err(|error| {
        anyhow::anyhow!("the memory compactor model collection failed: {error}")
    })?;
    let served = models
        .get_model(&model.provider, &model.id)
        .ok_or_else(|| {
            anyhow::anyhow!(
                "the memory compactor model {selector} is not served by the model collection"
            )
        })?;
    Ok(Target {
        models,
        model: served,
        api_key: resolved.api_key,
        headers: resolved.headers,
        thinking: settings.get_memory_thinking().model_level(),
    })
}
