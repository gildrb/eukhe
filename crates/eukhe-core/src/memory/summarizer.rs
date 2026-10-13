//! The compactor's model, resolved from settings on every call so a
//! settings change applies without a restart: `memory.model`
//! (`provider/model-id`), else `auxiliaryModel`, else the default model —
//! the agent's startup chain (saved default, featured default, first model
//! with credentials) — at the `memory.thinking` effort (default medium).
//! The `allowedModels` pin applies like everywhere else; an unusable model
//! fails the call (the owner reports it and retries) instead of silently
//! picking another one. The request runs through the durable model
//! collection ([`crate::durable::create_models`]), which serves the
//! registered pi-ai models only. It asks for at most [`MAX_TOKENS`], and a
//! dropped call cancels it.

use std::path::{Path, PathBuf};

use eukhe_ai::api::simple_options::{DEFAULT_THINKING_BUDGETS, MIN_ANSWER_TOKENS};
use eukhe_ai::models::ModelsSimpleStreamOptions;
use eukhe_ai::types::{SimpleStreamOptions, StreamOptions};
use eukhe_chord::context::AbortController;
use eukhe_types::ai::{Model, ModelThinkingLevel};
use eukhe_types::pi_ai::{self, Context};

use super::compactor::{Summarizer, SummarizerFuture};

/// The `session_id` of every compactor request: providers key prompt-cache
/// routing on it, and the compactor's `<chat>` prefix is shared across
/// calls.
const COMPACTOR_SESSION: &str = "chat-memory-compactor";

/// The output cap of one compactor call: a high-effort think (the default
/// `high` budget) and room for a line of [`super::NODE`] bytes (the answer
/// floor). The model's own output budget, often many times larger, would
/// let one call run on for minutes or hours; a smaller one still applies.
const MAX_TOKENS: u64 = DEFAULT_THINKING_BUDGETS.high.unwrap() + MIN_ANSWER_TOKENS;

/// Cancels a compactor call's request when the call is dropped: the
/// provider streams on a task of its own, which only the signal stops.
struct AbortOnDrop(AbortController);

impl Drop for AbortOnDrop {
    fn drop(&mut self) {
        self.0.abort(None);
    }
}

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
            let abort = AbortOnDrop(AbortController::new());
            let mut options: ModelsSimpleStreamOptions = SimpleStreamOptions {
                stream: StreamOptions {
                    session_id: Some(COMPACTOR_SESSION.to_string()),
                    // A model budget of 0 names none.
                    max_tokens: Some(match target.model.max_tokens {
                        0 => MAX_TOKENS,
                        budget => budget.min(MAX_TOKENS),
                    }),
                    ..StreamOptions::default()
                },
                reasoning: reasoning(target.thinking),
                ..SimpleStreamOptions::default()
            }
            .into();
            options.options.stream.request.signal = Some(abort.0.signal());
            options.options.stream.request.api_key = target.api_key;
            options.options.stream.request.headers = target.headers.map(|headers| {
                headers
                    .into_iter()
                    .map(|(name, value)| (name, Some(value)))
                    .collect()
            });
            Ok(target
                .models
                .complete_simple(&target.model, context, options)
                .await)
        })
    }
}

/// The compactor model as configured: `memory.model`, else
/// `auxiliaryModel` (`provider/model-id`); `None` when it follows the
/// default model. Reads the global settings of `agent_dir`.
#[must_use]
pub fn configured_memory_model(agent_dir: &Path) -> Option<String> {
    let settings = crate::settings::SettingsManager::create(agent_dir, agent_dir);
    explicit_model(&settings)
}

fn explicit_model(settings: &crate::settings::SettingsManager) -> Option<String> {
    settings.get_memory_model().or_else(|| {
        settings
            .get_auxiliary_model()
            .map(str::trim)
            .filter(|model| !model.is_empty())
            .map(str::to_string)
    })
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
    models: eukhe_ai::models::Models,
    model: pi_ai::Model,
    api_key: Option<String>,
    headers: Option<std::collections::BTreeMap<String, String>>,
    thinking: ModelThinkingLevel,
}

fn resolve(agent_dir: &Path) -> anyhow::Result<Target> {
    // The agent dir doubles as the cwd: the compactor serves every
    // project, so no project's settings may steer it.
    let settings = crate::settings::SettingsManager::create(agent_dir, agent_dir);
    let explicit = explicit_model(&settings);
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

#[cfg(test)]
mod tests {
    use std::future::Future;
    use std::time::Duration;

    use eukhe_types::pi_ai::{Message, UserContent, UserMessage};
    use serde_json::{json, Value};
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::net::{TcpListener, TcpStream};

    use super::*;

    /// Fail instead of hanging when a step never comes.
    async fn within<F: Future>(future: F) -> F::Output {
        tokio::time::timeout(Duration::from_secs(30), future)
            .await
            .expect("the step comes")
    }

    /// One HTTP request's JSON body.
    async fn read_body(socket: &mut TcpStream) -> Value {
        let mut request = Vec::new();
        let mut buffer = [0u8; 8192];
        loop {
            let read = socket.read(&mut buffer).await.unwrap();
            assert_ne!(read, 0, "the request ends before its body");
            request.extend_from_slice(&buffer[..read]);
            let Some(end) = request.windows(4).position(|window| window == b"\r\n\r\n") else {
                continue;
            };
            let length = std::str::from_utf8(&request[..end])
                .unwrap()
                .lines()
                .find_map(|line| {
                    let (name, value) = line.split_once(':')?;
                    name.eq_ignore_ascii_case("content-length")
                        .then(|| value.trim().parse::<usize>())
                })
                .expect("a sized body")
                .unwrap();
            let body = end + 4;
            if request.len() >= body + length {
                return serde_json::from_slice(&request[body..body + length]).unwrap();
            }
        }
    }

    /// A compactor call asks for at most [`MAX_TOKENS`], however large the
    /// model's own budget, and dropping it mid-stream closes its request:
    /// the provider streams on a task of its own.
    #[tokio::test]
    async fn a_compactor_call_is_capped_and_closes_its_request_when_dropped() {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();
        let dir = tempfile::tempdir().unwrap();
        let settings = json!({"memory": {"model": "local/m"}});
        std::fs::write(dir.path().join("settings.json"), settings.to_string()).unwrap();
        let models = json!({"providers": {"local": {
            "baseUrl": format!("http://127.0.0.1:{port}/v1"),
            "apiKey": "local-key",
            "api": "openai-completions",
            "models": [{"id": "m", "contextWindow": 262_144, "maxTokens": 131_072}]
        }}});
        std::fs::write(dir.path().join("models.json"), models.to_string()).unwrap();
        let call = tokio::spawn(SettingsSummarizer::new(dir.path().to_path_buf()).complete(
            Context {
                system_prompt: None,
                messages: vec![Message::User(UserMessage {
                    content: UserContent::Text("hi".to_string()),
                    timestamp: 0,
                })],
                tools: None,
            },
        ));
        let (mut socket, _) = within(listener.accept()).await.unwrap();
        let body = within(read_body(&mut socket)).await;
        // The reply starts, then stalls.
        socket
            .write_all(
                concat!(
                    "HTTP/1.1 200 OK\r\ncontent-type: text/event-stream\r\n\r\n",
                    r#"data: {"id":"c","object":"chat.completion.chunk","created":0,"model":"m","#,
                    r#""choices":[{"index":0,"delta":{"content":"li"},"finish_reason":null}]}"#,
                    "\n\n",
                )
                .as_bytes(),
            )
            .await
            .unwrap();
        call.abort();
        let mut rest = [0u8; 1];
        // A reset closes it as well as an end of stream.
        let closed = within(socket.read(&mut rest)).await.unwrap_or(0);
        assert_eq!(
            (body["max_completion_tokens"].clone(), closed),
            (json!(MAX_TOKENS), 0)
        );
    }
}
