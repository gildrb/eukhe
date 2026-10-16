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
//!
//! Every request first takes a background slot of its provider from the
//! same admission authority as the sessions' requests
//! ([`crate::admission`]), so `providerMaxInFlight` bounds the compactor
//! and the sessions together. A background request waits while a session
//! request of its provider runs or waits, and a session request that comes
//! while it runs preempts it: the call stops its request at once and asks
//! again, so it resumes once the provider is free. A preemption is a
//! pause inside one model call, never a failure or an end of the call:
//! the compactor's [`super::CALL_DEADLINE`] bounds each model call, its
//! waits for a slot and its preemptions included, so a call preempted
//! without end fails at the deadline (docs/harness.md H1.5, H2).

use std::path::{Path, PathBuf};

use eukhe_ai::api::simple_options::{DEFAULT_THINKING_BUDGETS, MIN_ANSWER_TOKENS};
use eukhe_ai::models::ModelsSimpleStreamOptions;
use eukhe_ai::types::{SimpleStreamOptions, StreamOptions};
use eukhe_chord::context::AbortController;
use eukhe_types::ai::{Model, ModelThinkingLevel};
use eukhe_types::daemon::AdmissionPriority;
use eukhe_types::pi_ai::{self, Context};
use futures::StreamExt;

use super::compactor::{ResponseStarted, Summarizer, SummarizerFuture};
use crate::admission::{local_admission, AdmissionHandle, AdmissionRequest, QueuedNotice};

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
#[derive(Clone)]
pub struct SettingsSummarizer {
    agent_dir: PathBuf,
    admission: AdmissionHandle,
}

impl SettingsSummarizer {
    /// Resolve against the settings, auth and models of `agent_dir`, and
    /// take every request's slot from `admission` (a daemon's supervisor
    /// registry).
    #[must_use]
    pub fn new(agent_dir: PathBuf, admission: AdmissionHandle) -> SettingsSummarizer {
        SettingsSummarizer {
            agent_dir,
            admission,
        }
    }

    /// [`Self::new`] with this process's in-process authority, under the
    /// limits of `agent_dir`'s global settings as they are at each call:
    /// the compactor of a process without a daemon.
    #[must_use]
    pub fn in_process(agent_dir: PathBuf) -> SettingsSummarizer {
        let settings_dir = agent_dir.clone();
        let admission = local_admission(move || {
            crate::settings::SettingsManager::create(&settings_dir, &settings_dir)
                .get_admission_limits()
        });
        SettingsSummarizer::new(agent_dir, admission)
    }
}

impl Summarizer for SettingsSummarizer {
    fn complete(&self, context: Context, mut started: ResponseStarted) -> SummarizerFuture {
        let agent_dir = self.agent_dir.clone();
        let admission = self.admission.clone();
        Box::pin(async move {
            // Resolution reads settings and auth from disk and may refresh
            // an OAuth token with a blocking request: off the executor.
            let resolve_target = || {
                let agent_dir = agent_dir.clone();
                async move {
                    tokio::task::spawn_blocking(move || resolve(&agent_dir))
                        .await
                        .map_err(|error| {
                            anyhow::anyhow!("compactor model resolution failed: {error}")
                        })?
                }
            };
            let mut target = resolve_target().await?;
            loop {
                let (queued, mut waited) = tokio::sync::oneshot::channel();
                let permit = admission
                    .acquire(AdmissionRequest {
                        provider_id: target.model.provider.clone(),
                        priority: AdmissionPriority::Background,
                        on_queued: QueuedNotice::new(move || {
                            // The receiver lives until the acquire
                            // returned, so the send cannot fail.
                            let _ = queued.send(());
                        }),
                    })
                    .await?;
                if waited.try_recv().is_ok() {
                    // The wait may have outlasted the credentials or the
                    // settings: resolve again, and when the compactor's
                    // provider changed meanwhile, ask that one.
                    let fresh = resolve_target().await?;
                    let moved = fresh.model.provider != target.model.provider;
                    target = fresh;
                    if moved {
                        continue;
                    }
                }
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
                options
                    .options
                    .stream
                    .request
                    .api_key
                    .clone_from(&target.api_key);
                options.options.stream.request.headers = target.headers.as_ref().map(|headers| {
                    headers
                        .iter()
                        .map(|(name, value)| (name.clone(), Some(value.clone())))
                        .collect()
                });
                let stream = target
                    .models
                    .stream_simple(&target.model, context.clone(), options);
                let reply = async {
                    // The response has started at its first event: the
                    // calls waiting for this prefix may go now (§3.3).
                    if stream.events().next().await.is_some() {
                        started.signal();
                    }
                    stream.result().await
                };
                tokio::select! {
                    biased;
                    reply = reply => {
                        return Ok(reply);
                    }
                    () = permit.preempted() => {}
                }
                // Preempted: the slot is gone already; the request stops
                // now, and the call asks for a slot again.
                drop(abort);
                tracing::debug!(
                    target: "chat_memory",
                    provider = %target.model.provider,
                    "a session request preempted a compactor call; it resumes once the provider is free"
                );
            }
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
    use std::fmt::Write as _;
    use std::future::Future;
    use std::sync::Arc;
    use std::time::Duration;

    use eukhe_types::pi_ai::{
        AssistantContentBlock, AssistantMessage, Message, UserContent, UserMessage,
    };
    use futures::future::BoxFuture;
    use futures::FutureExt as _;
    use serde_json::{json, Value};
    use tempfile::TempDir;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::net::{TcpListener, TcpStream};
    use tokio::sync::mpsc;

    use super::*;
    use crate::admission::{
        AdmissionError, AdmissionRegistry, AdmissionSnapshot, LocalAdmission, ModelPermit,
        ProviderAdmission,
    };
    use crate::memory::{chat_dir, Kind, Memory, MemoryStatus, NODE, SETTLE_TIMEOUT};

    /// A reply that starts, then stalls.
    const STALLED: &str = concat!(
        "HTTP/1.1 200 OK\r\ncontent-type: text/event-stream\r\n\r\n",
        r#"data: {"id":"c","object":"chat.completion.chunk","created":0,"model":"m","#,
        r#""choices":[{"index":0,"delta":{"content":"li"},"finish_reason":null}]}"#,
        "\n\n",
    );

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

    /// Answer one request with `content`, then close the connection.
    async fn reply_with(mut socket: TcpStream, content: &str) {
        let mut answer = String::from(
            "HTTP/1.1 200 OK\r\ncontent-type: text/event-stream\r\nconnection: close\r\n\r\n",
        );
        for (delta, finish_reason) in [
            (json!({"role": "assistant", "content": content}), None),
            (json!({}), Some("stop")),
        ] {
            let chunk = json!({
                "id": "c",
                "object": "chat.completion.chunk",
                "created": 0,
                "model": "m",
                "choices": [{"index": 0, "delta": delta, "finish_reason": finish_reason}]
            });
            write!(answer, "data: {chunk}\n\n").unwrap();
        }
        answer.push_str("data: [DONE]\n\n");
        socket.write_all(answer.as_bytes()).await.unwrap();
    }

    /// Whether the client closed `socket` (a reset closes it as well as an
    /// end of stream).
    async fn closed(socket: &mut TcpStream) -> bool {
        let mut rest = [0u8; 1];
        within(socket.read(&mut rest)).await.unwrap_or(0) == 0
    }

    fn context(text: &str) -> Context {
        Context {
            system_prompt: None,
            messages: vec![Message::User(UserMessage {
                content: UserContent::Text(text.to_string()),
                timestamp: 0,
            })],
            tools: None,
        }
    }

    fn text(reply: &AssistantMessage) -> String {
        reply
            .content
            .iter()
            .filter_map(|block| match block {
                AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
            })
            .collect()
    }

    /// The tests' admission authority: a registry of its own (never the
    /// process's shared one) at the agent dir's limits, reporting the class
    /// of every request that has to wait.
    struct Watched {
        inner: LocalAdmission,
        queued: mpsc::UnboundedSender<AdmissionPriority>,
    }

    impl ProviderAdmission for Watched {
        async fn acquire(&self, request: AdmissionRequest) -> Result<ModelPermit, AdmissionError> {
            let AdmissionRequest {
                provider_id,
                priority,
                on_queued,
            } = request;
            let queued = self.queued.clone();
            self.inner
                .acquire(AdmissionRequest {
                    provider_id,
                    priority,
                    on_queued: QueuedNotice::new(move || {
                        on_queued.notify();
                        queued.send(priority).unwrap();
                    }),
                })
                .await
        }
    }

    /// An agent dir whose compactor model `local/m` is served by
    /// `listener`, with `limits` as its `providerMaxInFlight`.
    struct Setup {
        dir: TempDir,
        listener: TcpListener,
        registry: Arc<AdmissionRegistry>,
        admission: AdmissionHandle,
        queued: mpsc::UnboundedReceiver<AdmissionPriority>,
    }

    async fn setup(limits: Value) -> Setup {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();
        let dir = tempfile::tempdir().unwrap();
        let settings = json!({"memory": {"model": "local/m"}, "providerMaxInFlight": limits});
        std::fs::write(dir.path().join("settings.json"), settings.to_string()).unwrap();
        let models = json!({"providers": {"local": {
            "baseUrl": format!("http://127.0.0.1:{port}/v1"),
            "apiKey": "local-key",
            "api": "openai-completions",
            "models": [{"id": "m", "contextWindow": 262_144, "maxTokens": 131_072}]
        }}});
        std::fs::write(dir.path().join("models.json"), models.to_string()).unwrap();
        let registry = Arc::new(AdmissionRegistry::default());
        let settings_dir = dir.path().to_path_buf();
        let inner = LocalAdmission::new(Arc::clone(&registry), move || {
            crate::settings::SettingsManager::create(&settings_dir, &settings_dir)
                .get_admission_limits()
        });
        let (sender, queued) = mpsc::unbounded_channel();
        Setup {
            dir,
            listener,
            registry,
            admission: AdmissionHandle::new(Arc::new(Watched {
                inner,
                queued: sender,
            })),
            queued,
        }
    }

    impl Setup {
        fn summarizer(&self) -> SettingsSummarizer {
            SettingsSummarizer::new(self.dir.path().to_path_buf(), self.admission.clone())
        }

        fn snapshot(&self) -> AdmissionSnapshot {
            self.registry.controller("local").snapshot()
        }

        /// A session's request to the compactor's provider.
        fn interactive(&self) -> BoxFuture<'static, Result<ModelPermit, AdmissionError>> {
            self.admission.acquire(AdmissionRequest {
                provider_id: "local".to_string(),
                priority: AdmissionPriority::Interactive,
                on_queued: QueuedNotice::new(|| {}),
            })
        }

        async fn accept(&self) -> TcpStream {
            within(self.listener.accept()).await.unwrap().0
        }
    }

    /// A compactor call asks for at most [`MAX_TOKENS`], however large the
    /// model's own budget, and dropping it mid-stream closes its request:
    /// the provider streams on a task of its own.
    #[tokio::test]
    async fn a_compactor_call_is_capped_and_closes_its_request_when_dropped() {
        let setup = setup(json!({})).await;
        let call = tokio::spawn(
            setup
                .summarizer()
                .complete(context("hi"), ResponseStarted::default()),
        );
        let mut socket = setup.accept().await;
        let body = within(read_body(&mut socket)).await;
        socket.write_all(STALLED.as_bytes()).await.unwrap();
        call.abort();
        assert_eq!(
            (
                body["max_completion_tokens"].clone(),
                closed(&mut socket).await
            ),
            (json!(MAX_TOKENS), true)
        );
    }

    /// A compactor call signals its response's start at the first streamed
    /// event, while the response still runs: the calls waiting for its
    /// prefix go then, not at its end (§3.3).
    #[tokio::test]
    async fn a_compactor_call_signals_its_response_start_before_it_ends() {
        let setup = setup(json!({})).await;
        let (started, response) = ResponseStarted::channel();
        let call = tokio::spawn(setup.summarizer().complete(context("hi"), started));
        let mut socket = setup.accept().await;
        within(read_body(&mut socket)).await;
        socket.write_all(STALLED.as_bytes()).await.unwrap();
        within(response).await.unwrap();
        assert!(!call.is_finished());
        call.abort();
    }

    /// The compactor's calls take slots of their provider: past
    /// `providerMaxInFlight` the next call waits, and goes out once the
    /// slot frees.
    #[tokio::test]
    async fn compactor_calls_count_against_the_providers_limit() {
        let mut setup = setup(json!({"local": 1})).await;
        let first = tokio::spawn(
            setup
                .summarizer()
                .complete(context("first"), ResponseStarted::default()),
        );
        let mut held = setup.accept().await;
        within(read_body(&mut held)).await;
        let second = tokio::spawn(
            setup
                .summarizer()
                .complete(context("second"), ResponseStarted::default()),
        );
        let waited = within(setup.queued.recv()).await;
        let while_held = setup.snapshot();
        reply_with(held, "one").await;
        let first = text(&within(first).await.unwrap().unwrap());
        let mut next = setup.accept().await;
        let body = within(read_body(&mut next)).await;
        reply_with(next, "two").await;
        let second = text(&within(second).await.unwrap().unwrap());
        assert_eq!(
            (
                waited,
                while_held,
                body["messages"].to_string().contains("second"),
                first,
                second,
                setup.snapshot()
            ),
            (
                Some(AdmissionPriority::Background),
                AdmissionSnapshot {
                    background_active: 1,
                    background_waiting: 1,
                    ..AdmissionSnapshot::default()
                },
                true,
                "one".to_string(),
                "two".to_string(),
                AdmissionSnapshot::default()
            )
        );
    }

    /// A session request that comes while the compactor's call holds the
    /// provider's only slot is admitted at once, and the call's request
    /// stops; the call waits while the session's request runs, then goes
    /// out again and builds its node: a preemption is no failure.
    #[tokio::test]
    async fn a_session_request_preempts_a_compactor_call_which_resumes_after_it() {
        let mut setup = setup(json!({"local": 1})).await;
        let memory = Memory::open(chat_dir(setup.dir.path()), Arc::new(setup.summarizer()))
            .await
            .unwrap();
        memory.append(Kind::Echo, &"y".repeat(NODE)).await.unwrap();
        let mut preempted = setup.accept().await;
        within(read_body(&mut preempted)).await;
        preempted.write_all(STALLED.as_bytes()).await.unwrap();
        let session = setup
            .interactive()
            .now_or_never()
            .expect("admitted at once")
            .expect("a slot");
        let stopped = closed(&mut preempted).await;
        let waited = within(setup.queued.recv()).await;
        let while_session_runs = setup.snapshot();
        drop(session);
        let mut resumed = setup.accept().await;
        within(read_body(&mut resumed)).await;
        reply_with(resumed, "echo: many y").await;
        assert_eq!(
            (
                stopped,
                waited,
                while_session_runs,
                within(memory.settled_render(SETTLE_TIMEOUT))
                    .await
                    .unwrap()
                    .text,
                memory.status().await.unwrap()
            ),
            (
                true,
                Some(AdmissionPriority::Background),
                AdmissionSnapshot {
                    active: 1,
                    background_waiting: 1,
                    ..AdmissionSnapshot::default()
                },
                "<chat>\n0+1|echo: many y\n</chat>".to_string(),
                MemoryStatus {
                    messages: 1,
                    nodes: 1,
                    view_lines: 1,
                    view_bytes: "echo: many y".len() as u64,
                    unsummarized: 0,
                    running: 0,
                    last_error: None,
                }
            )
        );
    }
}
