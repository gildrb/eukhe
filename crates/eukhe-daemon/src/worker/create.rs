//! Session creation on the worker: the `create` command opens (or reopens)
//! the durable session storage, takes its lease, starts the event bridge
//! on the main conversation, and records the revival evidence. Reopening a
//! storage whose run was interrupted resumes that run (`open_session`
//! calls `resume()`): no prompt replay, no queue snapshot.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_core::durable::{
    ModelRequest, ParentLink, SessionConfig, SessionRole, SessionStorage, TurnWait,
};
use eukhe_durable::harness::types::{AgentChange, FieldChange};
use eukhe_types::pi_ai::ModelThinkingLevel;
use serde_json::{json, Value};

use super::durable_host::{self, meta, HostRequest, HostedSession};
use super::{emit_worker_event_with, paths, response_failure, response_success, Worker};
use crate::protocol::DaemonResponse;

/// The parsed `create` command.
pub(crate) struct CreateParams {
    pub(crate) session_path: Option<PathBuf>,
    pub(crate) no_session: bool,
    pub(crate) name: Option<String>,
    pub(crate) model: Option<ModelRequest>,
    pub(crate) thinking: Option<ModelThinkingLevel>,
    pub(crate) cwd: String,
    pub(crate) session_dir: PathBuf,
    /// A caller-chosen session id (RLM children derive it from their
    /// durable task id, so a rerun reopens the same child storage).
    pub(crate) session_id: Option<String>,
    pub(crate) rlm_depth: Option<u32>,
    pub(crate) rlm_max_depth: Option<u32>,
    pub(crate) rlm_child_id: Option<String>,
    pub(crate) parent_active_session_id: Option<String>,
    pub(crate) parent_session_id: Option<String>,
    pub(crate) child_script: Option<String>,
    pub(crate) model_patterns: Option<Vec<String>>,
    /// The create payload's `executionMode` (the telemetry execution mode
    /// the client stamps, TS main.ts `executionMode: appMode`); absent
    /// (an agent-spawned session) stays `None` (reported as `unknown`).
    pub(crate) execution_mode: Option<String>,
    /// The parent's in-flight model request the spawn anchored to (TS
    /// `spawnedByRequestId`, in the create config): reaches the child's
    /// semantic-edge ledger registration.
    pub(crate) spawned_by_request_id: Option<String>,
}

impl CreateParams {
    /// Parse a `create` payload.
    ///
    /// # Errors
    ///
    /// The wire message of an invalid field.
    pub(crate) fn parse(payload: &Value, agent_dir: &Path) -> Result<Self, String> {
        let expand = |path: &str| paths::expand_tilde(path).map_err(|error| error.to_string());
        let session_path = payload
            .get("sessionPath")
            .and_then(Value::as_str)
            .map(expand)
            .transpose()?;
        let no_session = payload
            .get("noSession")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        if session_path.is_some() && no_session {
            return Err("Session cannot be both no-session and session-pathed".to_string());
        }
        let thinking = match payload.get("thinking") {
            None | Some(Value::Null) => None,
            Some(Value::String(level)) => Some(ModelThinkingLevel::parse(level).ok_or_else(|| {
                format!("Invalid thinking level \"{level}\". Valid values: off, minimal, low, medium, high, xhigh, max")
            })?),
            Some(_) => return Err("Invalid thinking level: expected a string".to_string()),
        };
        let model = payload
            .get("model")
            .and_then(Value::as_str)
            .map(|pattern| ModelRequest {
                provider: payload
                    .get("provider")
                    .and_then(Value::as_str)
                    .map(str::to_string),
                pattern: pattern.to_string(),
            });
        let session_dir = match payload.get("sessionDir").and_then(Value::as_str) {
            Some(dir) => expand(dir)?,
            None => paths::sessions_dir(agent_dir).map_err(|error| error.to_string())?,
        };
        let (rlm_depth, rlm_max_depth) = create_payload_rlm_depth(payload)?;
        let metadata = payload
            .get("runtimeMetadata")
            .filter(|metadata| metadata.get("kind").and_then(Value::as_str) == Some("subagent"));
        let text = |value: Option<&Value>, key: &str| {
            value
                .and_then(|value| value.get(key))
                .and_then(Value::as_str)
                .map(str::to_string)
        };
        Ok(Self {
            session_path,
            no_session,
            name: text(Some(payload), "name").filter(|name| !name.trim().is_empty()),
            model,
            thinking,
            cwd: text(Some(payload), "cwd").unwrap_or_else(|| "/".to_string()),
            session_dir,
            session_id: text(Some(payload), "sessionId").filter(|id| !id.is_empty()),
            rlm_depth,
            rlm_max_depth,
            rlm_child_id: text(metadata, "rlmChildId"),
            parent_active_session_id: text(metadata, "parentActiveSessionId"),
            parent_session_id: text(metadata, "parentSessionId"),
            child_script: text(Some(payload), "childScript"),
            model_patterns: payload
                .get("models")
                .and_then(Value::as_array)
                .map(|patterns| {
                    patterns
                        .iter()
                        .filter_map(Value::as_str)
                        .map(str::to_string)
                        .collect()
                }),
            execution_mode: text(Some(payload), "executionMode")
                .filter(|mode| !mode.trim().is_empty()),
            spawned_by_request_id: text(Some(payload), "spawnedByRequestId"),
        })
    }

    /// The session id and storage this create opens.
    fn storage(&self) -> (String, SessionStorage) {
        if self.no_session {
            let id = self.session_id.clone().unwrap_or_else(new_session_id);
            return (id, SessionStorage::Memory);
        }
        let (session_id, dir) = if let Some(path) = &self.session_path {
            durable_host::storage_for_path(path)
        } else {
            let id = self.session_id.clone().unwrap_or_else(new_session_id);
            let dir = self.session_dir.join(&id);
            (id, dir)
        };
        (session_id, SessionStorage::Jsonl { dir, fsync: true })
    }

    /// Whether this create reopens an existing session storage.
    fn reopens(&self) -> bool {
        match (&self.session_path, &self.session_id) {
            (Some(path), _) => durable_host::session_exists(path),
            (None, Some(id)) => !self.no_session && self.session_dir.join(id).is_dir(),
            (None, None) => false,
        }
    }
}

/// A fresh session id (`UUIDv7`, like every eukhe session).
fn new_session_id() -> String {
    uuid::Uuid::now_v7().to_string()
}

impl Worker {
    pub(super) async fn handle_create(&self, payload: &Value) -> DaemonResponse {
        // One create in flight at a time: a concurrent create joins this
        // open and answers with the created summary.
        let _create_gate = self.create_gate.lock().await;
        let existing_summary = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            core.created.then(|| self.summary_locked(&core))
        };
        if let Some(summary) = existing_summary {
            // Idempotent re-create after a supervisor restart or respawn.
            self.rebind_herdr_reporter(payload);
            return response_success(
                None,
                "create",
                Some(serde_json::to_value(&summary).unwrap_or(Value::Null)),
            );
        }
        let params = match CreateParams::parse(payload, &self.config.agent_dir) {
            Ok(params) => params,
            Err(error) => return response_failure(None, "create", &error, None),
        };
        let cx = BACKGROUND_CONTEXT.clone();
        let hosted = match self.open_hosted(&params, &cx).await {
            Ok(hosted) => hosted,
            Err(response) => return *response,
        };
        if let Err(response) = self.install_hosted(hosted, &params, &cx).await {
            return *response;
        }
        self.rebind_herdr_reporter(payload);
        self.bind_scheduled_jobs().await;
        let (summary, busy) = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            (self.summary_locked(&core), core.is_busy())
        };
        // The revival evidence: a resumed run is live work again.
        let _ = self.record_recovery(busy, "create");
        if let Some(registration) = &self.registration {
            registration.notify_session_created(summary.session_id.clone());
        }
        self.poke_context_tree_refresh();
        // TS session boot resolves the initial model through
        // `refreshAvailableModels`, which also fetches the live Prime
        // Inference catalog in the background and caches it on disk. Fire
        // the same refresh here: the effect is the cache file (fresh
        // registries read it), and failures fall back to the cached or
        // bundled catalog without touching the session.
        let agent_dir = self.config.agent_dir.clone();
        tokio::spawn(async move {
            let auth = eukhe_core::auth::AuthStorage::create(&agent_dir);
            let mut registry =
                eukhe_core::models::ModelRegistry::create(auth, agent_dir.join("models.json"));
            let _ = registry.refresh_available_models().await;
        });
        let mut data = serde_json::to_value(&summary).unwrap_or(Value::Null);
        // The durable compaction resumes with the session itself, so a
        // supervisor-declared interrupted compaction needs no disclosure
        // row: the record is consumed.
        if payload.get("interruptedCompaction").is_some() {
            data["interruptedCompactionPersisted"] = json!(true);
        }
        response_success(None, "create", Some(data))
    }

    /// The eukhe session config for `params` (cwd, id, storage, role,
    /// model, thinking, chat memory, turn-wait sink).
    pub(crate) async fn session_config(
        &self,
        params: &CreateParams,
        session_id: String,
        storage: SessionStorage,
    ) -> anyhow::Result<SessionConfig> {
        let mut config = SessionConfig::new(
            self.config.agent_dir.clone(),
            PathBuf::from(&params.cwd),
            session_id,
            storage,
        );
        config.role = SessionRole {
            rlm_depth: params.rlm_depth.unwrap_or(0),
            rlm_max_depth: params
                .rlm_max_depth
                .unwrap_or(crate::rlm_children::DEFAULT_RLM_MAX_DEPTH),
            parent: params
                .parent_session_id
                .clone()
                .map(|session_id| ParentLink {
                    session_id,
                    task_id: None,
                    agent_name: None,
                    spawned_by_request_id: params.spawned_by_request_id.clone(),
                }),
        };
        config.model.clone_from(&params.model);
        config.thinking = params.thinking;
        config.children = self.rlm_subagent_host(crate::rlm_children::ParentIdentity {
            rlm_depth: config.role.rlm_depth,
            rlm_max_depth: config.role.rlm_max_depth,
            model: None,
            cwd: Some(params.cwd.clone()),
            session_id: Some(config.session_id.clone()),
            session_file: None,
            thinking: params.thinking.map(|level| level.as_str().to_owned()),
            child_script: params.child_script.clone(),
        });
        let scripted = self.config.script.is_some();
        if !scripted && config.role.is_root() {
            config.memory = Some(self.chat_memory().await?);
        }
        let core = Arc::clone(&self.core);
        let events = Arc::clone(&self.events);
        let summary_core = Arc::clone(&self.core);
        let summary_events = Arc::clone(&self.events);
        config.turn_wait = Some(Arc::new(move |wait| {
            emit_worker_event_with(
                &core,
                &events,
                json!(eukhe_types::daemon::ChatTurnWaitEvent {
                    waiting: matches!(wait, TurnWait::Waiting),
                }),
            );
        }));
        // The live compaction summary block (the old engine's
        // `set_compaction_summary_sink`): every summarizer text delta,
        // then the file-operations flush, straight onto the wire between
        // the run's `compaction_start` and `compaction_end`.
        config.summary_delta = Some(Arc::new(move |delta: &str| {
            emit_worker_event_with(
                &summary_core,
                &summary_events,
                json!({ "type": "compaction_summary_delta", "delta": delta }),
            );
        }));
        // The kernel host seams: scheduled-jobs cron wiring, bash notices.
        self.wire_session_host(&mut config);
        Ok(config)
    }

    /// The chat memory every root session of this worker shares (opened once).
    async fn chat_memory(&self) -> anyhow::Result<eukhe_core::memory::Memory> {
        let agent_dir = self.config.agent_dir.clone();
        self.chat_memory
            .get_or_try_init(|| {
                eukhe_core::memory::Memory::open(
                    eukhe_core::memory::chat_dir(&agent_dir),
                    Arc::new(eukhe_core::memory::SettingsSummarizer::new(
                        agent_dir.clone(),
                    )),
                )
            })
            .await
            .cloned()
    }

    /// Open the session `params` names: lease, legacy import, Harness open,
    /// `resume()`. An explicit model/thinking flag on an existing session
    /// reconfigures its main conversation.
    ///
    /// # Errors
    ///
    /// The create failure response (held lease, open failure).
    pub(crate) async fn open_hosted(
        &self,
        params: &CreateParams,
        cx: &Context,
    ) -> Result<Arc<HostedSession>, Box<DaemonResponse>> {
        let fail = |message: String| Box::new(response_failure(None, "create", &message, None));
        let (session_id, storage) = params.storage();
        let existed = params.reopens();
        let config = self
            .session_config(params, session_id, storage)
            .await
            .map_err(|error| fail(format!("{error:#}")))?;
        let request = HostRequest {
            config,
            script: self.config.script.clone(),
            telemetry_disabled: self.config.telemetry_disabled,
            execution_mode: params.execution_mode.clone(),
        };
        let hosted = match HostedSession::open(request, &self.config.agent_dir, cx).await {
            Ok(hosted) => Arc::new(hosted),
            Err(durable_host::HostError::Lease(error)) => {
                return Err(Box::new(crate::hold_refusal::create_failure_response(
                    &error,
                )));
            }
            Err(error) => return Err(fail(error.to_string())),
        };
        if existed && (params.model.is_some() || params.thinking.is_some()) {
            if let Err(error) = reconfigure_main(&hosted, params, cx).await {
                let _ = hosted.close(cx).await;
                return Err(fail(error.to_string()));
            }
        }
        Ok(hosted)
    }

    /// Make `hosted` the worker's session: the core identity, the session
    /// metadata, and the event bridge on its main conversation.
    ///
    /// # Errors
    ///
    /// The create failure response (metadata or event stream unreadable);
    /// the session is closed again.
    pub(crate) async fn install_hosted(
        &self,
        hosted: Arc<HostedSession>,
        params: &CreateParams,
        cx: &Context,
    ) -> Result<(), Box<DaemonResponse>> {
        let fail = |message: String| Box::new(response_failure(None, "create", &message, None));
        let installed = async {
            if let Some(name) = &params.name {
                meta::set_session_name(hosted.harness(), Some(name.trim().to_string()), cx).await?;
            }
            let session_meta = meta::read_session_meta(hosted.harness(), cx).await?;
            let main = hosted.main()?;
            // The withdrawn inputs survive the restart: the durable
            // store seeds the caches (resume, clear, and mutations read
            // them from here).
            let withdrawn =
                durable_host::suspended::read_suspended(hosted.harness(), main.id(), cx).await?;
            {
                let mut core = self
                    .core
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                core.session_id = hosted.session_id().to_string();
                core.session_dir = hosted.storage_dir().map(Path::to_path_buf);
                core.session_name = session_meta.name;
                core.anthropic_warning_shown = session_meta.anthropic_warning_shown;
                core.created_at = Some(crate::util::iso_from_unix_ms(crate::util::now_ms()));
                core.cwd.clone_from(&params.cwd);
                core.rlm_depth = params.rlm_depth.unwrap_or(0);
                core.runtime_kind = if params.rlm_child_id.is_some() {
                    "subagent".to_string()
                } else {
                    "top-level".to_string()
                };
                core.rlm_child_id.clone_from(&params.rlm_child_id);
                core.parent_active_session_id
                    .clone_from(&params.parent_active_session_id);
                core.parent_session_id.clone_from(&params.parent_session_id);
                core.child_script.clone_from(&params.child_script);
                core.scoped_models = self.resolve_scoped_models(params);
                let settings = eukhe_core::settings::SettingsManager::create(
                    &params.cwd,
                    &self.config.agent_dir,
                );
                let tier = Some(settings.get_default_service_tier());
                core.service_tier = tier;
                core.active_service_tier = tier;
                core.suspended = withdrawn
                    .suspended
                    .iter()
                    .map(durable_host::suspended::WithdrawnInput::queued)
                    .collect();
                core.held = withdrawn
                    .held
                    .iter()
                    .map(durable_host::suspended::WithdrawnInput::queued)
                    .collect();
                core.last_activity_ms = crate::util::now_ms();
            }
            self.show_conversation(&hosted, &main).await
        }
        .await;
        if let Err(error) = installed {
            let _ = hosted.close(cx).await;
            return Err(fail(error.to_string()));
        }
        if let Some(previous) = self.session.replace(hosted) {
            if let Err(error) = previous.close(cx).await {
                eprintln!("eukhe-daemon worker: closing the replaced session failed: {error}");
            }
        }
        let mut core = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        core.created = true;
        core.shutdown_requested = false;
        // A fresh session parks immediately: the idle-passivation loop
        // arms from here.
        self.park_notify.notify_one();
        Ok(())
    }

    /// The `models` patterns (else settings `enabledModels`) resolved into
    /// the session's scoped list `{ model, thinkingLevel? }`.
    fn resolve_scoped_models(&self, params: &CreateParams) -> Vec<Value> {
        let patterns = params.model_patterns.clone().unwrap_or_else(|| {
            eukhe_core::settings::SettingsManager::create(&params.cwd, &self.config.agent_dir)
                .get_enabled_models()
                .unwrap_or_default()
        });
        if patterns.is_empty() {
            return Vec::new();
        }
        let registry = crate::state_getters::worker_model_registry(&self.config.agent_dir);
        let available: Vec<eukhe_types::ai::Model> =
            registry.get_available().into_iter().cloned().collect();
        eukhe_core::models::resolve_model_scope_from_models(&patterns, &available)
            .iter()
            .map(|scoped| {
                let mut entry = json!({ "model": scoped.model });
                if let Some(level) = scoped.thinking_level {
                    entry["thinkingLevel"] = json!(level);
                }
                entry
            })
            .collect()
    }

    /// (Re)bind the pane reporter from the create payload's client env.
    pub(super) fn rebind_herdr_reporter(&self, payload: &Value) {
        let client_env: std::collections::BTreeMap<String, String> = payload
            .get("env")
            .cloned()
            .and_then(|env| serde_json::from_value(env).ok())
            .map(|env| crate::herdr::filter_client_env(&env))
            .unwrap_or_default();
        // A live RLM child shares the parent's pane: it never reports.
        let spawned_as_child = payload
            .get("rlmDepth")
            .and_then(Value::as_u64)
            .is_some_and(|depth| depth > 0);
        let (active, session_ref) = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            (core.is_busy(), Worker::herdr_session_ref(&core))
        };
        let mut slot = self
            .herdr
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let reporter = match crate::herdr::HerdrConfig::from_env(&client_env) {
            Some(config) if !spawned_as_child => {
                let generation = self
                    .herdr_generation
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                    + 1;
                crate::herdr::HerdrReporter::start(
                    config,
                    session_ref.clone(),
                    generation,
                    Arc::clone(&self.herdr_generation),
                )
            }
            // A re-create without a pane identity keeps the existing binding.
            None if !spawned_as_child && slot.enabled() => return,
            _ => crate::herdr::HerdrReporter::default(),
        };
        reporter.session_started(active, session_ref);
        *slot = reporter;
    }
}

/// Apply an explicit create model/thinking to an existing session's main
/// conversation (a new root takes them at creation).
async fn reconfigure_main(
    hosted: &HostedSession,
    params: &CreateParams,
    cx: &Context,
) -> anyhow::Result<()> {
    let main = hosted.main()?;
    let mut change = AgentChange::default();
    if let Some(request) = &params.model {
        let settings = hosted.deps().settings.manager();
        let resolved = eukhe_core::durable::resolve_session_model(
            &hosted.deps().models,
            &settings,
            Some(request),
            params.thinking,
            cx,
        )
        .await?
        .ok_or_else(|| anyhow::anyhow!("Model \"{}\" not found", request.pattern))?;
        change.model = FieldChange::Set(resolved.model);
        change.thinking_level = FieldChange::Set(params.thinking.unwrap_or(resolved.thinking));
    } else if let Some(thinking) = params.thinking {
        change.thinking_level = FieldChange::Set(thinking);
    }
    main.configure(change, cx).await?;
    Ok(())
}

pub(super) fn active_session_id_of(payload: &[u8]) -> String {
    serde_json::from_slice::<Value>(payload)
        .ok()
        .and_then(|value| {
            value
                .get("activeSessionId")
                .and_then(Value::as_str)
                .map(str::to_string)
        })
        .unwrap_or_default()
}

pub(super) fn worker_server_capabilities(agent_dir: &std::path::Path) -> Vec<String> {
    // The factory lane advertises only while its opt-in gate reads enabled.
    crate::factory_activity::advertised_server_capabilities(agent_dir)
}

/// RLM depth fields of a create payload: `(depth, max_depth)`. Values must
/// be non-negative integers that fit a u32.
fn create_payload_rlm_depth(payload: &Value) -> Result<(Option<u32>, Option<u32>), String> {
    fn parse(payload: &Value, key: &str) -> Result<Option<u32>, String> {
        match payload.get(key) {
            None | Some(Value::Null) => Ok(None),
            Some(value) => value
                .as_u64()
                .and_then(|value| u32::try_from(value).ok())
                .map(Some)
                .ok_or_else(|| format!("create {key} must be a non-negative integer")),
        }
    }
    let depth = parse(payload, "rlmDepth")?;
    let max_depth = parse(payload, "rlmMaxDepth")?;
    Ok((depth, max_depth))
}
