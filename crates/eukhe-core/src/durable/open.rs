//! Opening an eukhe session: storage (with the one-time legacy import),
//! settings, models, resources, the extension registry, and the Harness
//! with its root conversation.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_durable::env::{NativeExecutionEnv, NativeExecutionEnvOptions};
use eukhe_durable::errors::StorageError;
use eukhe_durable::harness::registry::Registry;
use eukhe_durable::harness::types::{AgentChange, FieldChange, HarnessOptions, ReportFn};
use eukhe_durable::harness::{Conversation, Harness, RootOptions};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::storage::jsonl::{JsonlStorage, JsonlStorageOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{Storage, ROOT_CONVERSATION_ID};

use super::deps::{
    HostDeps, OpenedSession, ResolvedServices, ServiceStop, SessionConfig, SessionStorage,
};
use super::env::env_factory;
use super::import::{import_legacy_session, ImportError};
use super::main_conversation::{main_conversation, set_main_conversation};
use super::models::provider::ProviderRuntime;
use super::models::{create_models, resolve_session_model, ModelsError};
use super::observe;
use super::observe::semantic_edges::{wrap_stream_fn, wrap_stream_simple_fn, SemanticEdgeRecorder};
use super::registry::create_eukhe_registry;
use super::settings::EukheSettings;
use crate::resources::{load_resources, LoadedResources, ResourceLoaderOptions};
use crate::session_engine::runtime_wiring::kernel_python_skills;
use crate::settings::SettingsManager;

/// Why a session could not open.
#[derive(Debug, thiserror::Error)]
pub enum OpenError {
    #[error("failed to import legacy session {}: {source}", path.display())]
    Import {
        path: PathBuf,
        #[source]
        source: ImportError,
    },
    #[error("failed to open session storage {}: {source}", dir.display())]
    Storage {
        dir: PathBuf,
        #[source]
        source: StorageError,
    },
    #[error("failed to load session resources: {0:#}")]
    Resources(anyhow::Error),
    #[error(transparent)]
    Models(#[from] ModelsError),
    #[error(transparent)]
    Harness(#[from] SessionError),
}

/// An open eukhe session: the durable Harness with eukhe's extensions
/// installed, its root conversation, and its main conversation. Dropping it
/// without [`EukheSession::close`] leaves the storage to the next open (a
/// crash).
pub struct EukheSession {
    harness: Harness,
    root: Conversation,
    main: Mutex<Conversation>,
    registry: Registry,
    deps: Arc<HostDeps>,
    stops: Mutex<Vec<ServiceStop>>,
}

impl EukheSession {
    #[must_use]
    pub fn harness(&self) -> &Harness {
        &self.harness
    }

    /// The session's root conversation (where the session started).
    #[must_use]
    pub fn root(&self) -> &Conversation {
        &self.root
    }

    /// The session's main conversation (`eukhe.session.main`, else the
    /// root), as of open or the last [`EukheSession::set_main`] /
    /// [`EukheSession::reload_main`].
    #[must_use]
    pub fn main(&self) -> Conversation {
        self.main
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    /// Make `conversation` the main conversation (one commit).
    ///
    /// # Errors
    ///
    /// The commit fails.
    pub async fn set_main(&self, conversation: &Conversation, cx: &Context) -> SessionResult<()> {
        let id = conversation.id();
        self.harness
            .commit(
                move |tx| async move { set_main_conversation(&tx, id).await },
                cx,
            )
            .await?;
        *self.main.lock().unwrap_or_else(PoisonError::into_inner) = conversation.clone();
        Ok(())
    }

    /// Re-read the main conversation after a commit that called
    /// [`set_main_conversation`] (a fork or tree navigation).
    ///
    /// # Errors
    ///
    /// The document cannot be read or names a missing conversation.
    pub async fn reload_main(&self, cx: &Context) -> SessionResult<Conversation> {
        let main = main_conversation(&self.harness, cx).await?;
        *self.main.lock().unwrap_or_else(PoisonError::into_inner) = main.clone();
        Ok(main)
    }

    #[must_use]
    pub fn registry(&self) -> &Registry {
        &self.registry
    }

    #[must_use]
    pub fn deps(&self) -> &Arc<HostDeps> {
        &self.deps
    }

    /// Stop the session's services (reverse start order), then close the
    /// Harness after its running tasks settle. Idempotent: a later call
    /// stops nothing and awaits the same Harness close.
    ///
    /// # Errors
    ///
    /// The Harness close failure.
    pub async fn close(&self, cx: &Context) -> SessionResult<()> {
        let stops = std::mem::take(&mut *self.stops.lock().unwrap_or_else(PoisonError::into_inner));
        for stop in stops.into_iter().rev() {
            stop().await;
        }
        self.deps.harness.clear();
        self.harness.close(cx).await
    }
}

impl Drop for EukheSession {
    fn drop(&mut self) {
        // Extensions hold the deps; the cell must not keep the Harness alive.
        self.deps.harness.clear();
    }
}

/// Open (or create) an eukhe session and resume its scheduled work.
///
/// A JSONL session whose storage directory is missing but whose legacy
/// `<sessions_dir>/<session_id>.jsonl` exists is imported first.
///
/// # Errors
///
/// The legacy import, storage, resource loading, model resolution, or
/// Harness open fails.
pub async fn open_session(config: SessionConfig, cx: &Context) -> Result<EukheSession, OpenError> {
    let (storage, storage_dir) = open_storage(&config, cx).await?;
    let settings = Arc::new(EukheSettings::new(&config.cwd, &config.agent_dir));
    let manager = settings.manager();
    let models = match &config.models {
        Some(models) => models.clone(),
        None => create_models(&config.agent_dir, cx).await?,
    };
    // The session's semantic-edge recorder (the ACP request-id ledger):
    // a durable storage keeps its ledger beside the session (a spawned
    // child's dir is its RLM session dir), a memory storage keeps the
    // recorder in memory-only mode (ids still mint and ride the wire).
    let parent = config.role.parent.clone();
    let ledger_home = storage_dir.clone();
    let semantic_edges = Arc::new(observe::semantic_edges::SemanticEdgeRecorder::open(
        observe::semantic_edges::SemanticEdgeIdentity {
            session_id: config.session_id.clone(),
            ledger_path: observe::semantic_edges::semantic_edge_ledger_path(
                parent.as_ref().and(ledger_home.as_deref()),
                ledger_home.as_deref(),
            ),
            parent_session_id: parent.as_ref().map(|parent| parent.session_id.clone()),
            spawned_by_request_id: parent
                .as_ref()
                .and_then(|parent| parent.spawned_by_request_id.clone()),
        },
    ));
    let loaded = load_session_resources(&config, &manager).await?;
    let deps = Arc::new(HostDeps::new(
        &config,
        ResolvedServices {
            storage_dir,
            settings: Arc::clone(&settings),
            models: models.clone(),
            resources: Arc::new(loaded.resources),
            generic_mcp_servers: loaded.generic_mcp_servers,
            mcp: loaded.mcp,
            python_skills: loaded.python_skills,
            semantic_edges: Arc::clone(&semantic_edges),
        },
    ));
    // The session's own model collection gets the eukhe provider behaviors
    // (failover, quota park, image routing, request timing); a shared
    // collection (the daemon's faux scripts) stays unwrapped.
    if config.models.is_none() {
        // The runtime registers itself on the deps; the handle it returns
        // is for callers that need it before the deps are reachable.
        let _ = ProviderRuntime::install(&models, &deps);
        // The semantic-edge wrapper rides OUTERMOST (over the provider
        // runtime's timing fn, the old engine's wrap order): every model
        // request mints its id, sends it on the wire headers, and settles
        // on the ledger.
        wrap_models_with_semantic_edges(&models, &semantic_edges);
    }
    let registry = create_eukhe_registry(&deps)?;

    let session_id = config.session_id.clone();
    let on_report: ReportFn = Arc::new(move |error: SessionError| {
        tracing::warn!(session_id = %session_id, error = %error, "durable harness report");
    });
    let mut options = HarnessOptions::new(models.clone(), Arc::new(registry.clone()));
    options.settings = Some(settings);
    options.env = Some(env_factory(&config.cwd));
    options.now.clone_from(&config.now);
    options.on_report = Some(on_report);
    let harness = Harness::open(storage, options, cx).await?;

    let opened = async {
        let root = open_root(&harness, &config, &models, &manager, cx).await?;
        let main = main_conversation(&harness, cx).await?;
        Ok::<_, OpenError>((root, main))
    };
    let (root, main) = match opened.await {
        Ok(opened) => opened,
        Err(error) => {
            close_after_failure(&harness, cx).await;
            return Err(error);
        }
    };
    deps.harness.set(harness.clone(), root.clone());
    let session = EukheSession {
        harness: harness.clone(),
        root: root.clone(),
        main: Mutex::new(main),
        registry,
        deps: Arc::clone(&deps),
        stops: Mutex::new(Vec::new()),
    };
    for start in deps.take_services() {
        let started = start(OpenedSession {
            harness: harness.clone(),
            root: root.clone(),
            deps: Arc::clone(&deps),
        })
        .await;
        match started {
            Ok(Some(stop)) => session
                .stops
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(stop),
            Ok(None) => {}
            Err(error) => {
                if let Err(close_error) = session.close(cx).await {
                    tracing::warn!(error = %close_error, "closing a session that failed to start");
                }
                return Err(error.into());
            }
        }
    }
    if let Err(error) = harness.resume() {
        if let Err(close_error) = session.close(cx).await {
            tracing::warn!(error = %close_error, "closing a session that failed to resume");
        }
        return Err(error.into());
    }
    Ok(session)
}

/// Wrap every provider's stream functions with the session's
/// semantic-edge recorder (TS `wrapStreamFnWithSemanticEdges`, outermost
/// over the provider runtime's wrappers): each provider row is re-wrapped
/// in place.
fn wrap_models_with_semantic_edges(
    models: &eukhe_pi_ai::models::Models,
    recorder: &Arc<SemanticEdgeRecorder>,
) {
    for provider in models.get_providers() {
        let mut provider = (*provider).clone();
        provider.stream = wrap_stream_fn(Arc::clone(recorder), provider.stream);
        provider.stream_simple =
            wrap_stream_simple_fn(Arc::clone(recorder), provider.stream_simple);
        models.set_provider(provider);
    }
}

async fn open_storage(
    config: &SessionConfig,
    cx: &Context,
) -> Result<(Arc<dyn Storage>, Option<PathBuf>), OpenError> {
    match &config.storage {
        SessionStorage::Memory => Ok((Arc::new(MemoryStorage::new()), None)),
        SessionStorage::Jsonl { dir, fsync } => {
            if let Some(legacy) = legacy_session_file(dir, &config.session_id) {
                let report = import_legacy_session(&legacy, dir, cx)
                    .await
                    .map_err(|source| OpenError::Import {
                        path: legacy.clone(),
                        source,
                    })?;
                tracing::info!(
                    legacy = %legacy.display(),
                    entries = report.entries,
                    skipped_rows = report.skipped_rows,
                    "imported legacy session"
                );
            }
            let fs = Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
                cwd: config.cwd.to_string_lossy().into_owned(),
                ..NativeExecutionEnvOptions::default()
            }));
            let storage = JsonlStorage::open(
                &dir.to_string_lossy(),
                fs,
                cx,
                JsonlStorageOptions { fsync: *fsync },
            )
            .await
            .map_err(|source| OpenError::Storage {
                dir: dir.clone(),
                source,
            })?;
            Ok((Arc::new(storage), Some(dir.clone())))
        }
    }
}

/// The legacy `<sessions_dir>/<id>.jsonl` to import into the missing `dir`.
fn legacy_session_file(dir: &Path, session_id: &str) -> Option<PathBuf> {
    if dir.exists() {
        return None;
    }
    let legacy = dir.parent()?.join(format!("{session_id}.jsonl"));
    legacy.is_file().then_some(legacy)
}

struct SessionResources {
    resources: LoadedResources,
    generic_mcp_servers: Vec<String>,
    mcp: Arc<Mutex<crate::mcp::McpManager>>,
    python_skills: Vec<crate::kernel::KernelPythonSkill>,
}

/// Skills, context files, `SYSTEM.md`, and MCP gating, loaded as the old
/// engine's `create_session` loads them.
async fn load_session_resources(
    config: &SessionConfig,
    manager: &SettingsManager,
) -> Result<SessionResources, OpenError> {
    let user_servers = manager
        .settings()
        .mcp_servers
        .clone()
        .unwrap_or_default()
        .into_iter()
        .filter_map(|(server, value)| {
            serde_json::from_value(value)
                .ok()
                .map(|parsed| (server, parsed))
        })
        .collect::<std::collections::HashMap<String, crate::mcp::McpServerConfig>>();
    let trust = manager.project_trust().clone();
    let cwd = config.cwd.clone();
    let agent_dir = config.agent_dir.clone();
    let prompt = config.prompt.clone();
    let shared_mcp = config.mcp.clone();
    tokio::task::spawn_blocking(move || {
        let (skill_overrides, persistent_servers, built_mcp) =
            crate::mcp::McpManager::prompt_gating(user_servers, &agent_dir);
        let mut extra_builtin_skill_overrides = prompt.extra_builtin_skill_overrides.clone();
        extra_builtin_skill_overrides.extend(skill_overrides);
        let mut generic_mcp_servers = prompt.generic_mcp_servers.clone();
        for server in persistent_servers {
            if !generic_mcp_servers.contains(&server) {
                generic_mcp_servers.push(server);
            }
        }
        let mut resources = load_resources(ResourceLoaderOptions {
            cwd: cwd.clone(),
            agent_dir: agent_dir.clone(),
            settings: Some(SettingsManager::create(&cwd, &agent_dir)),
            extra_builtin_skill_overrides,
            additional_skill_paths: prompt.additional_skill_paths.clone(),
            additional_prompt_paths: prompt.additional_prompt_paths.clone(),
            system_prompt: prompt.custom_system_prompt.clone(),
            ..ResourceLoaderOptions::default()
        })
        .map_err(OpenError::Resources)?;
        let kernel_skills = kernel_python_skills(&resources.skills, trust.level);
        if let Some(message) = trust.warning(&kernel_skills.withheld) {
            resources
                .skill_diagnostics
                .push(crate::skills::ResourceDiagnostic::Warning {
                    message,
                    path: None,
                });
        }
        Ok(SessionResources {
            resources,
            generic_mcp_servers,
            mcp: shared_mcp.unwrap_or_else(|| Arc::new(Mutex::new(built_mcp))),
            python_skills: kernel_skills.admitted,
        })
    })
    .await
    .map_err(|error| {
        OpenError::Resources(anyhow::anyhow!("resource loading task failed: {error}"))
    })?
}

/// The root conversation; a new one starts with the requested (or settings
/// default) model and thinking level at the session's cwd. An existing root
/// keeps its agent.
async fn open_root(
    harness: &Harness,
    config: &SessionConfig,
    models: &eukhe_pi_ai::models::Models,
    manager: &SettingsManager,
    cx: &Context,
) -> Result<Conversation, OpenError> {
    if let Some(root) = harness.conversation(ROOT_CONVERSATION_ID, cx).await? {
        return Ok(root);
    }
    let resolved =
        resolve_session_model(models, manager, config.model.as_ref(), config.thinking, cx).await?;
    let mut agent = AgentChange {
        cwd: FieldChange::Set(config.cwd.to_string_lossy().into_owned()),
        ..AgentChange::default()
    };
    match resolved {
        Some(resolved) => {
            agent.model = FieldChange::Set(resolved.model);
            agent.thinking_level = FieldChange::Set(resolved.thinking);
        }
        None => {
            if let Some(thinking) = config.thinking {
                agent.thinking_level = FieldChange::Set(thinking);
            }
        }
    }
    Ok(harness
        .root(
            RootOptions {
                agent: Some(agent),
                init: None,
            },
            cx,
        )
        .await?)
}

async fn close_after_failure(harness: &Harness, cx: &Context) {
    if let Err(error) = harness.close(cx).await {
        tracing::warn!(error = %error, "closing a session that failed to open");
    }
}

#[cfg(test)]
mod tests;
