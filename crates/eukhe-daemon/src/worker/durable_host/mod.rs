//! The worker's durable session host: one [`EukheSession`] (the durable
//! Harness with the eukhe extensions) per worker session, its storage
//! lease, and the event bridge that turns the shown conversation's durable
//! events into the daemon wire.
//!
//! The Harness owns persistence, the input inbox, retries, compaction, tool
//! execution, and crash resume. A worker that dies mid-run is relaunched by
//! the supervisor; its `create` reopens the same storage and `open_session`
//! resumes the run (no prompt replay, no queue snapshot).

pub(crate) mod bridge;
pub(crate) mod meta;
pub(crate) mod suspended;
pub mod translator;
pub mod wire_messages;

pub(crate) use bridge::{EventBridge, ShownView};
pub use translator::{CoalesceMode, ConversationMirror, EventTranslator};

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::Context;
use eukhe_core::durable::observe::telemetry::{
    build_client, install as install_telemetry, telemetry_enabled_switch, SessionCounters,
    SessionTelemetry, SkillCounts, TelemetryWiring,
};
use eukhe_core::durable::{
    compose_models_json, open_session, EukheSession, HostDeps, ModelRequest, ModelsError,
    OpenError, SessionConfig, SessionStorage,
};
use eukhe_durable::harness::{watch_events, AgentEventStream, Conversation, Harness};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_pi_ai::models::Models;
use eukhe_pi_ai::providers::faux_script::{
    create_faux_script_models, parse_faux_script_value, FauxScriptError,
};
use futures::future::FutureExt as _;

use crate::lease::SessionLease;

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Why a session could not be hosted.
#[derive(Debug, thiserror::Error)]
pub(crate) enum HostError {
    #[error(transparent)]
    Lease(anyhow::Error),
    #[error(transparent)]
    Models(#[from] ModelsError),
    #[error(transparent)]
    Open(#[from] OpenError),
    #[error(transparent)]
    Session(#[from] SessionError),
}

/// A create-config faux script (`script`) as the model collection every
/// session of the worker shares: its responses are consumed in order across
/// the worker's sessions (a replacement continues the script where the
/// replaced session left it, like the old engine the worker kept).
#[derive(Clone)]
pub(crate) struct ScriptedModels {
    models: Models,
    model: ModelRequest,
}

impl ScriptedModels {
    /// # Errors
    ///
    /// The script is malformed.
    pub(crate) fn parse(script: &serde_json::Value) -> Result<Self, FauxScriptError> {
        let parsed = parse_faux_script_value(script)?;
        let pattern = parsed.model.id.clone();
        let (models, provider) = create_faux_script_models(parsed);
        Ok(Self {
            models,
            model: ModelRequest {
                provider: Some(provider.get_model().provider),
                pattern,
            },
        })
    }
}

/// What the worker opens a session with.
pub(crate) struct HostRequest {
    /// The eukhe session config (cwd, id, storage, role, model, memory...).
    pub(crate) config: SessionConfig,
    /// The worker's faux script models: the session's models become them
    /// and its model the scripted one.
    pub(crate) scripted: Option<ScriptedModels>,
    /// The create command's telemetry opt-out ("1" = disabled; the
    /// session installs no telemetry subscriber).
    pub(crate) telemetry_disabled: Option<bool>,
    /// The create payload's `executionMode` (the client's mode, e.g.
    /// `interactive`); absent reports `unknown`.
    pub(crate) execution_mode: Option<String>,
}

/// One open session on the worker.
pub(crate) struct HostedSession {
    session_id: String,
    storage_dir: Option<PathBuf>,
    harness: Harness,
    deps: Arc<HostDeps>,
    /// `None` once closed. Commands clone the `Arc` for the duration of
    /// one call; [`HostedSession::close`] closes it.
    session: Mutex<Option<Arc<EukheSession>>>,
    lease: Mutex<Option<Arc<SessionLease>>>,
    bridge: Mutex<Option<EventBridge>>,
    /// The session telemetry (`None` when opted out or not a root
    /// session), fed by `telemetry_stream`'s observer.
    telemetry: Option<Arc<SessionTelemetry>>,
    telemetry_stream: Mutex<Option<AgentEventStream>>,
}

impl std::fmt::Debug for HostedSession {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("HostedSession")
            .field("session_id", &self.session_id)
            .field("storage_dir", &self.storage_dir)
            .finish_non_exhaustive()
    }
}

impl HostedSession {
    /// Take the storage lease (JSONL storages), open the session (legacy
    /// import, Harness open, root, services, `resume()`), and return it.
    /// The event bridge starts separately ([`HostedSession::show`]).
    ///
    /// # Errors
    ///
    /// The lease is held by a live process, or the session cannot be
    /// opened.
    pub(crate) async fn open(
        request: HostRequest,
        agent_dir: &Path,
        cx: &Context,
    ) -> Result<Self, HostError> {
        let HostRequest {
            mut config,
            scripted,
            telemetry_disabled,
            execution_mode,
        } = request;
        let storage_dir = match &config.storage {
            SessionStorage::Jsonl { dir, .. } => Some(dir.clone()),
            SessionStorage::Memory => None,
        };
        let lease = match &storage_dir {
            Some(dir) => {
                let (dir, agent_dir) = (dir.clone(), agent_dir.to_path_buf());
                let lease = tokio::task::spawn_blocking(move || {
                    crate::lease::acquire_runtime_session_lease(&dir, &agent_dir)
                })
                .await
                .map_err(|error| HostError::Lease(error.into()))?
                .map_err(HostError::Lease)?;
                Some(Arc::new(lease))
            }
            None => None,
        };
        if let Some(scripted) = scripted {
            // The agent dir's `models.json` composes over the script (its
            // models list and switch like the old registry's).
            compose_models_json(&scripted.models, agent_dir)?;
            config.models = Some(scripted.models);
            // The script serves every turn of the session, whatever model
            // the create named (the old scripted engine ignored the
            // selection): a request naming another provider (a scripted
            // RLM child inheriting its parent's off-catalog selector)
            // runs on the scripted model, since the script's collection
            // holds no other provider to resolve it against.
            let foreign = config.model.as_ref().is_none_or(|request| {
                request
                    .provider
                    .as_deref()
                    .is_some_and(|requested| Some(requested) != scripted.model.provider.as_deref())
            });
            if foreign {
                config.model = Some(scripted.model);
            }
        }
        let is_root = config.role.is_root();
        let session_id = config.session_id.clone();
        let session = open_session(config, cx).await?;
        // Session telemetry (the old worker lifecycle's install, on the
        // durable session): the create's opt-out and non-root sessions
        // install nothing; the client resolves from settings + env, the
        // live switch gates recording, and the observer rides the main
        // conversation's event stream. Fire-and-forget: telemetry never
        // fails the session, and a failed attach keeps the started event
        // with no run facts.
        let (telemetry, telemetry_stream) = install_session_telemetry(
            &session,
            is_root,
            telemetry_disabled,
            execution_mode,
            agent_dir,
            cx,
        )
        .await;
        Ok(Self {
            session_id,
            storage_dir,
            harness: session.harness().clone(),
            deps: Arc::clone(session.deps()),
            session: Mutex::new(Some(Arc::new(session))),
            lease: Mutex::new(lease),
            bridge: Mutex::new(None),
            telemetry,
            telemetry_stream: Mutex::new(telemetry_stream),
        })
    }

    /// The durable session id (`UUIDv7`).
    pub(crate) fn session_id(&self) -> &str {
        &self.session_id
    }

    /// `<sessions_dir>/<id>/`; `None` for an in-memory (`noSession`) session.
    pub(crate) fn storage_dir(&self) -> Option<&Path> {
        self.storage_dir.as_deref()
    }

    pub(crate) fn harness(&self) -> &Harness {
        &self.harness
    }

    pub(crate) fn deps(&self) -> &Arc<HostDeps> {
        &self.deps
    }

    /// The open session.
    ///
    /// # Errors
    ///
    /// `Harness is closed` after [`HostedSession::close`].
    pub(crate) fn session(&self) -> SessionResult<Arc<EukheSession>> {
        lock(&self.session)
            .clone()
            .ok_or_else(|| SessionError::error("Harness is closed"))
    }

    /// The conversation the user talks to (the session's main
    /// conversation: the root unless a fork or tree move changed it).
    ///
    /// # Errors
    ///
    /// `Harness is closed`.
    pub(crate) fn main(&self) -> SessionResult<Conversation> {
        Ok(self.session()?.main())
    }

    /// Resolves once every event batch committed so far reached the wire
    /// (immediately without a bridge).
    ///
    /// A commit publishes to its listeners in turn on the session line, so
    /// a submission waiter can wake before the event stream queued the same
    /// commit's frames. One read on the line first passes that publication.
    pub(crate) async fn events_delivered(&self) {
        if let Ok(main) = self.main() {
            // A closed harness ends the event stream too, which resolves
            // `delivered` below: the barrier read has nothing left to pass.
            let barrier = self
                .harness
                .conversation(main.id(), &eukhe_chord::context::BACKGROUND_CONTEXT);
            if let Err(error) = barrier.await {
                eprintln!("eukhe-daemon worker: event delivery barrier read failed: {error}");
            }
        }
        let delivered = lock(&self.bridge).as_ref().map(EventBridge::delivered);
        if let Some(delivered) = delivered {
            delivered.await;
        }
    }

    /// Show `conversation`: stop the previous bridge, start one on it.
    ///
    /// # Errors
    ///
    /// The event stream cannot be attached.
    pub(crate) async fn show(
        &self,
        conversation: &Conversation,
        sink: bridge::BridgeSink,
    ) -> SessionResult<()> {
        let previous = lock(&self.bridge).take();
        if let Some(previous) = previous {
            previous.stop().await;
        }
        // The session's provider failover events ride along when this
        // session owns its model collection (faux-script shared ones have
        // no runtime).
        let provider_events = self
            .deps()
            .provider_runtime
            .get()
            .map(|runtime| runtime.subscribe());
        // The retry starts report the live policy (`retry.*`, pi-durable's
        // defaults when unset), resolved like the Harness resolves it and
        // re-read per start.
        let settings = Arc::clone(&self.deps().settings);
        let retry_policy = translator::RetryPolicySource::new(move || {
            eukhe_durable::harness::agent::resolve_settings(Some(&settings.harness())).retry
        });
        let started = EventBridge::start(
            &self.harness,
            conversation.id(),
            provider_events,
            retry_policy,
            sink,
        )
        .await?;
        *lock(&self.bridge) = Some(started);
        Ok(())
    }

    /// The session telemetry, when installed (the kill path reports the
    /// archive; skill and child-usage counters ride the same handle).
    pub(crate) fn telemetry(&self) -> Option<&Arc<SessionTelemetry>> {
        self.telemetry.as_ref()
    }

    /// Stop the bridge, close the Harness (pending commits flush), and
    /// release the storage lease. The telemetry observer stops first (no
    /// run facts after the close), and `end()` finalizes the session's
    /// events after it — its failure is swallowed, like every telemetry
    /// seam. Idempotent.
    ///
    /// # Errors
    ///
    /// The Harness close fails (the lease is released either way).
    pub(crate) async fn close(&self, cx: &Context) -> SessionResult<()> {
        let bridge = lock(&self.bridge).take();
        if let Some(bridge) = bridge {
            bridge.stop().await;
        }
        let telemetry_stream = lock(&self.telemetry_stream).take();
        if let Some(stream) = telemetry_stream {
            let _ = stream.stop().await;
        }
        let session = lock(&self.session).take();
        let closed = match session.map(Arc::try_unwrap) {
            Some(Ok(session)) => session.close(cx).await,
            // A command still holds the session for its call: close the
            // Harness under it (its extensions' services stop with the
            // last handle).
            Some(Err(shared)) => shared.harness().close(cx).await,
            None => Ok(()),
        };
        lock(&self.lease).take();
        if let Some(telemetry) = &self.telemetry {
            let _ = telemetry.end().await;
        }
        closed
    }
}

/// Install the session telemetry of a freshly opened root session (the
/// old daemon lifecycle's composition root): the client from settings +
/// env, the execution mode the create payload carried, the live opt-out
/// switch, and the skill adoption counts; the observer consumes the main
/// conversation's event batches. `None`s when opted out, non-root, or the
/// stream cannot attach (telemetry never fails the session).
async fn install_session_telemetry(
    session: &EukheSession,
    is_root: bool,
    telemetry_disabled: Option<bool>,
    execution_mode: Option<String>,
    agent_dir: &Path,
    cx: &Context,
) -> (Option<Arc<SessionTelemetry>>, Option<AgentEventStream>) {
    if telemetry_disabled == Some(true) || !is_root {
        return (None, None);
    }
    let deps = session.deps();
    let wiring = TelemetryWiring {
        client: build_client(&deps.settings.manager(), agent_dir),
        execution_mode,
        now: None,
        telemetry_enabled: Some(telemetry_enabled_switch(&deps.cwd, agent_dir)),
    };
    let telemetry = Arc::new(install_telemetry(
        &wiring,
        Some(SkillCounts {
            skill_count: deps.resources.skills.len(),
            python_skill_count: deps.python_skills.len(),
        }),
        Arc::new(SessionCounters::default()),
    ));
    let stream = match watch_events(session.harness(), session.main().id(), cx).await {
        Ok(stream) => {
            let observer = Arc::clone(&telemetry);
            let started = stream.start(Arc::new(move |batch, _cx| {
                observer.observe_batch(&batch);
                std::future::ready(Ok(())).boxed()
            }));
            if let Err(error) = started {
                eprintln!("eukhe-daemon worker: telemetry observer failed to start: {error}");
                return (Some(telemetry), None);
            }
            Some(stream)
        }
        Err(error) => {
            eprintln!("eukhe-daemon worker: telemetry observer failed to attach: {error}");
            None
        }
    };
    (Some(telemetry), stream)
}

/// The worker's session slot: the hosted session once `create` opened it.
/// Feature handlers clone the `Arc` out and never hold the slot's lock
/// across an await.
#[derive(Clone, Default)]
pub(crate) struct SessionSlot {
    inner: Arc<Mutex<Option<Arc<HostedSession>>>>,
}

impl SessionSlot {
    pub(crate) fn get(&self) -> Option<Arc<HostedSession>> {
        lock(&self.inner).clone()
    }

    /// Install `session`, returning the replaced one (the caller closes it).
    pub(crate) fn replace(&self, session: Arc<HostedSession>) -> Option<Arc<HostedSession>> {
        lock(&self.inner).replace(session)
    }

    pub(crate) fn take(&self) -> Option<Arc<HostedSession>> {
        lock(&self.inner).take()
    }
}

/// The storage of a session: `<sessions_dir>/<id>/`. A `sessionPath` names
/// either that directory or a legacy `<sessions_dir>/<id>.jsonl` (imported
/// on first open into the sibling directory).
#[must_use]
pub(crate) fn storage_for_path(path: &Path) -> (String, PathBuf) {
    if path
        .extension()
        .is_some_and(|extension| extension == "jsonl")
    {
        let id = path
            .file_stem()
            .map(|stem| stem.to_string_lossy().into_owned())
            .unwrap_or_default();
        let dir = path.with_extension("");
        (id, dir)
    } else {
        let id = path
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default();
        (id, path.to_path_buf())
    }
}

/// Whether a durable session exists at `path` (its directory, or a legacy
/// file still to import).
#[must_use]
pub(crate) fn session_exists(path: &Path) -> bool {
    let (_, dir) = storage_for_path(path);
    dir.is_dir() || path.is_file()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_session_path_names_its_storage_dir() {
        let dir = Path::new("/s/0192a000-0000-7000-8000-0000000000f1");
        assert_eq!(
            storage_for_path(dir),
            (
                "0192a000-0000-7000-8000-0000000000f1".to_owned(),
                dir.to_path_buf()
            )
        );
        // A legacy JSONL file maps to the sibling directory it imports into.
        assert_eq!(
            storage_for_path(Path::new("/s/abc.jsonl")),
            ("abc".to_owned(), PathBuf::from("/s/abc"))
        );
    }

    #[test]
    fn a_session_exists_as_its_dir_or_a_legacy_file() {
        let root = tempfile::tempdir().expect("tempdir");
        let legacy = root.path().join("abc.jsonl");
        assert!(!session_exists(&legacy));
        std::fs::write(&legacy, "").expect("legacy file");
        assert!(session_exists(&legacy));
        let stored = root.path().join("def");
        assert!(!session_exists(&stored));
        std::fs::create_dir(&stored).expect("storage dir");
        assert!(session_exists(&stored));
        assert!(session_exists(&root.path().join("def.jsonl")));
    }
}

/// The worker's telemetry install gate (the old lifecycle's): the
/// create's opt-out installs nothing; a root create installs the
/// observer over the main conversation's events.
#[cfg(test)]
mod telemetry_tests {
    use super::{HostRequest, HostedSession};
    use crate::durable_test_support::{cx, Fixture};

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn telemetry_installs_for_root_sessions_and_respects_the_opt_out() {
        let fixture = Fixture::new();
        let open = |session_id: &str, telemetry_disabled| {
            let request = HostRequest {
                config: fixture.config(session_id),
                scripted: None,
                telemetry_disabled,
                execution_mode: Some("interactive".to_owned()),
            };
            let agent_dir = fixture.agent_dir.clone();
            async move {
                HostedSession::open(request, &agent_dir, cx())
                    .await
                    .expect("open session")
            }
        };
        let opted_out = open("telemetry-opt-out", Some(true)).await;
        assert!(opted_out.telemetry().is_none());
        opted_out.close(cx()).await.unwrap();

        let root = open("telemetry-root", None).await;
        assert!(root.telemetry().is_some());
        root.close(cx()).await.unwrap();
    }
}
