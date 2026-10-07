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
pub mod translator;
pub mod wire_messages;

pub use translator::{CoalesceMode, ConversationMirror, EventTranslator};

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::Context;
use eukhe_core::durable::{
    open_session, EukheSession, HostDeps, ModelRequest, OpenError, SessionConfig, SessionStorage,
};
use eukhe_durable::harness::{Conversation, Harness};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_pi_ai::providers::faux_script::{
    create_faux_script_models, parse_faux_script_value, FauxScriptError,
};

use crate::lease::SessionLease;

pub(crate) use bridge::{EventBridge, ShownView};

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Why a session could not be hosted.
#[derive(Debug, thiserror::Error)]
pub(crate) enum HostError {
    #[error(transparent)]
    Lease(anyhow::Error),
    #[error("invalid create script: {0}")]
    Script(#[from] FauxScriptError),
    #[error(transparent)]
    Open(#[from] OpenError),
    #[error(transparent)]
    Session(#[from] SessionError),
}

/// What the worker opens a session with.
pub(crate) struct HostRequest {
    /// The eukhe session config (cwd, id, storage, role, model, memory...).
    pub(crate) config: SessionConfig,
    /// A create-config faux script (`script`): the session's models become
    /// the scripted faux provider and its model the scripted one.
    pub(crate) script: Option<serde_json::Value>,
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
    /// The lease is held by a live process, the script is malformed, or
    /// the session cannot be opened.
    pub(crate) async fn open(
        request: HostRequest,
        agent_dir: &Path,
        cx: &Context,
    ) -> Result<Self, HostError> {
        let HostRequest { mut config, script } = request;
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
        if let Some(script) = script {
            let parsed = parse_faux_script_value(&script)?;
            let model_id = parsed.model.id.clone();
            let (models, provider) = create_faux_script_models(parsed);
            config.models = Some(models);
            if config.model.is_none() {
                config.model = Some(ModelRequest {
                    provider: Some(provider.get_model().provider),
                    pattern: model_id,
                });
            }
        }
        let session_id = config.session_id.clone();
        let session = open_session(config, cx).await?;
        Ok(Self {
            session_id,
            storage_dir,
            harness: session.harness().clone(),
            deps: Arc::clone(session.deps()),
            session: Mutex::new(Some(Arc::new(session))),
            lease: Mutex::new(lease),
            bridge: Mutex::new(None),
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
    pub(crate) async fn events_delivered(&self) {
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
        let started = EventBridge::start(&self.harness, conversation.id(), sink).await?;
        *lock(&self.bridge) = Some(started);
        Ok(())
    }

    /// Stop the bridge, close the Harness (pending commits flush), and
    /// release the storage lease. Idempotent.
    ///
    /// # Errors
    ///
    /// The Harness close fails (the lease is released either way).
    pub(crate) async fn close(&self, cx: &Context) -> SessionResult<()> {
        let bridge = lock(&self.bridge).take();
        if let Some(bridge) = bridge {
            bridge.stop().await;
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
        closed
    }
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
            ("0192a000-0000-7000-8000-0000000000f1".to_owned(), dir.to_path_buf())
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
