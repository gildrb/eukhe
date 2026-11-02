//! Subagents of a headless session (`-p`, `--mode json`, `--mode rpc`).
//! The session runs in this process, but its children are ordinary daemon
//! child sessions: they are spawned through the daemon supervisor with
//! the same [`SupervisorChildSessions`] host a daemon worker uses, so
//! model resolution, workspaces, kickoff, settle watching, rename, delete
//! and hand-back stay one code path. The parent's in-process
//! `eukhe.rlm.child` task long-polls each child through this host and
//! admits its report into the parent conversation.
//!
//! The supervisor starts on demand: the first host call that reaches it
//! ensures one listens at the run's daemon socket (a background start,
//! which never replaces a running daemon). A run that never spawns never
//! touches a daemon. A supervisor this run starts lives only as long as
//! this process ([`SupervisorLife::Caller`]); a daemon that was already
//! running is the user's and keeps running.
//!
//! On that supervisor the session registers as its children's parent
//! ([`HeadlessParentLink`]) for the life of this process: a child's
//! `agent_message.send(..., receiver_role="parent")` reaches the session's
//! main conversation, and when this process ends, however it ends, the
//! supervisor closes the children it still hosts.

use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock, Weak};

use anyhow::Context as _;
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::child_workspace::Handback;
use eukhe_core::durable::children::{self as durable, RlmSubagentHost};
use eukhe_core::durable::{EukheSession, SessionConfig};
use eukhe_core::kernel::HostRequestHandlers;
use eukhe_daemon::headless_parent::{HeadlessParentIdentity, HeadlessParentLink};
use eukhe_daemon::rlm_children::{
    durable_child_identities, ParentIdentity, SupervisorChildSessions,
};
use eukhe_daemon::supervisor_link::SupervisorLink;
use eukhe_types::ai::ModelThinkingLevel;

use crate::interactive_mode::{Launch, SupervisorLife};
use crate::mode::RunOptions;

/// Verification seam: the scripted-engine FILE every child of a scripted
/// headless parent runs (the daemon-attached modes read the same
/// variable). The product never sets it.
const FAUX_CHILD_SCRIPT_ENV: &str = "EUKHE_FAUX_CHILD_SCRIPT";

/// The child runtime of one headless session: the value its
/// `SessionConfig::children` holds ([`Self::host`]), bound to the opened
/// session afterwards ([`Self::bind`]).
pub(crate) struct HeadlessChildren {
    host: Arc<HeadlessChildHost>,
}

/// [`SupervisorChildSessions`] behind an on-demand supervisor start.
struct HeadlessChildHost {
    sessions: Arc<SupervisorChildSessions>,
    link: Arc<SupervisorLink>,
    socket_path: PathBuf,
    spawn_cwd: PathBuf,
    /// The session as its children's parent registers.
    parent: HeadlessParentIdentity,
    /// The opened session ([`HeadlessChildren::bind`]), held weakly (the
    /// session's own deps hold this host).
    session: OnceLock<Weak<EukheSession>>,
    /// Set once a supervisor answered on `socket_path`; concurrent first
    /// calls share the one in-flight start, and a failed start leaves it
    /// unset so a later call tries again. It holds the session's
    /// registration as its children's parent for the life of the host;
    /// `None` when the supervisor refused it (an older daemon): the
    /// children run, but cannot message the session.
    supervisor: tokio::sync::OnceCell<Option<HeadlessParentLink>>,
}

impl HeadlessChildren {
    /// The child runtime of the headless session `session_id` working in
    /// `cwd` (its persisted storage at `session_file`; `None` for a memory
    /// session) at `rlm_depth` under the bound `rlm_max_depth`. The
    /// session id is also its active session id: the children's parent
    /// edge (`parentActiveSessionId`) and the spawn cap's family root.
    pub(crate) fn new(
        options: &RunOptions,
        session_id: &str,
        cwd: &Path,
        session_file: Option<&Path>,
        rlm_depth: u32,
        rlm_max_depth: u32,
    ) -> Self {
        let socket_path =
            crate::config::resolve_daemon_socket_path(options.daemon_socket.as_deref());
        let link = Arc::new(SupervisorLink::new(socket_path.clone()));
        let sessions = Arc::new(SupervisorChildSessions::new(
            Arc::clone(&link),
            options.config.agent_dir.clone(),
            session_id.to_owned(),
        ));
        sessions.set_identity(ParentIdentity {
            rlm_depth,
            rlm_max_depth,
            // The live parent model source ([`Self::bind`]) answers it at
            // each spawn.
            model: None,
            cwd: Some(cwd.to_string_lossy().into_owned()),
            session_id: Some(session_id.to_owned()),
            session_file: session_file.map(|file| file.to_string_lossy().into_owned()),
            thinking: options
                .config
                .thinking
                .map(ModelThinkingLevel::wire_name)
                .map(str::to_owned),
            child_script: std::env::var_os(FAUX_CHILD_SCRIPT_ENV)
                .map(|script| script.to_string_lossy().into_owned()),
        });
        Self {
            host: Arc::new(HeadlessChildHost {
                sessions,
                link,
                socket_path,
                spawn_cwd: options.config.cwd.clone(),
                parent: HeadlessParentIdentity {
                    session_id: session_id.to_owned(),
                    session_name: None,
                    session_file: session_file.map(Path::to_path_buf),
                    cwd: cwd.to_path_buf(),
                },
                session: OnceLock::new(),
                supervisor: tokio::sync::OnceCell::new(),
            }),
        }
    }

    /// The host the session spawns its children through
    /// (`SessionConfig::children`).
    pub(crate) fn host(&self) -> Arc<dyn RlmSubagentHost> {
        Arc::clone(&self.host) as Arc<dyn RlmSubagentHost>
    }

    /// Wire the session's `agent_message.*` and `agent_observe.*` host
    /// handlers into `config`: the session messages and observes its
    /// children through the supervisor that hosts them (the kin rule
    /// admits only its own children).
    pub(crate) fn register_agent_messaging(&self, config: &mut SessionConfig) {
        let handlers = config
            .extra_host_handlers
            .get_or_insert_with(HostRequestHandlers::default);
        eukhe_daemon::headless_parent::register_agent_messaging(
            &self.host.link,
            &self.host.parent,
            &self.host.sessions,
            handlers,
        );
    }

    /// Bind the host to the opened `session`: a spawn without a model
    /// inherits the model its main conversation runs on now, a child
    /// starts from the session's cvar family, and the family view reads
    /// the main conversation's durable children. The readers hold the
    /// session weakly (the session's own deps hold this host).
    pub(crate) fn bind(&self, session: &Arc<EukheSession>) {
        // A second bind keeps the first session: one host belongs to one
        // open.
        let _first_bind_wins = self.host.session.set(Arc::downgrade(session));
        let sessions = &self.host.sessions;
        let weak = Arc::downgrade(session);
        sessions.set_parent_model_source(Arc::new(move || {
            let session = weak.upgrade();
            Box::pin(async move {
                let agent = session?.main().agent(&BACKGROUND_CONTEXT).await.ok()?;
                agent
                    .model
                    .map(|model| format!("{}/{}", model.provider, model.model_id))
            })
        }));
        let weak = Arc::downgrade(session);
        sessions.set_parent_cvar_family_source(Arc::new(move || {
            weak.upgrade().map_or_else(Vec::new, |session| {
                session.deps().settings.manager().cvars().family().to_vec()
            })
        }));
        let weak = Arc::downgrade(session);
        sessions.set_durable_children_source(Arc::new(move || {
            let session = weak.upgrade();
            Box::pin(async move {
                match session {
                    Some(session) => {
                        durable_child_identities(
                            session.harness(),
                            session.main().id(),
                            &BACKGROUND_CONTEXT,
                        )
                        .await
                    }
                    None => Ok(Vec::new()),
                }
            })
        }));
    }
}

impl HeadlessChildHost {
    /// The child sessions, once a supervisor listens on the run's socket
    /// (started here, tied to this process, when none does) and the
    /// session registered as their parent.
    #[tracing::instrument(level = "debug", skip_all, fields(socket = %self.socket_path.display()))]
    async fn supervised(&self) -> anyhow::Result<&SupervisorChildSessions> {
        self.supervisor
            .get_or_try_init(|| async {
                let exe = std::env::current_exe().context("resolve the eukhe executable")?;
                let (ready, launch) = crate::interactive_mode::ensure_daemon(
                    &exe,
                    eukhe_tui::daemon_build::Build::THIS,
                    &self.socket_path,
                    &self.spawn_cwd,
                    eukhe_tui::daemon_build::Caller::Background,
                    SupervisorLife::Caller,
                )
                .await
                .with_context(|| {
                    format!(
                        "cannot start the daemon supervisor that hosts subagents on {}",
                        self.socket_path.display()
                    )
                })?;
                if let Some(notice) = ready.notice() {
                    tracing::warn!("{notice}");
                }
                match launch {
                    Launch::Started { pid } => tracing::debug!(
                        pid,
                        "started the subagent supervisor; it stops when this process exits"
                    ),
                    Launch::Found => {}
                }
                let session = self.session.get().cloned().unwrap_or_default();
                anyhow::Ok(
                    match HeadlessParentLink::register(&self.link, self.parent.clone(), session)
                        .await
                    {
                        Ok(parent) => Some(parent),
                        Err(error) => {
                            tracing::warn!(
                                %error,
                                "this session's subagents cannot message it, and outlive a crash of this run"
                            );
                            None
                        }
                    },
                )
            })
            .await?;
        Ok(self.sessions.as_ref())
    }
}

impl RlmSubagentHost for HeadlessChildHost {
    fn spawn(
        &self,
        request: durable::RlmChildSpawnRequest,
    ) -> durable::RlmHostFuture<'_, durable::RlmChildSession> {
        Box::pin(async move { self.supervised().await?.spawn(request).await })
    }

    fn prompt(&self, request: durable::RlmChildPromptRequest) -> durable::RlmHostFuture<'_, ()> {
        Box::pin(async move { self.supervised().await?.prompt(request).await })
    }

    fn wait_settled(
        &self,
        request: durable::RlmChildWaitRequest,
    ) -> durable::RlmHostFuture<'_, durable::RlmChildObservation> {
        Box::pin(async move { self.supervised().await?.wait_settled(request).await })
    }

    fn cancel(&self, request: durable::RlmChildCancelRequest) -> durable::RlmHostFuture<'_, ()> {
        Box::pin(async move { self.supervised().await?.cancel(request).await })
    }

    fn stop(&self, request: durable::RlmChildCancelRequest) -> durable::RlmHostFuture<'_, ()> {
        Box::pin(async move { self.supervised().await?.stop(request).await })
    }

    fn delete(&self, request: durable::RlmChildDeleteRequest) -> durable::RlmHostFuture<'_, ()> {
        Box::pin(async move { self.supervised().await?.delete(request).await })
    }

    /// Lists only the children this process spawned, so it never needs
    /// a supervisor of its own: a spawn already started one.
    fn list(&self) -> durable::RlmHostFuture<'_, Vec<durable::RlmChildListing>> {
        self.sessions.list()
    }

    /// A child renames through the supervisor; the session itself is no
    /// supervisor session, so a self rename (which routes through the
    /// supervisor to the session's worker) has no route.
    fn rename(&self, request: durable::RlmRenameRequest) -> durable::RlmHostFuture<'_, ()> {
        Box::pin(async move {
            match &request.target {
                durable::RlmRenameTarget::Child { .. } => {
                    self.supervised().await?.rename(request).await
                }
                durable::RlmRenameTarget::Session { .. } => anyhow::bail!(
                    "rlm.rename can rename only this session's subagents: a headless session is not daemon-hosted"
                ),
            }
        })
    }

    fn spawn_capacity(&self) -> durable::RlmHostFuture<'_, durable::RlmSpawnCapacity> {
        Box::pin(async move { self.supervised().await?.spawn_capacity().await })
    }

    fn hand_back(
        &self,
        request: durable::RlmChildHandbackRequest,
    ) -> durable::RlmHostFuture<'_, Option<Handback>> {
        Box::pin(async move { self.supervised().await?.hand_back(request).await })
    }
}
