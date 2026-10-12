//! The gateway's daemon connection: start the daemon through the launcher,
//! reconnect with backoff, and open (create + attach) the session the phone
//! talks to.

use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::Context;
use eukhe_tui::daemon_client::{outdated_daemon_notice, DaemonClient, DaemonClientEvent};
use eukhe_types::daemon::{DaemonCommand, DaemonSessionLifecycle};
use serde_json::{Map, Value};
use tokio::sync::{mpsc, watch};

use crate::sessions::{SavedSession, SessionRef};
use crate::DaemonLauncher;

/// The first reconnect delay; it doubles up to [`RECONNECT_MAX_DELAY`].
pub(crate) const RECONNECT_FIRST_DELAY: Duration = Duration::from_millis(250);
pub(crate) const RECONNECT_MAX_DELAY: Duration = Duration::from_secs(10);

/// The attach capabilities: the interactive client's set (snapshot state
/// without duplicated history or image payloads).
const ATTACH_CAPABILITIES: [&str; 4] = [
    "attach_snapshot",
    "event_sequence",
    "slim_attach",
    "elide_snapshot_images",
];

/// The session the gateway is attached to.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Binding {
    pub(crate) session: SessionRef,
    pub(crate) active_session_id: String,
    /// The create config that (re)opens it.
    pub(crate) create_config: Value,
}

/// An opened session and whether it ran a turn at attach time.
pub(crate) struct Opened {
    pub(crate) binding: Binding,
    pub(crate) streaming: bool,
}

/// How a reconnect ended.
pub(crate) enum Reconnect {
    Connected,
    /// SIGINT or SIGTERM arrived first.
    ShuttingDown,
}

/// One live daemon connection plus what it takes to replace it.
pub(crate) struct Link<L> {
    socket_path: PathBuf,
    launcher: L,
    shutdown: watch::Receiver<bool>,
    pub(crate) client: DaemonClient,
    pub(crate) events: mpsc::UnboundedReceiver<DaemonClientEvent>,
    /// Fires when the supervisor connection's reader ends.
    pub(crate) reader_dead: watch::Receiver<bool>,
}

type Connection = (DaemonClient, mpsc::UnboundedReceiver<DaemonClientEvent>);

/// Connect to the daemon on `socket_path` and greet it once; never starts
/// one.
#[tracing::instrument(skip_all, fields(socket = %socket_path.display()))]
async fn connect_daemon(socket_path: &Path) -> anyhow::Result<Connection> {
    let (client, events) = DaemonClient::connect(socket_path)
        .await
        .context("connect to the eukhe daemon")?;
    if let Some(version) = client.outdated_daemon_version() {
        tracing::warn!("{}", outdated_daemon_notice(&version));
    }
    Ok((client, events))
}

impl<L: DaemonLauncher> Link<L> {
    /// The first connection; the launcher starts the daemon when needed.
    ///
    /// # Errors
    ///
    /// The launcher cannot start a daemon, or the connection fails.
    #[tracing::instrument(skip_all, fields(socket = %socket_path.display()))]
    pub(crate) async fn connect(
        socket_path: PathBuf,
        launcher: L,
        shutdown: watch::Receiver<bool>,
    ) -> anyhow::Result<Self> {
        launcher.ensure().await.context("start the eukhe daemon")?;
        let (client, events) = connect_daemon(&socket_path).await?;
        Ok(Self {
            socket_path,
            launcher,
            shutdown,
            reader_dead: client.reader_dead(),
            client,
            events,
        })
    }

    /// Whether the supervisor connection is gone (its reader ended, or its
    /// death watch closed).
    pub(crate) fn is_dead(&self) -> bool {
        *self.reader_dead.borrow() || self.reader_dead.has_changed().is_err()
    }

    /// Use a new connection in place of the dead one.
    fn install(&mut self, (client, events): Connection) {
        self.client.close();
        self.reader_dead = client.reader_dead();
        self.client = client;
        self.events = events;
        tracing::info!("reconnected to the daemon");
    }

    /// Replace a dead connection: the launcher (re)starts the daemon, and
    /// failed attempts retry with a doubling delay until one connects or
    /// shutdown begins.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn reconnect(&mut self) -> Reconnect {
        let mut delay = RECONNECT_FIRST_DELAY;
        loop {
            if *self.shutdown.borrow() {
                return Reconnect::ShuttingDown;
            }
            let attempt = async {
                self.launcher
                    .ensure()
                    .await
                    .context("start the eukhe daemon")?;
                connect_daemon(&self.socket_path).await
            }
            .await;
            match attempt {
                Ok(connection) => {
                    self.install(connection);
                    return Reconnect::Connected;
                }
                Err(error) => {
                    tracing::warn!(
                        error = %format!("{error:#}"),
                        retry_ms = delay.as_millis(),
                        "daemon reconnect failed"
                    );
                    tokio::select! {
                        () = tokio::time::sleep(delay) => {}
                        changed = self.shutdown.changed() => {
                            if changed.is_err() {
                                return Reconnect::ShuttingDown;
                            }
                        }
                    }
                    delay = (delay * 2).min(RECONNECT_MAX_DELAY);
                }
            }
        }
    }

    /// One connection attempt to a daemon that another client started;
    /// never starts one (the last daemon stopped on request).
    ///
    /// # Errors
    ///
    /// No daemon answers on the socket.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn try_reconnect(&mut self) -> anyhow::Result<()> {
        let connection = connect_daemon(&self.socket_path).await?;
        self.install(connection);
        Ok(())
    }

    /// The saved root sessions of `session_dir`, newest first.
    ///
    /// # Errors
    ///
    /// The request fails or the answer has another shape.
    #[tracing::instrument(skip_all)]
    pub(crate) async fn root_sessions(
        &self,
        session_dir: &Path,
        cwd: &Path,
    ) -> anyhow::Result<Vec<SavedSession>> {
        let data = self
            .client
            .request_ok(DaemonCommand::ListSavedSessions {
                id: None,
                active_session_id: None,
                // Required by the cwd-addressed form; without the
                // `current` scope every cwd's sessions answer.
                cwd: Some(cwd.display().to_string()),
                session_dir: Some(session_dir.display().to_string()),
                scope: Value::Null,
                rest: Map::default(),
            })
            .await
            .context("list the saved sessions")?;
        crate::sessions::root_sessions(&data)
    }

    /// Open a session as a resident one (a saved `session_path`, else a new
    /// session) and attach to it. The daemon reuses a live worker of the
    /// same session, so the CLI and the gateway share it.
    ///
    /// # Errors
    ///
    /// The create or the attach fails, or an answer lacks the session ids.
    #[tracing::instrument(skip(self, create_config))]
    pub(crate) async fn open(
        &self,
        session_path: Option<&str>,
        create_config: Value,
    ) -> anyhow::Result<Opened> {
        let created = self
            .client
            .request_ok(DaemonCommand::Create {
                id: None,
                session_path: session_path.map(str::to_string),
                continue_recent: None,
                no_session: None,
                name: None,
                config: Some(create_config.clone()),
                runtime_metadata: None,
                lifecycle: Some(DaemonSessionLifecycle::Resident),
                env: None,
                launch_env: None,
                rest: Map::default(),
            })
            .await
            .context("open the session")?;
        let field = |key: &str| {
            created
                .get(key)
                .and_then(Value::as_str)
                .filter(|value| !value.is_empty())
                .map(str::to_string)
                .with_context(|| format!("the daemon opened a session without {key}"))
        };
        let active_session_id = field("activeSessionId")?;
        let session = SessionRef {
            id: field("sessionId")?,
            path: field("sessionFile")?,
        };
        let attached = self
            .client
            .request_ok(DaemonCommand::Attach {
                id: None,
                active_session_id: active_session_id.clone(),
                client_id: None,
                capabilities: Some(ATTACH_CAPABILITIES.map(str::to_string).to_vec()),
                resume_cursor: None,
                recovery_config: None,
                env: None,
                launch_env: None,
                rest: Map::default(),
            })
            .await
            .context("attach to the session")?;
        let streaming = attached
            .pointer("/snapshot/state/isStreaming")
            .and_then(Value::as_bool)
            .context("the attach snapshot has no isStreaming state")?;
        tracing::info!(session = %session.path, %active_session_id, "attached");
        Ok(Opened {
            binding: Binding {
                session,
                active_session_id,
                create_config,
            },
            streaming,
        })
    }

    /// Stop receiving the events of `active_session_id`.
    ///
    /// # Errors
    ///
    /// The detach request fails.
    #[tracing::instrument(skip(self))]
    pub(crate) async fn detach(&self, active_session_id: &str) -> anyhow::Result<()> {
        self.client
            .request_ok(DaemonCommand::Detach {
                id: None,
                active_session_id: Some(active_session_id.to_string()),
                rest: Map::default(),
            })
            .await
            .with_context(|| format!("detach from {active_session_id}"))?;
        Ok(())
    }
}
