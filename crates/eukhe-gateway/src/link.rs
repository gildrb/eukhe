//! The gateway's daemon connection: start the daemon through the launcher,
//! reconnect with backoff, and open (create + attach) the session the phone
//! talks to.

use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::Context;
use eukhe_tui::daemon_build::{kept_daemon_notice, Build};
use eukhe_tui::daemon_client::{DaemonClient, DaemonClientEvent};
use eukhe_tui::saved_sessions::{attach, create_resident, list_root_sessions, CreatedSession};
use eukhe_types::daemon::DaemonCommand;
use serde_json::{Map, Value};
use tokio::sync::{mpsc, watch};

use crate::sessions::{SavedSession, SessionRef};
use eukhe_tui::saved_sessions::DaemonLauncher;

/// The first reconnect delay; it doubles up to [`RECONNECT_MAX_DELAY`].
pub(crate) const RECONNECT_FIRST_DELAY: Duration = Duration::from_millis(250);
pub(crate) const RECONNECT_MAX_DELAY: Duration = Duration::from_secs(10);

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
    if let Some(notice) = kept_daemon_notice(Build::THIS, client.daemon_build()) {
        tracing::warn!("{notice}");
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
        list_root_sessions(&self.client, session_dir, cwd).await
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
        let CreatedSession {
            active_session_id,
            session_id,
            session_file,
        } = create_resident(
            &self.client,
            session_path.map(str::to_string),
            create_config.clone(),
        )
        .await?;
        let session = SessionRef {
            id: session_id,
            path: session_file,
        };
        let attached = attach(&self.client, &active_session_id).await?;
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
