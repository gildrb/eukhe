//! Starting the daemon a client connects to (TS `ensureDaemonRunning`).
//!
//! A [`ProcessLauncher`] owns one supervisor command (an executable and its
//! arguments: `eukhe --mode daemon --daemon-socket <p>` for the CLI,
//! `<path>/eukhe-daemon supervisor --socket <p> --agent-dir <d>` for a host
//! that bundles the engine) and the socket that supervisor binds. A start
//! probes the socket, keeps or replaces the daemon it finds (the verdict of
//! [`crate::daemon_build`]), spawns the command detached when no daemon
//! serves, and waits until the new daemon greets.
//!
//! Only an interactive start ([`ProcessLauncher::ensure_interactive`]) frees
//! a socket: it asks an older idle daemon to stop, and hands a holder that
//! must go to the caller's [`SocketTakeover`]. A background start
//! ([`ProcessLauncher::ensure_background`], the [`DaemonLauncher`] seam)
//! never replaces a daemon.

use std::future::Future;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use anyhow::{anyhow, Context as _, Result};
use eukhe_types::daemon::timing::DAEMON_STARTUP_TIMEOUT_MS;
use eukhe_types::daemon::{
    DaemonCommand, DAEMON_PROTOCOL_VERSION, DAEMON_SCHEMA_ID, IDLE_SHUTDOWN_CAPABILITY,
};

use crate::daemon_build::{
    kept_daemon_notice, older_client_notice, replacement_verdict, Build, Caller, Relation,
    Replacement,
};
use crate::daemon_client::{is_foreign_daemon, DaemonClient};
use crate::saved_sessions::DaemonLauncher;

/// Pause between daemon-startup probes (TS `ensureDaemonRunning` polls at
/// 25ms). A cold supervisor binds its socket ~39ms after the spawn, so the
/// poll interval quantizes every cold launch: the bind lands 0-interval
/// before the next probe, a pure wait on a floor of microseconds. The 1ms
/// interval caps that overshoot at <=1ms for the cost of ~40 failed
/// connects per cold launch (each ~us; bounded by the same 30s startup
/// budget, so a hung boot adds at most ~1k connects/s of syscall work,
/// not a spin). Overshoot tables: probe-grid record 20261001-034500 on the
/// bench repo. Timing-only: the probe itself, the 30s startup budget, and
/// the timeout error are unchanged.
const DAEMON_PROBE_INTERVAL_MS: u64 = 1;

/// The connect budget of one probe of [`socket_released`].
const RELEASE_PROBE_TIMEOUT: Duration = Duration::from_millis(250);

/// The pause between two probes of [`socket_released`].
const RELEASE_PROBE_INTERVAL: Duration = Duration::from_millis(25);

/// What a start left listening on the socket.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DaemonReady {
    /// A daemon of the client's build.
    Current,
    /// A daemon of another build that this start did not replace (it had
    /// active work, the start came from a background client, it is newer
    /// than the client, or it is another build of the same rank); the
    /// notice tells the user.
    Kept { notice: String },
}

impl DaemonReady {
    /// The outcome of a `client` that uses the `daemon` it found.
    fn using(client: Build<'_>, daemon: Build<'_>) -> Self {
        kept_daemon_notice(client, daemon).map_or(Self::Current, |notice| Self::Kept { notice })
    }

    /// The one-line notice a client shows for this outcome, if any.
    #[must_use]
    pub fn notice(self) -> Option<String> {
        match self {
            Self::Current => None,
            Self::Kept { notice } => Some(notice),
        }
    }
}

/// How an interactive start frees a daemon socket it must take over.
///
/// The launcher calls it only for an interactive start: when something that
/// does not greet as this product's daemon holds the socket, and when an
/// older daemon agreed to an idle shutdown but still holds the socket after
/// [`SocketTakeover::shutdown_wait`]. An implementation stops the holding
/// process only when it is sure the process is this user's eukhe daemon on
/// that socket; anything else it leaves running and names in its error.
pub trait SocketTakeover: Send + Sync {
    /// How long a daemon that agreed to an idle shutdown may take to
    /// release its socket (the supervisor's whole drain).
    fn shutdown_wait(&self) -> Duration;

    /// Stop the process holding `socket_path`; `why` says why the socket
    /// must be freed and starts the error message.
    ///
    /// # Errors
    ///
    /// The holder was left running (not a daemon of this user on this
    /// socket, or it survived the stop) or could not be identified.
    fn stop_holder(&self, socket_path: &Path, why: &str)
        -> impl Future<Output = Result<()>> + Send;
}

/// The takeover of a background start, which never frees a socket: the
/// type has no value.
enum NoTakeover {}

impl SocketTakeover for NoTakeover {
    fn shutdown_wait(&self) -> Duration {
        match *self {}
    }

    // The type has no value, so the body never runs and awaits nothing;
    // the `std::future::ready` form this lint suggests is an unreachable
    // call (`match *self {}` diverges before it).
    #[allow(clippy::unused_async_trait_impl)]
    async fn stop_holder(&self, _socket_path: &Path, _why: &str) -> Result<()> {
        match *self {}
    }
}

/// Who starts: a background client, or an interactive client with the way
/// it frees the socket.
enum Start<'a, T> {
    Background,
    Interactive(&'a T),
}

/// Whether a daemon's protocol version and schema match this build's.
#[derive(Clone, Copy)]
enum Protocol {
    Compatible,
    Incompatible,
}

/// The daemon probe outcome (TS `DaemonVersionProbe`). The client rides
/// boxed so the enum's other arms pay nothing for the largest one.
enum DaemonProbe {
    /// No socket answered.
    Absent,
    /// An eukhe supervisor answered.
    Answered {
        client: Box<DaemonClient>,
        protocol: Protocol,
    },
    /// Something holds the socket but does not greet as this product's
    /// daemon (another protocol name, or an unparseable hello); the
    /// connect error rides along for messages.
    Foreign(String),
}

/// What an idle shutdown request left on the socket.
enum IdleStop {
    /// The daemon was idle and is gone.
    Stopped,
    /// The daemon keeps serving: it has work, it did not agree to stop,
    /// or it cannot stop only when idle.
    Busy,
}

/// Starts one supervisor command on one socket.
pub struct ProcessLauncher {
    /// The supervisor command, ready to spawn (its stdio is null).
    command: Mutex<Command>,
    socket_path: PathBuf,
    stop_hint: String,
}

impl ProcessLauncher {
    /// A launcher that spawns `command` when no daemon serves
    /// `socket_path`. `command` runs a supervisor that binds `socket_path`
    /// (program, arguments, working directory and environment are the
    /// caller's); the launcher runs it detached: null stdio, in a new
    /// session (the eukhe binaries leave the launcher's session at startup).
    /// `stop_hint` is the step a user takes to stop a daemon that holds the
    /// socket (an error names it: "Run: `<stop_hint>`, then retry ...").
    #[must_use]
    pub fn new(
        mut command: Command,
        socket_path: impl Into<PathBuf>,
        stop_hint: impl Into<String>,
    ) -> Self {
        command
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        eukhe_types::platform::process::request_new_session(&mut command);
        Self {
            command: Mutex::new(command),
            socket_path: socket_path.into(),
            stop_hint: stop_hint.into(),
        }
    }

    /// The socket the supervisor binds.
    #[must_use]
    pub fn socket_path(&self) -> &Path {
        &self.socket_path
    }

    /// Start for a background client (a dashboard, a gateway, a host's
    /// relaunch of a lost daemon): spawn the supervisor when no daemon
    /// serves, then wait until it greets. A running daemon is never
    /// replaced: one of another build is kept with a notice.
    ///
    /// # Errors
    ///
    /// The daemon on the socket is incompatible, something that is not this
    /// product's daemon holds the socket, the supervisor cannot be spawned,
    /// or no daemon greets before the startup timeout.
    pub async fn ensure_background(&self, client: Build<'_>) -> Result<DaemonReady> {
        self.ensure(client, Start::<NoTakeover>::Background).await
    }

    /// Start for an interactive client (a user starting a chat): like
    /// [`ProcessLauncher::ensure_background`], but an idle daemon of a lower
    /// version is replaced ([`replacement_verdict`]) and a foreign holder of
    /// the socket is handed to `takeover`. A client older than an
    /// incompatible daemon fails with the older-client notice.
    ///
    /// # Errors
    ///
    /// An incompatible daemon is kept (newer than the client, or busy), the
    /// socket's holder could not be stopped, the supervisor cannot be
    /// spawned, or no daemon greets before the startup timeout.
    pub async fn ensure_interactive(
        &self,
        client: Build<'_>,
        takeover: &impl SocketTakeover,
    ) -> Result<DaemonReady> {
        self.ensure(client, Start::Interactive(takeover)).await
    }

    async fn ensure<T: SocketTakeover>(
        &self,
        client: Build<'_>,
        start: Start<'_, T>,
    ) -> Result<DaemonReady> {
        let socket_path = self.socket_path.as_path();
        let caller = match start {
            Start::Background => Caller::Background,
            Start::Interactive(_) => Caller::Interactive,
        };
        match probe_daemon(socket_path).await {
            DaemonProbe::Absent => {}
            DaemonProbe::Foreign(reason) => match start {
                Start::Interactive(takeover) => takeover.stop_holder(socket_path, &reason).await?,
                Start::Background => return Err(self.incompatible(&reason)),
            },
            DaemonProbe::Answered {
                client: daemon_client,
                protocol,
            } => {
                let daemon = daemon_client.daemon_build();
                let verdict = replacement_verdict(client, daemon, caller);
                let takeover = match (verdict, &start) {
                    (Replacement::Replace, Start::Interactive(takeover)) => Some(*takeover),
                    // A background start is never answered `Replace`
                    // (`background_never_replaces`): it keeps the daemon.
                    (Replacement::Replace, Start::Background) | (Replacement::Keep(_), _) => None,
                };
                let Some(takeover) = takeover else {
                    let outcome = match (verdict, protocol) {
                        (
                            Replacement::Replace
                            | Replacement::Keep(
                                Relation::Same
                                | Relation::Older
                                | Relation::Newer
                                | Relation::Other,
                            ),
                            Protocol::Compatible,
                        ) => Ok(DaemonReady::using(client, daemon)),
                        (Replacement::Keep(Relation::Newer), Protocol::Incompatible) => {
                            Err(anyhow!("{}", older_client_notice(client, daemon)))
                        }
                        (
                            Replacement::Replace
                            | Replacement::Keep(Relation::Same | Relation::Older | Relation::Other),
                            Protocol::Incompatible,
                        ) => Err(self.incompatible("it is not replaced by this start")),
                    };
                    daemon_client.close();
                    return outcome;
                };
                match (
                    self.stop_daemon_if_idle(&daemon_client, takeover).await?,
                    protocol,
                ) {
                    (IdleStop::Stopped, Protocol::Compatible | Protocol::Incompatible) => {}
                    (IdleStop::Busy, Protocol::Compatible) => {
                        return Ok(DaemonReady::using(client, daemon));
                    }
                    (IdleStop::Busy, Protocol::Incompatible) => {
                        return Err(self.incompatible("the running daemon has active work"));
                    }
                }
            }
        }
        self.spawn_detached()?;
        let deadline = Instant::now() + Duration::from_millis(DAEMON_STARTUP_TIMEOUT_MS);
        loop {
            match probe_daemon(socket_path).await {
                DaemonProbe::Answered {
                    client: daemon_client,
                    protocol: Protocol::Compatible,
                } => {
                    // A concurrent launcher of another build may have won the
                    // socket: it serves, so use it (the notice names it).
                    let ready = DaemonReady::using(client, daemon_client.daemon_build());
                    daemon_client.close();
                    return Ok(ready);
                }
                DaemonProbe::Answered {
                    client: daemon_client,
                    protocol: Protocol::Incompatible,
                } => {
                    // A concurrent launcher won the socket with a build whose
                    // protocol matches ours at connect time but failed the
                    // schema check: re-probe before deciding.
                    daemon_client.close();
                }
                DaemonProbe::Foreign(_) | DaemonProbe::Absent => {}
            }
            if Instant::now() > deadline {
                return Err(anyhow!(
                    "Timed out waiting for the Eukhe daemon to start on {}. Run: {}, then retry the original command.",
                    socket_path.display(),
                    self.stop_hint
                ));
            }
            tokio::time::sleep(Duration::from_millis(DAEMON_PROBE_INTERVAL_MS)).await;
        }
    }

    /// The error for a daemon this start does not use or replace.
    fn incompatible(&self, why: &str) -> anyhow::Error {
        anyhow!(
            "An incompatible Eukhe daemon is running on {} ({why}).\n\nRun:\n  {}\n\nThen retry the original command.",
            self.socket_path.display(),
            self.stop_hint
        )
    }

    /// Ask the daemon to stop only when idle (`shutdown` with `ifIdle`). The
    /// supervisor decides it atomically with the stop, so a run that starts
    /// during the request is never aborted. A daemon without the
    /// idle-shutdown capability would ignore `ifIdle` and stop
    /// unconditionally: it is not asked and counts as busy. A daemon that
    /// agreed but does not exit is stopped through `takeover`. Its sessions
    /// persist and reattach to the replacement.
    async fn stop_daemon_if_idle(
        &self,
        client: &DaemonClient,
        takeover: &impl SocketTakeover,
    ) -> Result<IdleStop> {
        if !client.supports_server_capability(IDLE_SHUTDOWN_CAPABILITY) {
            client.close();
            return Ok(IdleStop::Busy);
        }
        let answer = client
            .request(DaemonCommand::Shutdown {
                id: None,
                force: None,
                if_idle: Some(true),
                rest: serde_json::Map::default(),
            })
            .await;
        client.close();
        let wait = takeover.shutdown_wait();
        match answer {
            Ok(response) if response.success => {}
            // The daemon answered and did not agree (busy, or already
            // stopping for another client).
            Ok(_) => return Ok(IdleStop::Busy),
            // No answer: the daemon may stop before it answers, so the
            // socket decides.
            Err(_) => {
                return Ok(if socket_released(&self.socket_path, wait).await {
                    IdleStop::Stopped
                } else {
                    IdleStop::Busy
                });
            }
        }
        if !socket_released(&self.socket_path, wait).await {
            takeover
                .stop_holder(
                    &self.socket_path,
                    &format!(
                        "the Eukhe daemon on {} did not stop after it agreed to an idle shutdown",
                        self.socket_path.display()
                    ),
                )
                .await?;
        }
        Ok(IdleStop::Stopped)
    }

    /// Spawn the supervisor command; the child outlives this process.
    fn spawn_detached(&self) -> Result<()> {
        let mut command = self
            .command
            .lock()
            .map_err(|_| anyhow!("the supervisor command's lock is poisoned"))?;
        command
            .spawn()
            .with_context(|| format!("spawn the Eukhe daemon on {}", self.socket_path.display()))?;
        Ok(())
    }
}

/// A background start of this build ([`ProcessLauncher::ensure_background`]);
/// the notice of a kept daemon goes to the log.
impl DaemonLauncher for ProcessLauncher {
    #[tracing::instrument(skip_all, fields(socket = %self.socket_path.display()))]
    async fn ensure(&self) -> Result<()> {
        if let Some(notice) = self.ensure_background(Build::THIS).await?.notice() {
            tracing::warn!("{notice}");
        }
        Ok(())
    }
}

/// Probe the socket once: connect, read the hello, and classify it. The
/// hello is the only round trip.
async fn probe_daemon(socket_path: &Path) -> DaemonProbe {
    let client = match DaemonClient::connect(socket_path).await {
        Ok((client, _events)) => client,
        Err(error) if is_foreign_daemon(&error) => {
            return DaemonProbe::Foreign(format!("{error:#}"));
        }
        Err(_) => return DaemonProbe::Absent,
    };
    let hello = client.hello();
    let compatible = hello.get("protocol").and_then(|p| p.get("version"))
        == Some(&serde_json::json!(DAEMON_PROTOCOL_VERSION))
        && hello.get("schemaId") == Some(&serde_json::json!(DAEMON_SCHEMA_ID));
    DaemonProbe::Answered {
        client: Box::new(client),
        protocol: if compatible {
            Protocol::Compatible
        } else {
            Protocol::Incompatible
        },
    }
}

/// Whether nothing accepts connections on `socket_path` within `within`
/// (probed every 25ms).
pub async fn socket_released(socket_path: &Path, within: Duration) -> bool {
    let deadline = Instant::now() + within;
    while Instant::now() < deadline {
        let connect = eukhe_types::platform::transport::connect_transport(socket_path);
        if !matches!(
            tokio::time::timeout(RELEASE_PROBE_TIMEOUT, connect).await,
            Ok(Ok(_))
        ) {
            return true;
        }
        tokio::time::sleep(RELEASE_PROBE_INTERVAL).await;
    }
    false
}
