//! The daemon-ensure concern (moved with its concern): the socket
//! probe, the replacement verdict on the daemon found there
//! ([`eukhe_tui::daemon_build::replacement_verdict`]), the detached
//! supervisor spawn, and the startup poll window with its timing consts.

use anyhow::Context as _;
use eukhe_daemon::timeouts;
use eukhe_tui::daemon_build::{
    kept_daemon_notice, older_client_notice, replacement_verdict, Build, Caller, Relation,
    Replacement,
};
use eukhe_types::daemon::timing::DAEMON_STARTUP_TIMEOUT_MS;

use super::{anyhow, Command, Duration, Instant, Path, Result, Stdio};

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

/// What [`ensure_daemon_running`] left listening on the socket.
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

/// Starts the daemon for a background client (the `dashboard` and
/// `gateway` commands, the TUI's relaunch of a lost daemon): it spawns a
/// daemon when none listens and waits until it greets, but never replaces
/// a running daemon.
pub(crate) struct CliLauncher {
    pub(crate) socket_path: std::path::PathBuf,
    pub(crate) spawn_cwd: std::path::PathBuf,
}

impl eukhe_tui::saved_sessions::DaemonLauncher for CliLauncher {
    #[tracing::instrument(skip_all, fields(socket = %self.socket_path.display()))]
    async fn ensure(&self) -> anyhow::Result<()> {
        let ready =
            ensure_daemon_running(&self.socket_path, &self.spawn_cwd, Caller::Background).await?;
        if let Some(notice) = ready.notice() {
            tracing::warn!("{notice}");
        }
        Ok(())
    }
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
        client: Box<eukhe_tui::daemon_client::DaemonClient>,
        protocol: Protocol,
    },
    /// Something holds the socket but does not greet as this product's
    /// daemon (another protocol name, or an unparseable hello); the
    /// connect error rides along for messages.
    Foreign(String),
}

/// Probe the socket once: connect, read the hello, and classify it. The
/// hello is the only round trip.
async fn probe_daemon(socket_path: &Path) -> DaemonProbe {
    let client = match eukhe_tui::daemon_client::DaemonClient::connect(socket_path).await {
        Ok((client, _events)) => client,
        Err(error) if eukhe_tui::daemon_client::is_foreign_daemon(&error) => {
            return DaemonProbe::Foreign(format!("{error:#}"));
        }
        Err(_) => return DaemonProbe::Absent,
    };
    let hello = client.hello();
    let compatible = hello.get("protocol").and_then(|p| p.get("version"))
        == Some(&serde_json::json!(
            eukhe_types::daemon::DAEMON_PROTOCOL_VERSION
        ))
        && hello.get("schemaId") == Some(&serde_json::json!(eukhe_types::daemon::DAEMON_SCHEMA_ID));
    DaemonProbe::Answered {
        client: Box::new(client),
        protocol: if compatible {
            Protocol::Compatible
        } else {
            Protocol::Incompatible
        },
    }
}

/// Ensure a daemon is listening on `socket_path`, spawning this executable
/// in `--mode daemon` when none is (TS `ensureDaemonRunning`).
///
/// # Errors
/// See [`ensure_daemon_running_with`]; also errors when this process's
/// executable path cannot be resolved.
pub async fn ensure_daemon_running(
    socket_path: &Path,
    spawn_cwd: &Path,
    caller: Caller,
) -> Result<DaemonReady> {
    let exe = std::env::current_exe().context("resolve the eukhe executable")?;
    ensure_daemon_running_with(&exe, Build::THIS, socket_path, spawn_cwd, caller).await
}

/// [`ensure_daemon_running`] with an explicit supervisor executable and
/// client build (the product path uses this process's own binary and
/// build, TS parity). The daemon on the socket is replaced only when
/// [`replacement_verdict`] says so (an interactive start of a newer build)
/// and only when the daemon is idle ([`stop_daemon_if_idle`]); every other
/// daemon of a compatible protocol is kept with a notice. A client older
/// than an incompatible daemon exits with the older-client notice. A
/// foreign holder of the socket (another protocol name) is stopped on an
/// interactive start when it is this user's eukhe-family supervisor on
/// this socket.
///
/// # Errors
/// Returns an error when an incompatible daemon is kept (newer than the
/// client, started by a background client, or busy), when a foreign holder
/// of the socket cannot or may not be stopped, when the supervisor process
/// cannot be spawned, or when no daemon starts before the startup timeout.
pub async fn ensure_daemon_running_with(
    exe: &Path,
    client: Build<'_>,
    socket_path: &Path,
    spawn_cwd: &Path,
    caller: Caller,
) -> Result<DaemonReady> {
    let incompatible = |why: &str| {
        anyhow!(
            "An incompatible Eukhe daemon is running on {} ({why}).\n\nRun:\n  {}\n\nThen retry the original command.",
            socket_path.display(),
            shutdown_command(socket_path)
        )
    };
    match probe_daemon(socket_path).await {
        DaemonProbe::Absent => {}
        DaemonProbe::Foreign(reason) => match caller {
            Caller::Interactive => stop_socket_holder(socket_path, &reason).await?,
            Caller::Background => return Err(incompatible(&reason)),
        },
        DaemonProbe::Answered {
            client: daemon_client,
            protocol,
        } => {
            let daemon = daemon_client.daemon_build();
            let kept = match (replacement_verdict(client, daemon, caller), protocol) {
                (Replacement::Replace, Protocol::Compatible | Protocol::Incompatible) => None,
                (
                    Replacement::Keep(
                        Relation::Same | Relation::Older | Relation::Newer | Relation::Other,
                    ),
                    Protocol::Compatible,
                ) => Some(Ok(DaemonReady::using(client, daemon))),
                (Replacement::Keep(Relation::Newer), Protocol::Incompatible) => {
                    Some(Err(anyhow!("{}", older_client_notice(client, daemon))))
                }
                (
                    Replacement::Keep(Relation::Same | Relation::Older | Relation::Other),
                    Protocol::Incompatible,
                ) => Some(Err(incompatible("it is not replaced by this start"))),
            };
            if let Some(outcome) = kept {
                daemon_client.close();
                return outcome;
            }
            match (
                stop_daemon_if_idle(&daemon_client, socket_path).await?,
                protocol,
            ) {
                (IdleStop::Stopped, Protocol::Compatible | Protocol::Incompatible) => {}
                (IdleStop::Busy, Protocol::Compatible) => {
                    return Ok(DaemonReady::using(client, daemon));
                }
                (IdleStop::Busy, Protocol::Incompatible) => {
                    return Err(incompatible("the running daemon has active work"));
                }
            }
        }
    }
    spawn_supervisor_detached(socket_path, spawn_cwd, exe)?;
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
                shutdown_command(socket_path)
            ));
        }
        tokio::time::sleep(Duration::from_millis(DAEMON_PROBE_INTERVAL_MS)).await;
    }
}

/// The `shutdown` command that stops whatever holds `socket_path`: the bare
/// command when `socket_path` is the socket that command, run in this
/// environment, targets and its scope reaches; else one naming the socket.
fn shutdown_command(socket_path: &Path) -> String {
    let root = crate::daemon_discovery::current_state_root(None);
    if root.default_socket_path == socket_path && root.scope_contains(socket_path) {
        "eukhe shutdown --force".to_string()
    } else {
        format!(
            "eukhe shutdown --force --daemon-socket '{}'",
            socket_path.display()
        )
    }
}

/// What an idle shutdown request left on the socket.
enum IdleStop {
    /// The daemon was idle and is gone.
    Stopped,
    /// The daemon keeps serving: it has work, it did not agree to stop,
    /// or it cannot stop only when idle.
    Busy,
}

/// Ask the daemon to stop only when idle (`shutdown` with `ifIdle`). The
/// supervisor decides it atomically with the stop, so a run that starts
/// during the request is never aborted. A daemon without the
/// idle-shutdown capability would ignore `ifIdle` and stop
/// unconditionally: it is not asked and counts as busy. A daemon that
/// agreed but does not exit is stopped through its socket holder. Its
/// sessions persist and reattach to the replacement.
async fn stop_daemon_if_idle(
    client: &eukhe_tui::daemon_client::DaemonClient,
    socket_path: &Path,
) -> Result<IdleStop> {
    if !client.supports_server_capability(eukhe_types::daemon::IDLE_SHUTDOWN_CAPABILITY) {
        client.close();
        return Ok(IdleStop::Busy);
    }
    let answer = client
        .request(eukhe_types::daemon::DaemonCommand::Shutdown {
            id: None,
            force: None,
            if_idle: Some(true),
            rest: serde_json::Map::default(),
        })
        .await;
    client.close();
    match answer {
        Ok(response) if response.success => {}
        // The daemon answered and did not agree (busy, or already stopping
        // for another client).
        Ok(_) => return Ok(IdleStop::Busy),
        // No answer: the daemon may stop before it answers, so the socket
        // decides.
        Err(_) => {
            return Ok(if wait_for_socket_gone(socket_path).await {
                IdleStop::Stopped
            } else {
                IdleStop::Busy
            });
        }
    }
    if !wait_for_socket_gone(socket_path).await {
        stop_socket_holder(
            socket_path,
            &format!(
                "the Eukhe daemon on {} did not stop after it agreed to an idle shutdown",
                socket_path.display()
            ),
        )
        .await?;
    }
    Ok(IdleStop::Stopped)
}

/// Stop the process holding `socket_path` (SIGTERM, then SIGKILL after a
/// bounded grace) when it is this user's eukhe-family supervisor launched on
/// this socket; anything else is named in the error and left running.
/// `why` says why the socket must be freed.
async fn stop_socket_holder(socket_path: &Path, why: &str) -> Result<()> {
    use crate::daemon_discovery::owner::{socket_holder, SocketHolder};
    let socket = socket_path.to_path_buf();
    let holder = tokio::task::spawn_blocking(move || socket_holder(&socket))
        .await
        .context("look up the daemon socket's holder")?;
    match holder {
        Some(SocketHolder::Daemon(owner)) => {
            let pid = owner.pid;
            let command = owner.command();
            let stopped = tokio::task::spawn_blocking(move || owner.terminate())
                .await
                .context("stop the daemon socket's holder")?;
            if stopped {
                Ok(())
            } else {
                Err(anyhow!(
                    "{why}; its process (pid {pid}: {command}) survived SIGKILL."
                ))
            }
        }
        Some(SocketHolder::Other { owner, reason }) => Err(anyhow!(
            "{why}. The process holding {} (pid {}: {}) was left running because {reason}; stop it, then retry the original command.",
            socket_path.display(),
            owner.pid,
            owner.command()
        )),
        // The holder may have exited between the probe and the lookup.
        None if wait_for_socket_gone(socket_path).await => Ok(()),
        None => Err(anyhow!(
            "{why}, and the process holding {} could not be identified. Run: {}, then retry the original command.",
            socket_path.display(),
            shutdown_command(socket_path)
        )),
    }
}

/// Wait until nothing accepts connections on the socket (bounded).
async fn wait_for_socket_gone(socket_path: &Path) -> bool {
    let deadline =
        Instant::now() + Duration::from_millis(timeouts::derived().launcher_shutdown_wait_ms);
    while Instant::now() < deadline {
        if !eukhe_daemon::socket::can_connect(socket_path, Duration::from_millis(250)).await {
            return true;
        }
        tokio::time::sleep(Duration::from_millis(25)).await;
    }
    false
}

/// Spawn a detached supervisor on `socket_path` (TS spawns its own entrypoint
/// with `--mode daemon --daemon-socket`; the child outlives this CLI).
fn spawn_supervisor_detached(socket_path: &Path, spawn_cwd: &Path, exe: &Path) -> Result<()> {
    let mut command = Command::new(exe);
    command
        .args(["--mode", "daemon", "--daemon-socket"])
        .arg(socket_path)
        .current_dir(spawn_cwd)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        // Strip inherited worker/supervisor role env vars so the spawned
        // supervisor never starts in worker mode (a CLI running inside a
        // daemon worker would otherwise launch a supervisor that listens but
        // never handshakes) -- the TS launcher deletes the same set.
        .env_remove(eukhe_daemon::worker::WORKER_ROLE_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_TOKEN_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_ACTIVE_SESSION_ID_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_RECOVERY_JOURNAL_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_SUPERVISOR_SOCKET_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_SOCKET_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_INSTANCE_ID_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_SCRIPT_ENV)
        // A lease owner id inherited from an ancestor (a CLI running
        // inside a worker's env) would name a stale session in every
        // lease this daemon's workers write -- TS `daemon-launch.ts`
        // deletes the same var before spawning the supervisor.
        .env_remove(eukhe_daemon::lease::SESSION_LEASE_OWNER_ID_ENV);
    // A daemon must not share the launching TUI's terminal session: a
    // session-wide terminal cleanup could hang it up after the TUI exits.
    // setsid (run by the child at startup) also creates its own process
    // group.
    eukhe_core::platform::process::request_new_session(&mut command);
    command
        .spawn()
        .with_context(|| format!("spawn the Eukhe daemon on {}", socket_path.display()))?;
    Ok(())
}
