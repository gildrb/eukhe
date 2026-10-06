//! The daemon-ensure concern (moved with its concern): the socket
//! probe, the replacement of a stale, outdated, or foreign daemon, the
//! detached supervisor spawn, and the startup poll window with its timing
//! consts.

use anyhow::Context as _;

use super::{anyhow, Command, Duration, Instant, Path, Result, Stdio};

const DAEMON_STARTUP_TIMEOUT_MS: u64 = 30_000;
const DAEMON_SHUTDOWN_WAIT_MS: u64 = 5_000;
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
    /// A daemon of this build.
    Current,
    /// A daemon of another eukhe version that had active work: it keeps
    /// serving (killing it would interrupt the work) and restarts on a later
    /// idle start.
    Outdated { version: String },
}

impl DaemonReady {
    /// The one-line notice a client shows for this outcome, if any.
    #[must_use]
    pub fn notice(&self) -> Option<String> {
        match self {
            Self::Current => None,
            Self::Outdated { version } => {
                Some(eukhe_tui::daemon_client::outdated_daemon_notice(version))
            }
        }
    }
}

/// The daemon probe outcome (TS `DaemonVersionProbe`). The clients ride
/// boxed so the enum's other arms pay nothing for the largest one.
enum DaemonProbe {
    /// No socket answered.
    Absent,
    /// A supervisor of this build answered.
    Current,
    /// A supervisor whose protocol/schema matches this build but that runs
    /// another eukhe version.
    Outdated {
        client: Box<eukhe_tui::daemon_client::DaemonClient>,
        version: String,
    },
    /// A supervisor answered with a different protocol version/schema.
    Stale(Box<eukhe_tui::daemon_client::DaemonClient>),
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
    if !compatible {
        return DaemonProbe::Stale(Box::new(client));
    }
    if let Some(version) = client.outdated_daemon_version() {
        return DaemonProbe::Outdated {
            client: Box::new(client),
            version,
        };
    }
    client.close();
    DaemonProbe::Current
}

/// Ensure a daemon of this build is listening on `socket_path`, spawning
/// this executable in `--mode daemon` when it is not (TS
/// `ensureDaemonRunning`).
///
/// # Errors
/// See [`ensure_daemon_running_with`]; also errors when this process's
/// executable path cannot be resolved.
pub async fn ensure_daemon_running(socket_path: &Path, spawn_cwd: &Path) -> Result<DaemonReady> {
    let exe = std::env::current_exe().context("resolve the eukhe executable")?;
    ensure_daemon_running_with(&exe, socket_path, spawn_cwd).await
}

/// [`ensure_daemon_running`] with an explicit supervisor executable (the
/// product path uses this process's own binary, TS parity). A daemon of
/// another eukhe version is replaced when idle and kept (reported as
/// [`DaemonReady::Outdated`]) when busy; an idle daemon with another
/// protocol/schema is replaced, a busy one refuses; a foreign holder of the
/// socket (another protocol name) is stopped when it is this user's
/// eukhe-family supervisor on this socket.
///
/// # Errors
/// Returns an error when an incompatible daemon has active work, when a
/// foreign holder of the socket cannot or may not be stopped, when the
/// supervisor process cannot be spawned, or when no daemon starts before
/// the startup timeout.
pub async fn ensure_daemon_running_with(
    exe: &Path,
    socket_path: &Path,
    spawn_cwd: &Path,
) -> Result<DaemonReady> {
    match probe_daemon(socket_path).await {
        DaemonProbe::Current => return Ok(DaemonReady::Current),
        DaemonProbe::Outdated { client, version } => {
            if session_work_active(&client).await {
                client.close();
                return Ok(DaemonReady::Outdated { version });
            }
            shutdown_idle_daemon(*client, socket_path).await?;
        }
        DaemonProbe::Stale(client) => {
            if session_work_active(&client).await {
                client.close();
                return Err(anyhow!(
                    "An incompatible Eukhe daemon is running on {}.\n\nRun:\n  {}\n\nThen retry the original command (the running daemon has active work).",
                    socket_path.display(),
                    shutdown_command(socket_path)
                ));
            }
            shutdown_idle_daemon(*client, socket_path).await?;
        }
        DaemonProbe::Foreign(reason) => stop_socket_holder(socket_path, &reason).await?,
        DaemonProbe::Absent => {}
    }
    spawn_supervisor_detached(socket_path, spawn_cwd, exe)?;
    let deadline = Instant::now() + Duration::from_millis(DAEMON_STARTUP_TIMEOUT_MS);
    loop {
        match probe_daemon(socket_path).await {
            DaemonProbe::Current => return Ok(DaemonReady::Current),
            // A concurrent launcher of another version won the socket: it
            // serves, so use it (the notice names the version).
            DaemonProbe::Outdated { client, version } => {
                client.close();
                return Ok(DaemonReady::Outdated { version });
            }
            DaemonProbe::Stale(client) => {
                // A concurrent launcher won the socket with a build whose
                // protocol matches ours at connect time but failed the
                // schema check: re-probe before deciding.
                client.close();
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

/// The `shutdown` command that stops whatever holds `socket_path`: the
/// discovery commands target the default socket unless told otherwise.
fn shutdown_command(socket_path: &Path) -> String {
    if socket_path == eukhe_daemon::socket::default_daemon_socket_path() {
        "eukhe shutdown --force".to_string()
    } else {
        format!(
            "eukhe shutdown --force --daemon-socket '{}'",
            socket_path.display()
        )
    }
}

/// Whether any live session is working (TS `shutdownStaleDaemonIfNotBusy`):
/// active, streaming, compacting, running tools, or waiting on subagents.
/// A daemon that cannot list its sessions counts as busy.
async fn session_work_active(client: &eukhe_tui::daemon_client::DaemonClient) -> bool {
    let sessions = client
        .request_ok(eukhe_types::daemon::DaemonCommand::List {
            id: None,
            all: None,
            cwd: None,
            session_dir: None,
            include_client_owned: None,
            rest: serde_json::Map::default(),
        })
        .await;
    sessions.map_or(true, |data| {
        data.get("sessions")
            .and_then(serde_json::Value::as_array)
            .is_none_or(|rows| {
                rows.iter().any(|row| {
                    [
                        "isSessionActive",
                        "isStreaming",
                        "isCompacting",
                        "isRunningTools",
                        "hasRunningSubagents",
                    ]
                    .iter()
                    .any(|flag| row.get(*flag) == Some(&serde_json::json!(true)))
                })
            })
    })
}

/// Ask an idle daemon to shut down and wait for its socket to go away; a
/// daemon that ignores the request is stopped through its socket holder.
/// Its sessions persist as JSONL and reattach to the replacement.
async fn shutdown_idle_daemon(
    client: eukhe_tui::daemon_client::DaemonClient,
    socket_path: &Path,
) -> Result<()> {
    // The daemon may stop before it answers; the socket check below is the
    // source of truth.
    let _ = client
        .request_ok(eukhe_types::daemon::DaemonCommand::Shutdown {
            id: None,
            force: None,
            rest: serde_json::Map::default(),
        })
        .await;
    client.close();
    if wait_for_socket_gone(socket_path).await {
        return Ok(());
    }
    stop_socket_holder(
        socket_path,
        &format!(
            "the Eukhe daemon on {} did not stop after a shutdown request",
            socket_path.display()
        ),
    )
    .await
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
    let deadline = Instant::now() + Duration::from_millis(DAEMON_SHUTDOWN_WAIT_MS);
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
    // setsid also creates its own process group.
    eukhe_core::platform::process::set_new_session(&mut command);
    command
        .spawn()
        .with_context(|| format!("spawn the Eukhe daemon on {}", socket_path.display()))?;
    Ok(())
}
