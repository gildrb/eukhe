//! The daemon-ensure concern: the CLI's supervisor command
//! (`eukhe --mode daemon --daemon-socket <p>`, run detached by
//! [`eukhe_client::launcher::ProcessLauncher`], which probes the socket and
//! applies the replacement verdict), the `eukhe shutdown` hint its errors
//! name, and the CLI's socket takeover (stopping this user's eukhe
//! supervisor that holds the socket).

use std::future::Future;

use anyhow::Context as _;
use eukhe_client::daemon_build::{Build, Caller};
use eukhe_client::launcher::{socket_released, DaemonReady, ProcessLauncher, SocketTakeover};
use eukhe_daemon::timeouts;

use super::{anyhow, Command, Duration, Path, Result};

/// The CLI's way to free a daemon socket on an interactive start: the
/// supervisor's whole drain for an agreed idle shutdown, then a stop of
/// the holder when it is this user's eukhe supervisor on that socket.
struct CliTakeover;

impl SocketTakeover for CliTakeover {
    fn shutdown_wait(&self) -> Duration {
        shutdown_wait()
    }

    fn stop_holder(
        &self,
        socket_path: &Path,
        why: &str,
    ) -> impl Future<Output = Result<()>> + Send {
        stop_socket_holder(socket_path, why)
    }
}

/// How long a daemon that agreed to stop may take to release its socket.
fn shutdown_wait() -> Duration {
    Duration::from_millis(timeouts::derived().launcher_shutdown_wait_ms)
}

/// The launcher of `exe` in `--mode daemon` on `socket_path`, spawned in
/// `spawn_cwd`. The spawned supervisor never inherits a worker's or
/// supervisor's role variables: a CLI running inside a daemon worker would
/// otherwise launch a supervisor that starts in worker mode (it listens
/// but never handshakes), and an inherited lease owner id would name a
/// stale session in every lease its workers write (the TS launcher deletes
/// the same set).
#[must_use]
pub(crate) fn cli_launcher(exe: &Path, socket_path: &Path, spawn_cwd: &Path) -> ProcessLauncher {
    let mut command = Command::new(exe);
    command
        .args(["--mode", "daemon", "--daemon-socket"])
        .arg(socket_path)
        .current_dir(spawn_cwd)
        .env_remove(eukhe_daemon::worker::WORKER_ROLE_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_TOKEN_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_ACTIVE_SESSION_ID_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_RECOVERY_JOURNAL_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_SUPERVISOR_SOCKET_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_SOCKET_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_INSTANCE_ID_ENV)
        .env_remove(eukhe_daemon::worker::WORKER_SCRIPT_ENV)
        .env_remove(eukhe_daemon::lease::SESSION_LEASE_OWNER_ID_ENV);
    ProcessLauncher::new(command, socket_path, shutdown_command(socket_path))
}

/// [`cli_launcher`] of this process's own executable: the launcher a
/// background client (the `dashboard` and `gateway` commands, the TUI's
/// relaunch of a lost daemon) starts its daemon with.
///
/// # Errors
///
/// This process's executable path cannot be resolved.
pub(crate) fn own_launcher(socket_path: &Path, spawn_cwd: &Path) -> Result<ProcessLauncher> {
    let exe = std::env::current_exe().context("resolve the eukhe executable")?;
    Ok(cli_launcher(&exe, socket_path, spawn_cwd))
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
/// build, TS parity): an interactive start
/// ([`ProcessLauncher::ensure_interactive`], with the CLI's takeover) or a
/// background one ([`ProcessLauncher::ensure_background`]).
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
    let launcher = cli_launcher(exe, socket_path, spawn_cwd);
    match caller {
        Caller::Interactive => launcher.ensure_interactive(client, &CliTakeover).await,
        Caller::Background => launcher.ensure_background(client).await,
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
        None if socket_released(socket_path, shutdown_wait()).await => Ok(()),
        None => Err(anyhow!(
            "{why}, and the process holding {} could not be identified. Run: {}, then retry the original command.",
            socket_path.display(),
            shutdown_command(socket_path)
        )),
    }
}
