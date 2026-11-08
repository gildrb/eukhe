//! The daemon-ensure concern: the CLI's supervisor command
//! (`eukhe --mode daemon --daemon-socket <p>`, run by
//! [`eukhe_client::launcher::ProcessLauncher`], which probes the socket and
//! applies the replacement verdict), how long the supervisor it starts
//! lives ([`SupervisorLife`]), the `eukhe shutdown` hint its errors name,
//! and the CLI's socket takeover (stopping this user's eukhe supervisor
//! that holds the socket).

use std::future::Future;

use anyhow::Context as _;
use eukhe_client::daemon_build::{Build, Caller};
use eukhe_client::launcher::{
    socket_released, DaemonReady, Launched, ProcessLauncher, SocketTakeover,
};
use eukhe_daemon::timeouts;

use super::{anyhow, Command, Duration, Path, Result};

/// How a supervisor that [`ensure_daemon`] starts relates to the caller's
/// life.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SupervisorLife {
    /// It outlives the caller (the shared daemon every client starts).
    Detached,
    /// It drains and exits when this process exits, however it ends (a
    /// crash or a kill included): its stdin is a pipe whose only write end
    /// this process holds ([`OWNED_SUPERVISORS`],
    /// [`crate::daemon_mode::DAEMON_OWNER_STDIN_ENV`]).
    Caller,
}

/// Who started the supervisor [`ensure_daemon`] left on the socket.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Launch {
    /// It was there already, or another launcher's won the socket: this
    /// process never stops it.
    Found,
    /// This call started it (process `pid`).
    Started { pid: u32 },
}

/// The supervisors this process started with [`SupervisorLife::Caller`],
/// held for the life of the process: each handle keeps its supervisor's
/// stdin pipe open, and the process's exit closes them all.
static OWNED_SUPERVISORS: std::sync::LazyLock<std::sync::Mutex<Vec<std::process::Child>>> =
    std::sync::LazyLock::new(std::sync::Mutex::default);

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
/// `spawn_cwd`, living as `life` says. The spawned supervisor never
/// inherits a worker's or supervisor's role variables: a CLI running inside
/// a daemon worker would otherwise launch a supervisor that starts in
/// worker mode (it listens but never handshakes), and an inherited lease
/// owner id would name a stale session in every lease its workers write
/// (the TS launcher deletes the same set). A [`SupervisorLife::Caller`]
/// supervisor is marked ([`crate::daemon_mode::DAEMON_OWNER_STDIN_ENV`]) to
/// drain when its stdin pipe closes; a detached one never inherits the
/// mark. Before a spawn the launcher runs the supervisor's own socket-dir
/// check: the supervisor's stderr goes nowhere, so a refused socket dir
/// would surface only as a startup timeout.
#[must_use]
pub(crate) fn cli_launcher(
    exe: &Path,
    socket_path: &Path,
    spawn_cwd: &Path,
    life: SupervisorLife,
) -> ProcessLauncher {
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
    match life {
        SupervisorLife::Detached => command.env_remove(crate::daemon_mode::DAEMON_OWNER_STDIN_ENV),
        SupervisorLife::Caller => command.env(crate::daemon_mode::DAEMON_OWNER_STDIN_ENV, "1"),
    };
    let launcher = ProcessLauncher::new(command, socket_path, shutdown_command(socket_path))
        .with_spawn_check(eukhe_daemon::platform::check_daemon_socket_dir);
    match life {
        SupervisorLife::Detached => launcher,
        SupervisorLife::Caller => launcher.tied_to_caller(),
    }
}

/// [`cli_launcher`] of this process's own executable, for a detached
/// supervisor: the launcher a background client (the `dashboard` and
/// `gateway` commands, the TUI's relaunch of a lost daemon) starts its
/// daemon with.
///
/// # Errors
///
/// This process's executable path cannot be resolved.
pub(crate) fn own_launcher(socket_path: &Path, spawn_cwd: &Path) -> Result<ProcessLauncher> {
    let exe = std::env::current_exe().context("resolve the eukhe executable")?;
    Ok(cli_launcher(
        &exe,
        socket_path,
        spawn_cwd,
        SupervisorLife::Detached,
    ))
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

/// [`ensure_daemon`] for a supervisor that outlives the caller (the TS
/// `ensureDaemonRunning` the integration tests drive).
///
/// # Errors
///
/// See [`ensure_daemon`].
pub async fn ensure_daemon_running_with(
    exe: &Path,
    client: Build<'_>,
    socket_path: &Path,
    spawn_cwd: &Path,
    caller: Caller,
) -> Result<DaemonReady> {
    ensure_daemon(
        exe,
        client,
        socket_path,
        spawn_cwd,
        caller,
        SupervisorLife::Detached,
    )
    .await
    .map(|(ready, _launch)| ready)
}

/// Ensure a daemon is listening on `socket_path`, spawning `exe` as the
/// supervisor (living as `life` says) when none is, with an explicit client
/// build (the product path uses this process's own binary and build, TS
/// parity); also reports whether this call started it. An interactive
/// start ([`ProcessLauncher::launch_interactive`], with the CLI's
/// takeover) or a background one ([`ProcessLauncher::launch_background`]).
///
/// # Errors
/// Returns an error when an incompatible daemon is kept (newer than the
/// client, started by a background client, or busy), when a foreign holder
/// of the socket cannot or may not be stopped, when the supervisor would
/// refuse the socket dir, when the supervisor process cannot be spawned, or
/// when no daemon starts before the startup timeout.
pub(crate) async fn ensure_daemon(
    exe: &Path,
    client: Build<'_>,
    socket_path: &Path,
    spawn_cwd: &Path,
    caller: Caller,
    life: SupervisorLife,
) -> Result<(DaemonReady, Launch)> {
    let launcher = cli_launcher(exe, socket_path, spawn_cwd, life);
    let Launched { ready, spawned } = match caller {
        Caller::Interactive => launcher.launch_interactive(client, &CliTakeover).await?,
        Caller::Background => launcher.launch_background(client).await?,
    };
    // Only the supervisor this call spawned is the caller's own.
    let launch = match spawned {
        None => Launch::Found,
        Some(supervisor) => {
            let pid = supervisor.id();
            match life {
                SupervisorLife::Caller => OWNED_SUPERVISORS
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .push(supervisor),
                SupervisorLife::Detached => drop(supervisor),
            }
            Launch::Started { pid }
        }
    };
    Ok((ready, launch))
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

#[cfg(test)]
mod tests {
    use std::os::unix::fs::PermissionsExt as _;

    use super::*;

    /// A socket dir the supervisor would refuse fails the launch with the
    /// supervisor's own refusal, before any spawn (the executable here does
    /// not exist), never as a startup timeout.
    #[tokio::test]
    async fn a_refused_socket_dir_fails_with_its_reason_not_a_timeout() {
        let home = tempfile::tempdir().expect("tempdir");
        let open = home.path().join("open");
        std::fs::create_dir(&open).expect("dir");
        std::fs::set_permissions(&open, std::fs::Permissions::from_mode(0o777)).expect("chmod");
        let socket = open.join("daemon.sock");
        let Err(error) = ensure_daemon(
            &home.path().join("no-such-eukhe"),
            Build::THIS,
            &socket,
            home.path(),
            Caller::Interactive,
            SupervisorLife::Detached,
        )
        .await
        else {
            panic!("the launch went ahead");
        };
        let uid = eukhe_types::platform::access::current_uid();
        assert_eq!(
            error.to_string(),
            format!(
                "the socket dir {} has mode 0777, so other users can replace its sockets. \
                 eukhe binds its sockets only in a real directory that uid {uid} owns and that \
                 no other user can write. Remove that path (or, if it is your own directory, run \
                 `chmod go-w` on it), or pass --daemon-socket with a path in a private directory.",
                open.display()
            )
        );
    }
}
