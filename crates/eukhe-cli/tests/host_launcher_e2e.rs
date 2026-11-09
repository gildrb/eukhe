//! A host that bundles the engine starts it the way the CLI does, without
//! linking the CLI: eukhe-client's `ProcessLauncher` runs
//! `eukhe-daemon supervisor --socket <p> --agent-dir <d>` detached (null
//! stdin and stdout, stderr a startup pipe the daemon lets go of once it
//! serves, a new session), waits until it greets, and a second start keeps
//! the daemon that serves.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use eukhe_client::daemon_build::Build;
use eukhe_client::daemon_client::DaemonClient;
use eukhe_client::launcher::{socket_released, DaemonReady, ProcessLauncher};
use eukhe_daemon::worker::{
    WORKER_ACTIVE_SESSION_ID_ENV, WORKER_INSTANCE_ID_ENV, WORKER_RECOVERY_JOURNAL_ENV,
    WORKER_ROLE_ENV, WORKER_SCRIPT_ENV, WORKER_SOCKET_ENV, WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
    WORKER_SUPERVISOR_SOCKET_ENV, WORKER_TOKEN_ENV,
};
use eukhe_types::daemon::DaemonCommand;

#[path = "support/eukhe.rs"]
mod eukhe;

/// The built `eukhe-daemon` next to this crate's `eukhe` binary (Cargo
/// builds the bins of the crate under test only: the workspace gate builds
/// it, else `cargo build -p eukhe-daemon`).
fn daemon_binary() -> PathBuf {
    let daemon = Path::new(env!("CARGO_BIN_EXE_eukhe"))
        .with_file_name(format!("eukhe-daemon{}", std::env::consts::EXE_SUFFIX));
    assert!(
        daemon.exists(),
        "eukhe-daemon binary not found at {}; run `cargo build -p eukhe-daemon` first",
        daemon.display()
    );
    daemon
}

/// The host's supervisor command: the bundled daemon on `socket` over
/// `agent_dir`. A supervisor left behind by a failed test must not leak
/// session workers: they exit on the short supervisor-lost window.
fn host_command(socket: &Path, agent_dir: &Path) -> Command {
    let mut command = Command::new(daemon_binary());
    eukhe::eukhe_env(&mut command)
        .arg("supervisor")
        .arg("--socket")
        .arg(socket)
        .arg("--agent-dir")
        .arg(agent_dir)
        .env("EUKHE_CODING_AGENT_DIR", agent_dir)
        .env(WORKER_SUPERVISOR_LOST_EXIT_MS_ENV, "15000");
    for var in [
        WORKER_ROLE_ENV,
        WORKER_TOKEN_ENV,
        WORKER_ACTIVE_SESSION_ID_ENV,
        WORKER_RECOVERY_JOURNAL_ENV,
        WORKER_SUPERVISOR_SOCKET_ENV,
        WORKER_SOCKET_ENV,
        WORKER_INSTANCE_ID_ENV,
        WORKER_SCRIPT_ENV,
    ] {
        command.env_remove(var);
    }
    command
}

#[tokio::test]
async fn a_host_launches_its_bundled_daemon_and_then_keeps_it() {
    let dir = tempfile::tempdir().expect("temp dir");
    let socket = dir.path().join("d.sock");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let launcher =
        ProcessLauncher::new(host_command(&socket, &agent_dir), &socket, "quit the host");

    let first = launcher.ensure_background(Build::THIS).await;
    let second = launcher.ensure_background(Build::THIS).await;

    // Teardown: the detached supervisor outlives this test unless told to
    // stop. It may close the connection before it answers, so the socket's
    // release is the evidence, not the answer.
    let (client, _events) = DaemonClient::connect(&socket)
        .await
        .expect("connect the launched daemon");
    let _answer = client
        .request(DaemonCommand::Shutdown {
            id: None,
            force: Some(true),
            if_idle: None,
            rest: serde_json::Map::default(),
        })
        .await;
    client.close();
    let released = socket_released(&socket, Duration::from_secs(30)).await;

    assert_eq!(
        (
            first.map_err(|error| format!("{error:#}")),
            second.map_err(|error| format!("{error:#}")),
            released,
        ),
        (Ok(DaemonReady::Current), Ok(DaemonReady::Current), true)
    );
}
