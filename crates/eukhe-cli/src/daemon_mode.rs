//! `--mode daemon`: the supervisor process. The interactive client spawns
//! this mode (detached) when no daemon is listening, so `eukhe` alone
//! is enough to bring the full session stack up (port of the TS
//! `daemon-mode.ts` entry: the CLI process becomes the supervisor).
//!
//! A supervisor started for one headless client's subagents lives only as
//! long as that client ([`DAEMON_OWNER_STDIN_ENV`]).

use std::io::Read as _;

use anyhow::{Context as _, Result};

use crate::config;

/// Set (to `1`) on a supervisor whose stdin is a pipe from the client that
/// started it, the only holder of its write end: when the pipe reaches
/// end of file (the client exited, normally, on an error, or killed), the
/// supervisor raises SIGTERM on itself and drains like any terminated
/// supervisor: running turns settle, the workers retire, it exits.
pub(crate) const DAEMON_OWNER_STDIN_ENV: &str = "EUKHE_DAEMON_OWNER_STDIN";

/// Run the daemon supervisor in-process until it shuts down.
pub fn run_daemon_mode(daemon_socket: Option<&str>) -> Result<i32> {
    if std::env::var_os(DAEMON_OWNER_STDIN_ENV).is_some() {
        // The marker names this process's own launch: its workers, and
        // anything they start, never inherit it.
        std::env::remove_var(DAEMON_OWNER_STDIN_ENV);
        std::thread::Builder::new()
            .name("owner-stdin".to_string())
            .spawn(|| {
                let mut sink = [0_u8; 64];
                let mut stdin = std::io::stdin().lock();
                loop {
                    match stdin.read(&mut sink) {
                        Ok(0) => break,
                        Ok(_) => {}
                        Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
                        Err(error) => {
                            eprintln!("eukhe daemon: the owner pipe broke ({error}); draining");
                            break;
                        }
                    }
                }
                let pid = i32::try_from(std::process::id()).unwrap_or_default();
                if !eukhe_core::platform::process::kill_pid(
                    pid,
                    eukhe_core::platform::process::Signal::Term,
                ) {
                    eprintln!("eukhe daemon: the owner left, but SIGTERM to itself failed");
                }
            })
            .context("start the owner-pipe watch")?;
    }
    let socket_path = config::resolve_daemon_socket_path(daemon_socket);
    let agent_dir = config::get_agent_dir();
    let options = eukhe_daemon::supervisor::SupervisorOptions {
        socket_path,
        agent_dir,
    };
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    runtime.block_on(eukhe_daemon::supervisor::run_supervisor(options))?;
    Ok(0)
}
