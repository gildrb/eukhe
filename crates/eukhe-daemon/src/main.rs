//! `eukhe-daemon`: supervisor and session-worker binary.

use std::path::PathBuf;

use anyhow::{anyhow, Result};

// Same allocator as the eukhe binary: mimalloc returns freed pages to the
// OS, so large transient phases (session loads, attach snapshots) do not
// stay resident (it replaces the glibc mallopt/malloc_trim tuning, which
// had no safe binding).
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[tokio::main]
async fn main() -> Result<()> {
    let mut args = std::env::args().skip(1);
    let command = args.next().unwrap_or_else(|| {
        eprintln!("usage: eukhe-daemon <supervisor|worker> [options]");
        std::process::exit(2);
    });
    match command.as_str() {
        "supervisor" => {
            let mut socket_path = None;
            let mut agent_dir = None;
            let mut args = args.peekable();
            while let Some(arg) = args.next() {
                match arg.as_str() {
                    "--socket" => socket_path = args.next().map(PathBuf::from),
                    "--agent-dir" => agent_dir = args.next().map(PathBuf::from),
                    other => return Err(anyhow!("unknown supervisor option: {other}")),
                }
            }
            let agent_dir = match agent_dir {
                Some(dir) => dir,
                None => eukhe_daemon::paths::agent_dir()?,
            };
            let options = eukhe_daemon::supervisor::SupervisorOptions {
                socket_path: socket_path
                    .unwrap_or_else(eukhe_daemon::socket::default_daemon_socket_path),
                agent_dir,
            };
            eukhe_daemon::supervisor::run_supervisor(options).await
        }
        "worker" => eukhe_daemon::worker::run_worker().await,
        other => Err(anyhow!(
            "unknown command: {other} (expected supervisor|worker)"
        )),
    }
}
