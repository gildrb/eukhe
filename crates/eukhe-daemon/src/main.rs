//! `eukhe-daemon`: the whole engine image. It serves the supervisor, the
//! session workers it spawns (`worker`), and the shared tiny-model workers
//! those sessions spawn (`tiny-worker`, the same entry `eukhe tiny-worker`
//! runs), so a host that bundles only this binary runs every process of
//! the engine.

use std::path::PathBuf;
use std::process::ExitCode;

use anyhow::{anyhow, Context as _, Result};

// Same allocator as the eukhe binary: mimalloc returns freed pages to the
// OS, so large transient phases (session loads, attach snapshots) do not
// stay resident (it replaces the glibc mallopt/malloc_trim tuning, which
// had no safe binding).
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> Result<ExitCode> {
    // A launcher that asked for a detached session (eukhe-client's
    // `ProcessLauncher`) gets it before anything else runs, while the
    // process is still single-threaded.
    eukhe_core::platform::process::enter_requested_session().context("start a new session")?;
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .context("start the async runtime")?
        .block_on(run())
}

async fn run() -> Result<ExitCode> {
    let mut args = std::env::args().skip(1);
    let command = args.next().unwrap_or_else(|| {
        eprintln!("usage: eukhe-daemon <supervisor|worker|tiny-worker> [options]");
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
            eukhe_daemon::supervisor::run_supervisor(options)
                .await
                .map(|()| ExitCode::SUCCESS)
        }
        "worker" => eukhe_daemon::worker::run_worker()
            .await
            .map(|()| ExitCode::SUCCESS),
        // The shared worker of one tiny model (spawned by the tiny client,
        // never by hand), with the ONNX engine.
        "tiny-worker" => {
            let args: Vec<String> = args.collect();
            Ok(eukhe_tiny::run_worker(&args, eukhe_tiny_onnx::open).await)
        }
        other => Err(anyhow!(
            "unknown command: {other} (expected supervisor|worker|tiny-worker)"
        )),
    }
}
