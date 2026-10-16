//! The one place the e2e tests build an `eukhe` process.

#![allow(dead_code)] // each including test binary uses its own subset

use std::path::Path;
use std::process::{Command, Stdio};

use eukhe_daemon::worker::{
    WORKER_ACTIVE_SESSION_ID_ENV, WORKER_INSTANCE_ID_ENV, WORKER_RECOVERY_JOURNAL_ENV,
    WORKER_ROLE_ENV, WORKER_SCRIPT_ENV, WORKER_SOCKET_ENV, WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
    WORKER_SUPERVISOR_SOCKET_ENV, WORKER_TOKEN_ENV,
};

#[path = "../../../eukhe-core/tests/support/kernel_runtime.rs"]
pub mod kernel_runtime;

/// A command for the cargo-built `eukhe` binary.
pub fn eukhe_command() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_eukhe"));
    eukhe_env(&mut command);
    command
}

/// The environment every test `eukhe` (and the daemon it starts) gets, for
/// a command that runs a binary passed in as a path. Its sessions prewarm
/// kernels on this checkout's runtime: without the interpreter they would
/// bootstrap the user's `~/.eukhe/kernel-venv`.
pub fn eukhe_env(command: &mut Command) -> &mut Command {
    command.env("EUKHE_KERNEL_PYTHON", kernel_runtime::kernel_python())
}

/// `--mode daemon --daemon-socket <socket>` over `agent_dir`, every stdio
/// stream null. The launcher strips inherited worker role env vars before
/// spawning the supervisor (a CLI running inside a daemon worker must not
/// leak them, and this test process may itself be one), and a supervisor
/// killed at teardown must not leak its session workers into later test
/// binaries: the worker's supervisor-lost exit (TS
/// `exitIfSupervisorOrphanedForTooLong`) runs on a short window instead of
/// the 5-minute default.
pub fn daemon_mode_args<'a>(
    command: &'a mut Command,
    socket: &Path,
    agent_dir: &Path,
) -> &'a mut Command {
    command
        .args(["--mode", "daemon", "--daemon-socket"])
        .arg(socket)
        .env("EUKHE_CODING_AGENT_DIR", agent_dir)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
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
    command.env(WORKER_SUPERVISOR_LOST_EXIT_MS_ENV, "15000")
}

/// Strip every builtin provider's key variables: ambient provider
/// credentials must not leak into the daemon's catalog (the supervisor's
/// session workers inherit its environment).
pub fn scrub_provider_keys(command: &mut Command) -> &mut Command {
    for provider in eukhe_ai::providers::all::builtin_providers() {
        let set = eukhe_ai::env_api_keys::find_env_keys(&provider.id, None);
        for var in set.unwrap_or_default() {
            command.env_remove(var);
        }
    }
    command
}
