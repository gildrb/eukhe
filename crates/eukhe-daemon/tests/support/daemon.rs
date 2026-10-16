//! The one place the e2e tests build an `eukhe-daemon` process.

#![allow(dead_code)] // each including test binary uses its own subset

use std::path::Path;
use std::process::{Command, Stdio};

#[path = "../../../eukhe-core/tests/support/kernel_runtime.rs"]
pub mod kernel_runtime;

/// A command for the cargo-built `eukhe-daemon` binary.
pub fn daemon_command() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_eukhe-daemon"));
    daemon_env(&mut command);
    command
}

/// The environment every test daemon gets, for a command that runs the
/// daemon some other way (a launcher, a private copy of the binary). Its
/// sessions prewarm kernels on this checkout's runtime: without the
/// interpreter they would bootstrap the user's `~/.eukhe/kernel-venv`.
pub fn daemon_env(command: &mut Command) -> &mut Command {
    command.env("EUKHE_KERNEL_PYTHON", kernel_runtime::kernel_python())
}

/// `eukhe-daemon supervisor --socket <socket> --agent-dir <agent_dir>` on
/// the cargo-built binary, every stdio stream null.
pub fn supervisor_command(socket: &Path, agent_dir: &Path) -> Command {
    let mut command = daemon_command();
    supervisor_args(&mut command, socket, agent_dir);
    command
}

/// The supervisor arguments and null stdio, for a command that runs the
/// daemon some other way.
pub fn supervisor_args<'a>(
    command: &'a mut Command,
    socket: &Path,
    agent_dir: &Path,
) -> &'a mut Command {
    command
        .arg("supervisor")
        .arg("--socket")
        .arg(socket)
        .arg("--agent-dir")
        .arg(agent_dir)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
}
