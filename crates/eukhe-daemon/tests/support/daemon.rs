//! The one place the e2e tests build an `eukhe-daemon` process.

use std::process::Command;

#[path = "../../../eukhe-core/tests/support/kernel_runtime.rs"]
mod kernel_runtime;

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
