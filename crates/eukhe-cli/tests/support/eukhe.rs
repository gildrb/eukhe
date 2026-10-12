//! The one place the e2e tests build an `eukhe` process.

use std::process::Command;

#[path = "../../../eukhe-core/tests/support/kernel_runtime.rs"]
mod kernel_runtime;

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
