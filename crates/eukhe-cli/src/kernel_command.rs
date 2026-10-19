//! `eukhe kernel install [--check]`: install the Python kernel's
//! environment (a uv-managed Python and the hash-locked kernel packages)
//! once. This command is the only path that downloads them; a session
//! uses the installed kernel and never downloads. `--check` reports the
//! state without network.

use eukhe_core::kernel::{
    install_kernel_python, kernel_install_state, EnsureKernelPythonOptions, KernelInstallState,
};

use crate::config::APP_NAME;

/// Run the `kernel` command; returns the process exit code.
pub fn run_kernel_command(args: &[String]) -> i32 {
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match args.as_slice() {
        ["install"] => install(),
        ["install", "--check"] => check(),
        _ => {
            eprintln!("Usage: {APP_NAME} kernel install [--check]");
            1
        }
    }
}

/// Prints the kernel state; exit 0 only when a session can start the
/// kernel as it is.
fn check() -> i32 {
    match kernel_install_state() {
        Ok(KernelInstallState::Override(python)) => {
            println!(
                "EUKHE_KERNEL_PYTHON is set: the kernel uses {} and eukhe installs nothing",
                python.display()
            );
            0
        }
        Ok(KernelInstallState::Installed(python)) => {
            println!("installed: {}", python.display());
            0
        }
        Ok(KernelInstallState::OutOfDate(venv)) => {
            println!(
                "out of date: {} is not for this build; a session sets it up again from local files if it can, else run `{APP_NAME} kernel install`",
                venv.display()
            );
            1
        }
        Ok(KernelInstallState::Missing(venv)) => {
            println!(
                "not installed: run `{APP_NAME} kernel install` (it goes in {})",
                venv.display()
            );
            1
        }
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}

/// Installs the kernel environment; an installed one is kept as it is.
fn install() -> i32 {
    if let Ok(KernelInstallState::Installed(python)) = kernel_install_state() {
        println!("already installed: {}", python.display());
        return 0;
    }
    let runtime = match tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            eprintln!("Error: cannot start the async runtime: {error}");
            return 1;
        }
    };
    match runtime.block_on(install_kernel_python(EnsureKernelPythonOptions::default())) {
        Ok(python) => {
            println!("installed: {}", python.display());
            0
        }
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}
