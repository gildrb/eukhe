//! `eukhe kernel install [--check]` and `eukhe kernel lock <requirement>...`.
//!
//! The kernel runs on one pinned Python that Eukhe fetches itself the
//! first time a kernel is needed, so `install` is never required: it does
//! the same fetch now (before going offline, or to show its progress in a
//! setup script). `--check` reports the state on disk without network.
//! `lock` adds packages to the project's lock, the only way a kernel
//! installs a package outside Eukhe's own lock.

use eukhe_core::kernel::{
    ensure_kernel_python, kernel_state, lock_project_packages, pinned_python_version,
    unused_kernel_venv, EnsureKernelPythonOptions, KernelFetchState,
};

use crate::config::APP_NAME;

/// Run the `kernel` command; returns the process exit code.
pub fn run_kernel_command(args: &[String]) -> i32 {
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match args.as_slice() {
        ["install"] => install(),
        ["install", "--check"] => check(),
        ["lock", requirements @ ..]
            if !requirements.is_empty() && requirements.iter().all(|arg| !arg.starts_with('-')) =>
        {
            lock(requirements)
        }
        _ => {
            eprintln!(
                "Error: Usage: {APP_NAME} kernel install [--check] | {APP_NAME} kernel lock <requirement>..."
            );
            eprintln!("Run \"eukhe help kernel\" for usage.");
            2
        }
    }
}

fn async_runtime() -> Option<tokio::runtime::Runtime> {
    match tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => Some(runtime),
        Err(error) => {
            eprintln!("Error: cannot start the async runtime: {error}");
            None
        }
    }
}

/// Each stage of a fetch, as a line on stdout.
fn progress() -> EnsureKernelPythonOptions {
    EnsureKernelPythonOptions {
        python_skills: Vec::new(),
        on_progress: Some(std::sync::Arc::new(|message: &str| println!("{message}"))),
    }
}

/// Prints `ready: <python> (Python <version>)` and exits 0 when a kernel
/// starts at once; `not fetched: ...` and exits 1 when the first kernel
/// start (or `eukhe kernel install`) has to fetch the Python first. No
/// network request.
fn check() -> i32 {
    let cwd = std::env::current_dir().ok();
    match kernel_state(cwd.as_deref()) {
        Ok(KernelFetchState::Ready(kernel)) => {
            println!("ready: {}", kernel.describe());
            0
        }
        Ok(KernelFetchState::NotFetched) => {
            println!(
                "not fetched: Python {} is fetched at the first kernel start, or now with `{APP_NAME} kernel install`",
                pinned_python_version()
            );
            1
        }
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}

/// Fetches what is absent of the pinned toolchain; one that is all there
/// is kept as it is. Each stage is a line on stdout; the last line is
/// `ready: <python> (Python <version>)`.
fn install() -> i32 {
    let Some(runtime) = async_runtime() else {
        return 1;
    };
    let cwd = std::env::current_dir().ok();
    match runtime.block_on(ensure_kernel_python(progress(), cwd.as_deref())) {
        Ok(kernel) => {
            if let Some(old) = unused_kernel_venv() {
                println!(
                    "unused: {} (the kernel env of earlier versions) can be deleted",
                    old.display()
                );
            }
            println!("ready: {}", kernel.describe());
            0
        }
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}

/// Adds the requirements to the lock of the project in the current
/// directory.
fn lock(requirements: &[&str]) -> i32 {
    let Some(runtime) = async_runtime() else {
        return 1;
    };
    let cwd = match std::env::current_dir() {
        Ok(cwd) => cwd,
        Err(error) => {
            eprintln!("Error: cannot read the current directory: {error}");
            return 1;
        }
    };
    let requirements: Vec<String> = requirements.iter().map(ToString::to_string).collect();
    let report = |message: &str| println!("{message}");
    match runtime.block_on(lock_project_packages(&cwd, &requirements, &report)) {
        Ok(change) if change.added.is_empty() => {
            println!(
                "already locked: nothing to add to {}",
                change.lock.display()
            );
            0
        }
        Ok(change) => {
            for package in &change.added {
                println!("locked: {package}");
            }
            println!("wrote {}", change.lock.display());
            0
        }
        Err(error) => {
            eprintln!("Error: {error:#}");
            1
        }
    }
}
