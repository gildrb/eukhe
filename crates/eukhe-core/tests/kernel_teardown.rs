// The Tier-C/D ruling (fleet-uniform, 2026-09-28) - this target's own
// crate root: the same bounded-boundary disposition as src/lib.rs
// (large_futures/too_many_lines/the cast family; details there).
#![allow(
    clippy::large_futures,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]

//! Verifier integration tests for kernel process teardown on drop (#232
//! close-out hygiene): a session or harness that boots a kernel and then
//! simply drops its handles must not leave the `python -m rlm.repl` process
//! alive. The reader/watcher tasks used to hold strong manager references
//! while blocked on the child's pipes, so `Inner::drop`'s kill never fired
//! without an explicit shutdown — kernels then lived until the runtime's
//! owner watchdog reaped them, if ever, accumulating across cargo test runs.
//!
//! The kernel Python is ambient product state (the auto-bootstrapped kernel
//! venv); like `kernel_lifecycle.rs`, these tests skip (with a note) on
//! machines without a live install so the suite stays hermetic elsewhere.

use std::path::PathBuf;
use std::sync::{Mutex, MutexGuard};
use std::time::{Duration, Instant};

/// The tests share one process (the process-table scans must see only the
/// current test's kernel), so this std lock serializes them; they are the
/// only contenders, so holding it across awaits is safe.
static TEST_LOCK: Mutex<()> = Mutex::new(());

fn test_lock() -> MutexGuard<'static, ()> {
    TEST_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// The kernel Python with eukhe-runtime installed; set
/// `EUKHE_CORE_KERNEL_PYTHON` to point at an explicit interpreter instead.
///
/// The interpreter is also handed to the session engine as
/// `EUKHE_KERNEL_PYTHON` (once, before any test of this binary touches a
/// kernel): without it the engine's managed-venv path re-derives the venv
/// from the runtime source, which a test binary built outside the source
/// checkout (`CARGO_TARGET_DIR` elsewhere) cannot find.
fn kernel_python() -> Option<PathBuf> {
    static EXPORT: std::sync::Once = std::sync::Once::new();
    let python = find_kernel_python()?;
    EXPORT.call_once(|| std::env::set_var("EUKHE_KERNEL_PYTHON", &python));
    Some(python)
}

fn find_kernel_python() -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os("EUKHE_CORE_KERNEL_PYTHON") {
        let explicit = PathBuf::from(explicit);
        assert!(
            explicit.exists(),
            "EUKHE_CORE_KERNEL_PYTHON {} not found",
            explicit.display()
        );
        return Some(explicit);
    }
    let home = std::env::var("HOME").unwrap_or_default();
    let candidate = PathBuf::from(format!("{home}/.eukhe/kernel-venv/bin/python"));
    if candidate.exists() {
        return Some(candidate);
    }
    eprintln!(
        "kernel python {} not found; skipping live teardown test",
        candidate.display()
    );
    None
}

/// True while a live (non-zombie) process with this pid exists.
fn process_alive(pid: i32) -> bool {
    if pid <= 0 {
        return false;
    }
    std::fs::read_to_string(format!("/proc/{pid}/stat"))
        .ok()
        .and_then(|raw| {
            // pid (comm) state ...
            let close = raw.rfind(')')?;
            raw[close + 1..]
                .trim_start()
                .chars()
                .next()
                .map(|state| state != 'Z' && state != 'X')
        })
        .unwrap_or(false)
}

/// Poll until the pid leaves the live-process table (teardown kills are
/// synchronous, but the kernel may be mid-boot when its owner drops, so the
/// settle budget covers the boot finishing first).
async fn await_process_gone(pid: i32) {
    let deadline = Instant::now() + Duration::from_mins(1);
    while process_alive(pid) {
        assert!(
            Instant::now() < deadline,
            "kernel pid {pid} outlived the drop of its owner (teardown gap)"
        );
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
}

/// Start a manager and run the RLM bootstrap, mirroring the TS provisioner
/// contract (start, then the bootstrap cell must be `ok`).
async fn started_manager(
    options: eukhe_core::kernel::shared::KernelManagerOptions,
) -> eukhe_core::kernel::manager::ReplKernelManager {
    let bootstrap = options
        .bootstrap_code
        .clone()
        .expect("tests always pass the RLM bootstrap");
    let manager = eukhe_core::kernel::manager::ReplKernelManager::new(options);
    manager
        .start(eukhe_core::kernel::manager::KernelStartOptions::default())
        .await
        .expect("kernel must start");
    let result = manager
        .execute(
            &bootstrap,
            eukhe_core::kernel::shared::ExecuteOptions::default(),
        )
        .await
        .expect("bootstrap execute must not fail");
    assert_eq!(
        result.status,
        eukhe_core::kernel::shared::ExecuteStatus::Ok,
        "rlm runtime bootstrap failed: {}",
        result.stderr
    );
    manager
}

fn test_options() -> Option<eukhe_core::kernel::shared::KernelManagerOptions> {
    let python = kernel_python()?;
    Some(eukhe_core::kernel::shared::KernelManagerOptions {
        python: Some(python),
        cwd: Some(std::env::temp_dir()),
        env: std::collections::HashMap::default(),
        session_id: Some("teardown-test".to_string()),
        host_handlers: eukhe_core::kernel::shared::HostRequestHandlers::default(),
        python_skills: Vec::new(),
        on_background_work_settled: None,
        snapshot: None,
        bootstrap_code: Some(eukhe_core::kernel::bootstrap::build_rlm_bootstrap_code(&[])),
        stderr_log_path: None,
    })
}

/// Dropping the last manager handle tears the kernel process down: no
/// explicit shutdown call, no reliance on the runtime's owner watchdog.
#[tokio::test]
#[allow(clippy::await_holding_lock)]
async fn manager_drop_kills_the_kernel_process() {
    let _guard = test_lock();
    let Some(options) = test_options() else {
        return;
    };
    let manager = started_manager(options).await;
    let pid = manager.process_id().expect("kernel pid");
    drop(manager);
    await_process_gone(pid).await;
}

/// The session-level seam: dropping the provisioner drops the memoized
/// manager and the kernel goes with it.
#[tokio::test]
#[allow(clippy::await_holding_lock)]
async fn provisioner_drop_kills_the_kernel_process() {
    let _guard = test_lock();
    let Some(python) = kernel_python() else {
        return;
    };
    let options = eukhe_core::kernel::provisioner::IpythonKernelProvisionerOptions {
        python: Some(python),
        ..Default::default()
    };
    let provisioner =
        eukhe_core::kernel::provisioner::IpythonKernelProvisioner::new("/tmp", options);
    let manager = provisioner
        .ensure(None, None)
        .await
        .expect("kernel must boot");
    let pid = manager.process_id().expect("kernel pid");
    drop(manager);
    drop(provisioner);
    await_process_gone(pid).await;
}
