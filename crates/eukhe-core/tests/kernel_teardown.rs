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
//! The kernel Python is this checkout's runtime
//! (`eukhe-core/tests/support/kernel_runtime.rs`).

use std::sync::{Mutex, MutexGuard};

#[path = "support/process_watch.rs"]
mod process_watch;
use process_watch::await_process_gone;

#[path = "support/kernel_runtime.rs"]
mod kernel_runtime;
use kernel_runtime::kernel_python;

/// The tests share one process (the process-table scans must see only the
/// current test's kernel), so this std lock serializes them; they are the
/// only contenders, so holding it across awaits is safe.
static TEST_LOCK: Mutex<()> = Mutex::new(());

fn test_lock() -> MutexGuard<'static, ()> {
    TEST_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
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

fn test_options() -> eukhe_core::kernel::shared::KernelManagerOptions {
    let python = kernel_python();
    eukhe_core::kernel::shared::KernelManagerOptions {
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
        transport: eukhe_core::kernel::KernelTransport::Local,
        kept_credentials: eukhe_core::kernel::shared::KeptCredentials::default(),
    }
}

/// Dropping the last manager handle tears the kernel process down: no
/// explicit shutdown call, no reliance on the runtime's owner watchdog.
#[tokio::test]
#[allow(clippy::await_holding_lock)]
async fn manager_drop_kills_the_kernel_process() {
    let _guard = test_lock();
    let options = test_options();
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
    let python = kernel_python();
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
