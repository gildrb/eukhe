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

//! Verifier integration tests: spawn a real `python -m rlm.repl` kernel
//! (the same JSON-lines protocol v3 runtime the TS product ships) through
//! `ReplKernelManager`, and check the persistence/revival semantics against
//! the TS product's behavior contract:
//!
//! - state persists across cells and turns;
//! - kill -9 the kernel, restart a fresh manager on the same snapshot, and
//!   the namespace revives: serializable variables return, unserializable
//!   objects are dropped and reported;
//! - the RLM surface (rlm, bash, harness) injected by the bootstrap exists
//!   and host requests round-trip to the registered handler.

use std::collections::HashMap;
use std::time::Duration;

use eukhe_core::kernel::bootstrap::build_rlm_bootstrap_code;
use eukhe_core::kernel::manager::{KernelStartOptions, ReplKernelManager};
use eukhe_core::kernel::shared::{
    ExecuteOptions, ExecuteStatus, HostRequestHandlers, KernelBashCommands, KernelManagerOptions,
    KernelShutdownOptions, KernelSnapshotConfig,
};
use eukhe_core::kernel::state_snapshot::{manifest_path_in, snapshot_path_in};

#[path = "support/kernel_runtime.rs"]
mod kernel_runtime;
use kernel_runtime::kernel_python;

/// Test options on this checkout's kernel runtime.
fn test_options(snapshot_dir: Option<&std::path::Path>) -> KernelManagerOptions {
    let python = kernel_python();
    KernelManagerOptions {
        python: Some(python),
        cwd: Some(std::env::temp_dir()),
        env: HashMap::new(),
        session_id: Some("integration-test".to_string()),
        host_handlers: HostRequestHandlers::new(),
        python_skills: Vec::new(),
        on_background_work_settled: None,
        snapshot: snapshot_dir.map(|dir| KernelSnapshotConfig {
            path: snapshot_path_in(dir),
            manifest_path: manifest_path_in(dir),
            max_bytes: None,
            max_variable_bytes: None,
            debounce_ms: None,
        }),
        // The TS provisioner (ipython.ts) always builds and executes the RLM
        // bootstrap after start; tests match that contract.
        bootstrap_code: Some(build_rlm_bootstrap_code(&[])),
        stderr_log_path: None,
    }
}

/// Start a manager and run the RLM bootstrap, mirroring the TS provisioner
/// (ipython.ts: start, then `m.execute(bootstrapCode)` must be `ok`).
async fn started_manager(options: KernelManagerOptions) -> ReplKernelManager {
    let bootstrap = options
        .bootstrap_code
        .clone()
        .expect("tests always pass the RLM bootstrap");
    let manager = ReplKernelManager::new(options);
    manager
        .start(KernelStartOptions::default())
        .await
        .expect("kernel must start");
    let result = manager
        .execute(&bootstrap, ExecuteOptions::default())
        .await
        .expect("bootstrap execute must not fail");
    assert_eq!(
        result.status,
        ExecuteStatus::Ok,
        "rlm runtime bootstrap failed: {}",
        result.stderr
    );
    manager
}

async fn execute(
    manager: &ReplKernelManager,
    code: &str,
) -> eukhe_core::kernel::shared::ExecuteResult {
    let result = manager
        .execute(code, ExecuteOptions::default())
        .await
        .expect("execute must not fail");
    result
}

#[tokio::test]
async fn kernel_state_persists_across_cells_and_turns() {
    let options = test_options(None);
    let manager = started_manager(options).await;

    // One turn defines; a separate call (a later "turn") uses.
    let first = execute(&manager, "x = 21\ny = 'hello'\nprint('defined')").await;
    assert_eq!(first.status, ExecuteStatus::Ok);
    assert_eq!(first.stdout.trim(), "defined");
    assert_eq!(
        first.result, None,
        "assignment cells produce no trailing result"
    );

    let second = execute(&manager, "x * 2").await;
    assert_eq!(second.status, ExecuteStatus::Ok);
    assert_eq!(
        second.result.as_deref(),
        Some("42"),
        "trailing expression repr is captured"
    );

    // _ is bound to the last trailing expression value.
    let third = execute(&manager, "_ + 1").await;
    assert_eq!(third.result.as_deref(), Some("43"));

    // await works at top level across turns.
    let fourth = execute(
        &manager,
        "import asyncio\nresult = await asyncio.sleep(0, 'done')\nresult",
    )
    .await;
    assert_eq!(fourth.result.as_deref(), Some("'done'"));

    // Error cells report ename/evalue/traceback, and state survives them.
    let error = execute(&manager, "1 / 0").await;
    assert_eq!(error.status, ExecuteStatus::Error);
    let kernel_error = error.error.expect("error cell carries the kernel error");
    assert_eq!(kernel_error.ename, "ZeroDivisionError");
    assert!(!kernel_error.traceback.is_empty());
    let after = execute(&manager, "x").await;
    assert_eq!(after.result.as_deref(), Some("21"));

    let shutdown = manager.shutdown(KernelShutdownOptions::default()).await;
    assert!(shutdown.is_ok());
}

#[tokio::test]
async fn project_modules_in_cwd_never_shadow_the_runtime_or_stdlib() {
    // Regression: `python -m rlm.repl` prepended the working directory to
    // `sys.path`, so a project's own `rlm/` or `json.py` ran at kernel boot.
    // Cells must still import project-only modules from the cwd, which the
    // runtime appends at the END of `sys.path`.
    let mut options = test_options(None);
    let project = tempfile::tempdir().expect("tempdir");
    let marker = project.path().join("shadow-imported");
    let shadow = format!(
        "open({:?}, 'w').close()\nraise SystemExit('shadowed')\n",
        marker.display().to_string()
    );
    std::fs::create_dir_all(project.path().join("rlm")).expect("mkdir");
    std::fs::write(project.path().join("rlm").join("__init__.py"), &shadow).expect("write");
    std::fs::write(project.path().join("json.py"), &shadow).expect("write");
    std::fs::write(project.path().join("csv.py"), &shadow).expect("write");
    std::fs::write(
        project.path().join("eukhe_project_probe.py"),
        "VALUE = 'project'\n",
    )
    .expect("write");
    options.cwd = Some(project.path().to_path_buf());
    let manager = started_manager(options).await;

    let probe = execute(
        &manager,
        "import os, sys, csv, json, rlm, eukhe_project_probe\ncwd = os.getcwd()\n(cwd, sys.path[-1] == cwd, '' in sys.path, [m.__file__.startswith(cwd) for m in (csv, json, rlm)], eukhe_project_probe.VALUE, eukhe_project_probe.__file__.startswith(cwd))",
    )
    .await;
    assert_eq!(probe.status, ExecuteStatus::Ok, "{}", probe.stderr);
    let cwd = project.path().canonicalize().expect("canonical cwd");
    assert_eq!(
        probe.result,
        Some(
            format!(
                "({:?}, True, False, [False, False, False], 'project', True)",
                cwd.display().to_string()
            )
            .replace('"', "'")
        )
    );
    assert!(
        !marker.exists(),
        "a cwd module shadowed the stdlib or runtime"
    );
    let shutdown = manager.shutdown(KernelShutdownOptions::default()).await;
    assert!(shutdown.is_ok());
}

#[tokio::test]
async fn background_thread_output_is_separated_from_cell_output() {
    let options = test_options(None);
    let manager = started_manager(options).await;
    // A user thread writing after its cell finished lands in background output.
    let first = execute(
        &manager,
        "import threading, time\ndef _bg():\n    time.sleep(0.3)\n    print('late from thread')\nt = threading.Thread(target=_bg); t.start()\nprint('from cell')",
    )
    .await;
    assert_eq!(first.stdout.trim(), "from cell");
    assert_eq!(first.status, ExecuteStatus::Ok);

    let second = execute(&manager, "time.sleep(0.5)").await;
    assert!(
        second
            .background_output
            .as_ref()
            .is_some_and(|background| background.text.contains("late from thread")),
        "late thread output surfaces as background output, got {:?}",
        second.background_output
    );
    manager
        .shutdown(KernelShutdownOptions::default())
        .await
        .expect("shutdown");
}

#[tokio::test]
async fn rlm_bootstrap_injects_the_kernel_surface() {
    let base = test_options(None);
    let options = KernelManagerOptions {
        bootstrap_code: Some(build_rlm_bootstrap_code(&[])),
        ..base
    };
    let manager = started_manager(options).await;

    let result = execute(
        &manager,
        "callable(rlm.spawn) and callable(rlm.find_models) and hasattr(rlm, 'harness') and callable(bash) and hasattr(rlm, 'get_harness_state')",
    )
    .await;
    assert_eq!(
        result.status,
        ExecuteStatus::Ok,
        "bootstrap must bind the RLM surface"
    );
    assert_eq!(
        result.result.as_deref(),
        Some("True"),
        "rlm/bash/harness must be usable"
    );

    manager
        .shutdown(KernelShutdownOptions::default())
        .await
        .expect("shutdown");
}

#[tokio::test]
async fn host_requests_round_trip_to_registered_handlers() {
    let mut handlers = HostRequestHandlers::new();
    handlers.register(
        "rlm.find_models",
        eukhe_core::kernel::shared::host_handler(|payload| async move {
            assert_eq!(payload.data["query"], "glm");
            assert_eq!(payload.data["limit"], 2);
            Ok(serde_json::json!({
                "models": [
                    {"provider": "pi", "id": "glm-5.3", "name": "GLM", "selector": "pi/glm-5.3"}
                ]
            }))
        }),
    );
    let base = test_options(None);
    let options = KernelManagerOptions {
        host_handlers: handlers,
        bootstrap_code: Some(build_rlm_bootstrap_code(&[])),
        ..base
    };
    let manager = started_manager(options).await;

    // rlm.find_models runs through the runtime's host_request bridge; the
    // host reply must reach the awaiting cell.
    let result = execute(
        &manager,
        "result = await rlm.find_models('glm', 2)\nresult[0].selector",
    )
    .await;
    assert_eq!(result.status, ExecuteStatus::Ok, "cell: {:?}", result.error);
    assert_eq!(result.result.as_deref(), Some("'pi/glm-5.3'"));

    // An unregistered request type fails the cell with the TS error text.
    let error = execute(
        &manager,
        "import rlm\nawait rlm.host_request('nope.custom', {})",
    )
    .await;
    assert_eq!(error.status, ExecuteStatus::Error);
    // The runtime raises the host-reply error inside the awaiting cell: it
    // surfaces as the cell's KernelError (evalue), not as stderr.
    let message = error
        .error
        .as_ref()
        .map(|kernel_error| kernel_error.evalue.as_str())
        .unwrap_or_default();
    assert!(
        message.contains("not available in this session"),
        "expected the TS unavailable-handler error, got stderr {:?} error {:?}",
        error.stderr,
        error.error
    );

    manager
        .shutdown(KernelShutdownOptions::default())
        .await
        .expect("shutdown");
}

#[tokio::test]
async fn kill9_then_restart_revives_snapshot_and_reports_unserializable() {
    let dir = tempfile::tempdir().expect("tempdir");
    let options = test_options(Some(dir.path()));
    let manager = started_manager(options).await;

    // Serializable variables plus one unserializable object (an open socket)
    // across separate turns.
    execute(
        &manager,
        "answer = 42\nitems = ['a', 'b']\nimport socket\nconn = socket.socket()",
    )
    .await;
    execute(&manager, "answer += 0").await; // second turn touches the namespace

    // Flush a snapshot so the namespace is durable before the kill.
    let snapshot = tokio::time::timeout(Duration::from_secs(15), manager.snapshot_state())
        .await
        .expect("snapshot must settle")
        .expect("snapshot must run while the kernel is up");
    assert!(
        snapshot.saved.contains(&"answer".to_string()),
        "saved: {:?}",
        snapshot.saved
    );
    assert!(
        snapshot.skipped.iter().any(|skip| skip.name == "conn"),
        "an open socket must be skipped and reported, got: {:?}",
        snapshot.skipped
    );

    let pid = manager.process_id().expect("kernel pid");
    assert!(pid > 0);
    // kill -9 the kernel process, like a host OOM/infra kill.
    let _ = eukhe_core::platform::process::kill_pid(
        pid as i32,
        eukhe_core::platform::process::Signal::Kill,
    );
    // The manager observes the death and goes defunct.
    for _ in 0..100 {
        if manager.is_defunct() {
            break;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    assert!(manager.is_defunct(), "killed kernel must settle defunct");

    // Restart-and-revive: a fresh manager on the same snapshot directory.
    let options = test_options(Some(dir.path()));
    let revived = started_manager(options).await;
    let restore = tokio::time::timeout(Duration::from_secs(15), revived.restore_state())
        .await
        .expect("restore must settle");
    let restore = restore.expect("restore must run");
    assert!(
        restore.restored.contains(&"answer".to_string())
            && restore.restored.contains(&"items".to_string()),
        "restored: {:?}",
        restore.restored
    );
    // TS semantics (state-snapshot.ts): `failed` names are entries present in
    // the snapshot that failed to revive. `conn` was skipped at snapshot time,
    // so it is absent from the payload and cannot appear here; its
    // drop-and-report already happened in `snapshot.skipped` above.

    // The revived values match the pre-kill values.
    let check = execute(&revived, "answer").await;
    assert_eq!(check.result.as_deref(), Some("42"));
    let items = execute(&revived, "items").await;
    assert_eq!(items.result.as_deref(), Some("['a', 'b']"));
    // The unserializable name is gone from the namespace.
    let missing = execute(&revived, "'conn' in dir()").await;
    assert_eq!(
        missing.result.as_deref(),
        Some("False"),
        "conn must be dropped"
    );

    revived
        .shutdown(KernelShutdownOptions {
            snapshot: true,
            drain_host_requests: true,
        })
        .await
        .expect("shutdown");
}

/// Background `bash()` handles hold kernel residency (TS #2053), and a
/// held goal/autonomous continuation waits for their settlement (TS #2465):
/// the kernel's bash-activity track is the liveness surface, and the
/// settlement callback is the wake-up. A live handle registers on the
/// track; its completion settles the track exactly once (the completion
/// notice request is admitted before the release event, the runtime's
/// await-reply-then-release order); a graceful teardown over the already
/// settled track fires nothing.
#[tokio::test]
async fn background_bash_settlement_fires_the_callback_once() {
    let mut options = test_options(None);
    let settled = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let counter = std::sync::Arc::clone(&settled);
    // The callback itself is the observable event: the test awaits its
    // notice (a stored permit wakes the wait even if the callback fired
    // first, and the counter stays the witness for the exactly-once
    // assertions).
    let settled_notify = std::sync::Arc::new(tokio::sync::Notify::new());
    let notify = std::sync::Arc::clone(&settled_notify);
    options.on_background_work_settled = Some(std::sync::Arc::new(move || {
        counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        notify.notify_one();
    }));
    let manager = started_manager(options).await;

    execute(&manager, "from rlm import bash").await;
    execute(&manager, "live = bash('sleep 600')").await;
    assert!(
        manager.has_background_work(),
        "the handle must register on the activity track"
    );
    assert_eq!(settled.load(std::sync::atomic::Ordering::SeqCst), 0);

    // The handle finishes: the settlement callback is the wake-up, so the
    // test waits for it directly (the timeout only bounds failure).
    execute(&manager, "live.kill()").await;
    let notified = settled_notify.notified();
    tokio::time::timeout(Duration::from_secs(10), notified)
        .await
        .expect("the settlement callback must fire");
    assert!(
        !manager.has_background_work(),
        "the handle's completion must settle the track"
    );
    assert_eq!(settled.load(std::sync::atomic::Ordering::SeqCst), 1);

    // A graceful teardown over the already-settled track fires nothing.
    manager
        .shutdown(KernelShutdownOptions::default())
        .await
        .expect("shutdown");
    assert_eq!(settled.load(std::sync::atomic::Ordering::SeqCst), 1);
}

/// Regression (H5): a subagent idle on a background `bash()` job was
/// stopped as stalled after `subagentStallMs` while the job (a long build)
/// still ran: its progress token held only session events. The kernel's
/// job output progress moves while a background handle writes output
/// and stays still while it is silent, so only a silent child stalls.
#[tokio::test]
async fn background_bash_output_moves_the_job_progress() {
    let manager = started_manager(test_options(None)).await;
    execute(&manager, "from rlm import bash").await;
    execute(&manager, "silent = bash('sleep 600')").await;
    let quiet = manager.job_output_progress().await;
    tokio::time::sleep(Duration::from_millis(300)).await;
    assert_eq!(
        manager.job_output_progress().await,
        quiet,
        "a silent job must not read as progress"
    );

    execute(
        &manager,
        "build = bash('while true; do echo compiling; sleep 0.05; done')",
    )
    .await;
    let first = manager.job_output_progress().await;
    let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
    while manager.job_output_progress().await == first {
        assert!(
            tokio::time::Instant::now() < deadline,
            "a writing job must move the progress"
        );
        tokio::time::sleep(Duration::from_millis(50)).await;
    }

    manager.kill();
}

/// Teardown with live background handles fires the settlement exactly once
/// (TS #2465's teardown row, over the #2053 concurrent-handles shape): the
/// handles die with the kernel, so owed continuations waiting on them must
/// hear the settlement before it is lost — once, not once per handle.
#[tokio::test]
async fn kernel_teardown_with_live_handles_settles_the_callback_once() {
    let mut options = test_options(None);
    let settled = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let counter = std::sync::Arc::clone(&settled);
    options.on_background_work_settled = Some(std::sync::Arc::new(move || {
        counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    }));
    let manager = started_manager(options).await;

    execute(&manager, "from rlm import bash").await;
    execute(&manager, "first = bash('sleep 600')").await;
    execute(&manager, "second = bash('sleep 600')").await;
    assert!(manager.has_background_work());
    assert_eq!(settled.load(std::sync::atomic::Ordering::SeqCst), 0);

    // TS #2053's teardown shape: kill() tears the handles down with the
    // kernel, and the settlement fires once for the whole track —
    // synchronously with the teardown, so the state is assertable here.
    manager.kill();
    assert!(!manager.has_background_work());
    assert_eq!(settled.load(std::sync::atomic::Ordering::SeqCst), 1);
}

/// Each `bash()` call a cell starts reports its command text and line
/// count through the bash-command display MIME, aggregated into the cell's
/// execute result — including calls routed through a helper function,
/// which a static scan of the cell source cannot see.
#[tokio::test]
async fn cell_result_summarizes_the_bash_commands_it_ran() {
    let options = test_options(None);
    let manager = started_manager(options).await;
    execute(&manager, "from rlm import bash").await;

    let result = execute(
        &manager,
        "async def sh(cmd):\n    return await bash(cmd)\nawait sh(\"echo one\\necho two\")\nawait bash(\"true\")",
    )
    .await;

    assert_eq!(result.status, ExecuteStatus::Ok);
    assert_eq!(
        result.bash_commands,
        Some(KernelBashCommands {
            first: "echo one\necho two".to_string(),
            count: 2,
            lines: 3,
        })
    );
    manager
        .shutdown(KernelShutdownOptions::default())
        .await
        .expect("shutdown");
}

#[tokio::test]
async fn graceful_shutdown_flushes_the_final_snapshot() {
    let dir = tempfile::tempdir().expect("tempdir");
    let options = test_options(Some(dir.path()));
    let manager = started_manager(options).await;
    execute(&manager, "persisted = 'value'\n").await;

    // shutdown({snapshot: true}) must flush the namespace without an
    // explicit snapshot call.
    let performed = tokio::time::timeout(
        Duration::from_secs(15),
        manager.shutdown(KernelShutdownOptions {
            snapshot: true,
            drain_host_requests: true,
        }),
    )
    .await
    .expect("shutdown must settle");
    assert!(performed.expect("shutdown result"));

    let options = test_options(Some(dir.path()));
    let revived = started_manager(options).await;
    let restore = revived
        .restore_state()
        .await
        .expect("restore after graceful shutdown");
    assert!(
        restore.restored.contains(&"persisted".to_string()),
        "graceful shutdown must persist the namespace, got {:?}",
        restore.restored
    );
    revived
        .shutdown(KernelShutdownOptions::default())
        .await
        .expect("shutdown");
}

/// Run `code` and abort it once it has started (its first stdout chunk),
/// returning the settled result, its forwarded stdout, and how long the
/// abort took to settle it.
async fn execute_then_abort(
    manager: &ReplKernelManager,
    code: &str,
) -> (eukhe_core::kernel::shared::ExecuteResult, String, Duration) {
    let signal = eukhe_core::kernel::cancellation::AbortSignal::new();
    let started = std::sync::Arc::new(tokio::sync::Notify::new());
    let stdout = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
    let on_stream: eukhe_core::kernel::shared::StreamCallback = {
        let started = std::sync::Arc::clone(&started);
        let stdout = std::sync::Arc::clone(&stdout);
        std::sync::Arc::new(move |chunk: &str, _stream| {
            stdout.lock().expect("stdout lock").push_str(chunk);
            started.notify_one();
        })
    };
    let run = manager.execute(
        code,
        ExecuteOptions {
            signal: Some(signal.clone()),
            output: eukhe_core::kernel::shared::OutputSink::Forward(on_stream),
            ..ExecuteOptions::default()
        },
    );
    tokio::pin!(run);
    let aborted_at = tokio::select! {
        result = &mut run => panic!("the cell settled before its abort: {:?}", result.map(|r| r.status)),
        () = started.notified() => {
            signal.abort();
            std::time::Instant::now()
        }
    };
    let result = tokio::time::timeout(Duration::from_secs(10), run)
        .await
        .expect("an aborted cell settles within the grace")
        .expect("an aborted cell settles with a result");
    let stdout = stdout.lock().expect("stdout lock").clone();
    (result, stdout, aborted_at.elapsed())
}

/// An abort stops a running cell whatever it does, and the next cell runs at
/// once: a cell that honors the interrupt settles aborted on a live kernel; a
/// cell that ignores it past the grace settles killed with the output so
/// far, the kernel's process group dies, and a fresh manager revives the
/// last snapshot. No wait for a busy kernel remains.
#[tokio::test]
async fn abort_stops_any_cell_and_the_next_cell_runs_at_once() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let options = test_options(Some(dir.path()));
    let manager = started_manager(options.clone()).await;
    for code in [
        "print('spin', flush=True)\nwhile True:\n    pass",
        "import time\nprint('sleep', flush=True)\ntime.sleep(60)",
    ] {
        let (result, _, _) = execute_then_abort(&manager, code).await;
        assert_eq!(result.status, ExecuteStatus::Aborted, "{code}");
        let next = execute(&manager, "print('next')").await;
        assert_eq!(next.stdout, "next\n");
    }

    let ok = execute(&manager, "kept = 41").await;
    assert_eq!(ok.status, ExecuteStatus::Ok);
    assert!(
        manager.snapshot_state().await.is_some(),
        "the snapshot the next kernel revives"
    );
    // Ignores the interrupt and starts a subprocess in the kernel's group.
    // It prints only inside the `try`, so the abort cannot land before it.
    let stubborn = "import subprocess, time\nchild = subprocess.Popen(['sleep', '60'])\nwhile True:\n    try:\n        print(child.pid, flush=True)\n        time.sleep(60)\n    except BaseException:\n        pass";
    let (killed, stdout, took) = execute_then_abort(&manager, stubborn).await;
    assert_eq!(killed.status, ExecuteStatus::Killed);
    assert!(took < Duration::from_secs(5), "settled after {took:?}");
    assert!(manager.is_defunct(), "the kernel was killed");
    let child: u32 = stdout
        .lines()
        .next()
        .and_then(|line| line.parse().ok())
        .expect("child pid printed");
    tokio::time::timeout(
        Duration::from_secs(5),
        eukhe_core::platform::process::wait_for_exit(child),
    )
    .await
    .expect("the cell's subprocess dies with the group")
    .expect("exit watch");

    let revived = started_manager(options).await;
    let restore = revived.restore_state().await.expect("snapshot restore");
    assert!(restore.restored.contains(&"kept".to_string()));
    let next = execute(&revived, "print(kept + 1)").await;
    assert_eq!(next.stdout, "42\n");
    revived.kill();
}
