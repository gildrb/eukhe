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

//! Verifier integration test of the bounded protocol (docs/runtime.md S3):
//! an oversized host request gets an error reply and the session keeps
//! working; a host request of a type the host does not serve gets an
//! error reply without reaching a handler; an oversized line with no
//! host-request header poisons the child and lands in protocol repair
//! instead of buffering until OOM (TS #2423 `MAX_PROTOCOL_LINE_CHARS` +
//! the `oversized protocol line` repair test).
//!
//! A fake runtime (a small executable script, not the real one) answers the
//! ready handshake and serves each request as its code says — so the
//! repair's replacement child serves the follow-up cell.

use std::collections::HashMap;
use std::time::{Duration, Instant};

use eukhe_core::kernel::manager::{KernelStartOptions, ReplKernelManager};
use eukhe_core::kernel::shared::{
    host_handler, ExecuteOptions, ExecuteStatus, HostRequestHandlers, KernelManagerOptions,
    KernelShutdownOptions,
};

#[path = "support/executable_script.rs"]
mod executable_script;
use executable_script::write_executable_script;

/// Speaks protocol v3: ready, then per request the oversized unterminated
/// line (the corruption under test), a multi-MiB blank line followed by a
/// plain stdout frame (the linear-scan test), a host request (oversized,
/// of an unserved type, or served) whose reply it echoes as stdout, or a
/// plain done frame.
const FAKE_RUNTIME: &str = r#"#!/usr/bin/env python3
import json
import sys
import time

print(json.dumps({"event": "ready", "protocol": 3, "python": "3.13.0"}), flush=True)
for line in sys.stdin:
    try:
        req = json.loads(line)
    except Exception:
        continue
    code = req.get("code")
    if code == "corrupt-huge-line":
        sys.stdout.write("x" * (33 * 1024 * 1024))
        sys.stdout.flush()
        time.sleep(30)
        break
    if code == "big-frame":
        sys.stdout.write(" " * (31 * 1024 * 1024) + "\n")
        sys.stdout.write(json.dumps({"event": "stdout", "id": req.get("id"), "text": "big"}) + "\n")
    if code in ("huge-host-request", "unserved-host-request", "served-host-request"):
        data = {"type": "echo"}
        if code == "huge-host-request":
            data["pad"] = "x" * (33 * 1024 * 1024)
        if code == "unserved-host-request":
            data["type"] = "nope.kind"
        frame = {"event": "host_request", "id": "hr-" + code, "data": data}
        sys.stdout.write(json.dumps(frame, separators=(",", ":")) + "\n")
        sys.stdout.flush()
        reply = json.loads(sys.stdin.readline())
        text = json.dumps({"id": reply.get("id"), "data": reply.get("data")})
        sys.stdout.write(json.dumps({"event": "stdout", "id": req.get("id"), "text": text}) + "\n")
    sys.stdout.write(json.dumps({"event": "done", "id": req.get("id"), "status": "ok"}) + "\n")
    sys.stdout.flush()
"#;

fn fake_runtime_path() -> std::path::PathBuf {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let path = dir.path().join("fake-kernel");
    write_executable_script(&path, FAKE_RUNTIME, 0o755);
    // Leak the temp dir: the script must exist until the spawned child exits.
    std::mem::forget(dir);
    path
}

fn manager(python: std::path::PathBuf) -> ReplKernelManager {
    let mut host_handlers = HostRequestHandlers::new();
    host_handlers.register(
        "echo",
        host_handler(|_payload| async { Ok(serde_json::json!({ "echoed": true })) }),
    );
    ReplKernelManager::new(KernelManagerOptions {
        python: Some(python),
        cwd: Some(std::env::temp_dir()),
        env: HashMap::new(),
        session_id: Some("protocol-caps-test".to_string()),
        host_handlers,
        python_skills: Vec::new(),
        snapshot: None,
        bootstrap_code: None,
        stderr_log_path: None,
        transport: eukhe_core::kernel::KernelTransport::Local,
        on_background_work_settled: None,
        kept_credentials: eukhe_core::kernel::shared::KeptCredentials::default(),
    })
}

/// The host reply the fake runtime echoed for one host-request cell.
async fn host_reply(manager: &ReplKernelManager, code: &str) -> serde_json::Value {
    let result = manager
        .execute(code, ExecuteOptions::default())
        .await
        .expect("the host-request cell must settle");
    assert_eq!(result.status, ExecuteStatus::Ok, "{result:?}");
    serde_json::from_str(&result.stdout).expect("the echoed reply")
}

#[tokio::test]
async fn host_requests_get_one_reply_each_and_only_served_ones_run() {
    let manager = manager(fake_runtime_path());
    manager
        .start(KernelStartOptions::default())
        .await
        .expect("fake kernel must start");
    let replies = vec![
        host_reply(&manager, "huge-host-request").await,
        host_reply(&manager, "unserved-host-request").await,
        host_reply(&manager, "served-host-request").await,
    ];
    assert_eq!(
        replies,
        vec![
            serde_json::json!({
                "id": "hr-huge-host-request",
                "data": {
                    "status": "error",
                    "error": "host request frame exceeds the 33554432-byte protocol line limit",
                },
            }),
            serde_json::json!({
                "id": "hr-unserved-host-request",
                "data": {
                    "status": "error",
                    "error": "host request type \"nope.kind\" is not available in this session",
                },
            }),
            serde_json::json!({
                "id": "hr-served-host-request",
                "data": { "status": "ok", "result": { "echoed": true } },
            }),
        ]
    );
    // The session kept working: no repair, the same child serves on.
    let follow = manager
        .execute("42", ExecuteOptions::default())
        .await
        .expect("follow-up execute must not fail");
    assert_eq!(follow.status, ExecuteStatus::Ok);
    let _ = tokio::time::timeout(
        Duration::from_secs(10),
        manager.shutdown(KernelShutdownOptions::default()),
    )
    .await;
}

#[tokio::test]
async fn oversized_unterminated_protocol_line_poisons_and_repairs() {
    let manager = manager(fake_runtime_path());
    manager
        .start(KernelStartOptions::default())
        .await
        .expect("fake kernel must start");

    let corrupt = manager
        .execute("corrupt-huge-line", ExecuteOptions::default())
        .await;
    let error = corrupt.expect_err("the oversized line must fail the request");
    assert!(
        error.to_string().contains("oversized protocol line"),
        "unexpected error: {error:#}"
    );

    // The poisoned child is replaced by the protocol repair; the follow-up
    // cell (the replacement also speaks the fake protocol) serves normally
    // with a plain ok done frame.
    let follow = manager.execute("42", ExecuteOptions::default()).await;
    let follow = follow.expect("follow-up execute must not fail");
    assert_eq!(follow.status, ExecuteStatus::Ok);
    assert_eq!(follow.result, None);

    let shutdown = manager.shutdown(KernelShutdownOptions::default()).await;
    assert!(shutdown.is_ok());
}

#[tokio::test]
async fn normal_protocol_lines_still_stream_through_the_bounded_reader() {
    // Multiple frames in one 64 Ki chunk plus a trailing partial line must
    // all dispatch: the chunked reader only poisons past the ceiling.
    let manager = manager(fake_runtime_path());
    manager
        .start(KernelStartOptions::default())
        .await
        .expect("fake kernel must start");
    for i in 0..50 {
        let result = manager
            .execute(&format!("cell-{i}"), ExecuteOptions::default())
            .await
            .expect("execute must not fail");
        assert_eq!(result.status, ExecuteStatus::Ok);
    }
    // Give the teardown its full grace window (the fake lives until EOF).
    let _ = tokio::time::timeout(
        Duration::from_secs(10),
        manager.shutdown(KernelShutdownOptions::default()),
    )
    .await;
}

#[tokio::test]
async fn multi_mib_blank_protocol_line_is_read_in_linear_time() {
    // A 31 MiB blank line arrives in pipe reads of at most 64 KiB; rescanning
    // the buffered prefix per read would scan >= 8 GB. Blank lines skip
    // parse_event, so the fixed path pays only the one-pass scan.
    let manager = manager(fake_runtime_path());
    manager
        .start(KernelStartOptions::default())
        .await
        .expect("fake kernel must start");
    let started = Instant::now();
    let result = manager
        .execute("big-frame", ExecuteOptions::default())
        .await
        .expect("execute must not fail");
    let elapsed = started.elapsed();
    assert_eq!(
        (result.status, result.stdout.as_str()),
        (ExecuteStatus::Ok, "big")
    );
    assert!(
        elapsed < Duration::from_secs(3),
        "31 MiB blank line took {elapsed:?}"
    );
    assert!(manager
        .shutdown(KernelShutdownOptions::default())
        .await
        .is_ok());
}
