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

//! `@remote` on the real runtime (docs/runtime.md S3): a decorated
//! function registers with the host (name, schema from its type hints,
//! docstring); the host's `call` request runs it and gets its result; a
//! function that raises, is unknown, or hangs past the bound answers a
//! typed error, and the kernel keeps serving cells and calls.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use eukhe_core::kernel::bootstrap::build_rlm_bootstrap_code;
use eukhe_core::kernel::manager::{KernelStartOptions, RemoteCallError, ReplKernelManager};
use eukhe_core::kernel::shared::{
    host_handler, ExecuteOptions, ExecuteStatus, HostRequestHandlers, KernelManagerOptions,
    KernelShutdownOptions,
};
use eukhe_core::kernel::KernelTransport;
use serde_json::{json, Value};

#[path = "support/kernel_runtime.rs"]
mod kernel_runtime;
use kernel_runtime::kernel_python;

async fn cell(manager: &ReplKernelManager, code: &str) -> Option<String> {
    let result = manager
        .execute(code, ExecuteOptions::default())
        .await
        .expect("execute");
    assert_eq!(
        result.status,
        ExecuteStatus::Ok,
        "cell {code:?} failed: {:?} {}",
        result.error,
        result.stderr
    );
    result.result
}

const DEFINE: &str = r#"import asyncio, time
from typing import Literal
from rlm import remote

@remote
def add(a: int, b: int = 2, mode: Literal["sum", "text"] = "sum", tags: list[str] | None = None) -> int:
    """Add two numbers."""
    return a + b if mode == "sum" else f"{a}+{b}"

@remote(name="explode")
def boom(reason: str):
    raise ValueError(reason)

@remote
def hang():
    time.sleep(3600)

@remote
async def hang_async():
    await asyncio.sleep(3600)

@remote
def not_a_number():
    return {"x": float("nan")}

@remote
async def twice(a: int) -> int:
    return 2 * a
"#;

#[tokio::test]
async fn a_remote_function_registers_answers_calls_and_fails_typed() {
    let registered = Arc::new(Mutex::new(Vec::new()));
    let mut handlers = HostRequestHandlers::new();
    let seen = Arc::clone(&registered);
    handlers.register(
        "remote.register",
        host_handler(move |payload| {
            let seen = Arc::clone(&seen);
            async move {
                let mut data = payload.data;
                data.as_object_mut()
                    .expect("object")
                    .remove("cellSourceCode");
                seen.lock().expect("lock").push(data);
                Ok(json!({}))
            }
        }),
    );
    let bootstrap = build_rlm_bootstrap_code(&[]);
    let manager = ReplKernelManager::new(KernelManagerOptions {
        python: Some(kernel_python()),
        cwd: Some(std::env::temp_dir()),
        env: HashMap::new(),
        session_id: Some("remote-test".to_owned()),
        host_handlers: handlers,
        python_skills: Vec::new(),
        on_background_work_settled: None,
        snapshot: None,
        bootstrap_code: Some(bootstrap.clone()),
        stderr_log_path: None,
        transport: KernelTransport::Local,
    });
    manager
        .start(KernelStartOptions::default())
        .await
        .expect("kernel starts");
    cell(&manager, &bootstrap).await;
    cell(&manager, DEFINE).await;

    let announced = |name: &str, function: &str, description: &str, parameters: Value| {
        json!({
            "type": "remote.register",
            "name": name,
            "module": "__main__",
            "function": function,
            "description": description,
            "parameters": parameters,
        })
    };
    let no_arguments = json!({ "type": "object", "properties": {}, "additionalProperties": false });
    assert_eq!(
        *registered.lock().expect("lock"),
        vec![
            announced(
                "add",
                "add",
                "Add two numbers.",
                json!({
                    "type": "object",
                    "properties": {
                        "a": { "type": "integer" },
                        "b": { "type": "integer" },
                        "mode": { "enum": ["sum", "text"] },
                        "tags": { "anyOf": [{ "type": "array", "items": { "type": "string" } }, { "type": "null" }] },
                    },
                    "additionalProperties": false,
                    "required": ["a"],
                })
            ),
            announced(
                "explode",
                "boom",
                "",
                json!({
                    "type": "object",
                    "properties": { "reason": { "type": "string" } },
                    "additionalProperties": false,
                    "required": ["reason"],
                })
            ),
            announced("hang", "hang", "", no_arguments.clone()),
            announced("hang_async", "hang_async", "", no_arguments.clone()),
            announced("not_a_number", "not_a_number", "", no_arguments),
            announced(
                "twice",
                "twice",
                "",
                json!({
                    "type": "object",
                    "properties": { "a": { "type": "integer" } },
                    "additionalProperties": false,
                    "required": ["a"],
                })
            ),
        ]
    );

    let call = |function: &'static str, args: Value, timeout_ms: u64| {
        let manager = manager.clone();
        async move {
            manager
                .remote_call("__main__", function, &args, timeout_ms)
                .await
        }
    };
    assert_eq!(
        (
            call("add", json!({ "a": 3 }), 10_000).await,
            call("add", json!({ "a": 3, "b": 4, "mode": "text" }), 10_000).await,
            call("boom", json!({ "reason": "no fuel" }), 10_000).await,
            call("add", json!({ "c": 1 }), 10_000).await,
            call("missing", json!({}), 10_000).await,
            call("hang", json!({}), 300).await,
            call("hang_async", json!({}), 300).await,
        ),
        (
            Ok(json!(5)),
            Ok(json!("3+4")),
            Err(RemoteCallError::Failed {
                function: "boom".to_owned(),
                message: "ValueError: no fuel".to_owned(),
            }),
            Err(RemoteCallError::Failed {
                function: "add".to_owned(),
                message: "TypeError: add() got an unexpected keyword argument 'c'".to_owned(),
            }),
            Err(RemoteCallError::Unknown {
                function: "missing".to_owned(),
            }),
            Err(RemoteCallError::Timeout {
                function: "hang".to_owned(),
                timeout_ms: 300,
            }),
            Err(RemoteCallError::Timeout {
                function: "hang_async".to_owned(),
                timeout_ms: 300,
            }),
        )
    );

    // A NaN result and wrong arguments to an async function answer typed
    // errors with their text; the kernel is not replaced.
    let nan = call("not_a_number", json!({}), 10_000).await;
    assert!(
        matches!(
            &nan,
            Err(RemoteCallError::Failed { function, message })
                if function == "not_a_number"
                    && message.starts_with("not_a_number returned a value JSON cannot carry: Out of range float values")
        ),
        "{nan:?}"
    );
    assert_eq!(
        call("twice", json!({ "b": 1 }), 10_000).await,
        Err(RemoteCallError::Failed {
            function: "twice".to_owned(),
            message: "TypeError: twice() got an unexpected keyword argument 'b'".to_owned(),
        })
    );

    // The hung function holds only its own thread: cells and calls go on.
    assert_eq!(cell(&manager, "1 + 1").await.as_deref(), Some("2"));
    assert_eq!(
        call("add", json!({ "a": 1, "b": 1 }), 10_000).await,
        Ok(json!(2))
    );
    assert_eq!(call("twice", json!({ "a": 3 }), 10_000).await, Ok(json!(6)));
    manager
        .shutdown(KernelShutdownOptions::default())
        .await
        .expect("shutdown");
}

/// A kernel that exits during a call answers `Unreachable` at once, not a
/// timeout at the end of the call's bound.
#[tokio::test]
async fn a_remote_call_whose_kernel_exits_is_unreachable_not_a_timeout() {
    let mut handlers = HostRequestHandlers::new();
    handlers.register(
        "remote.register",
        host_handler(|_payload| async { Ok(json!({})) }),
    );
    let bootstrap = build_rlm_bootstrap_code(&[]);
    let manager = ReplKernelManager::new(KernelManagerOptions {
        python: Some(kernel_python()),
        cwd: Some(std::env::temp_dir()),
        env: HashMap::new(),
        session_id: Some("remote-exit-test".to_owned()),
        host_handlers: handlers,
        python_skills: Vec::new(),
        on_background_work_settled: None,
        snapshot: None,
        bootstrap_code: Some(bootstrap.clone()),
        stderr_log_path: None,
        transport: KernelTransport::Local,
    });
    manager
        .start(KernelStartOptions::default())
        .await
        .expect("kernel starts");
    cell(&manager, &bootstrap).await;
    cell(
        &manager,
        "import os\nfrom rlm import remote\n\n@remote\ndef die():\n    os._exit(3)\n",
    )
    .await;
    let started = std::time::Instant::now();
    let called = manager
        .remote_call("__main__", "die", &json!({}), 60_000)
        .await;
    assert_eq!(
        (
            called,
            started.elapsed() < std::time::Duration::from_secs(30)
        ),
        (
            Err(RemoteCallError::Unreachable(
                "the kernel stopped before it replied".to_owned()
            )),
            true,
        )
    );
}
