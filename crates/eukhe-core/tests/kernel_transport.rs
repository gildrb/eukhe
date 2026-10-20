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

//! The kernel transport (docs/runtime.md S3) on the real runtime: a fake
//! wrapper (`setsid -w sh -c 'exec "$@"'`, so the stub runs in a session of
//! its own, like a process behind `docker exec` or `ssh`) runs the
//! unchanged stub in a sandbox directory that maps to a different host
//! directory. The stub starts and serves cells there; an `fs.*` host
//! request reaches the host handler with host paths and its reply's paths
//! come back as the sandbox's; a path outside every mount is refused with
//! the typed `FsError`; and a kill ends the stub through its closed stdin.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use eukhe_core::kernel::bootstrap::build_rlm_bootstrap_code;
use eukhe_core::kernel::manager::{KernelStartOptions, ReplKernelManager};
use eukhe_core::kernel::shared::{
    host_handler, ExecuteOptions, ExecuteStatus, HostRequestHandlers, KernelManagerOptions,
};
use eukhe_core::kernel::transport::{
    KernelTransport, KernelWrapper, PathMap, PathMount, WrapperCommand,
};
use serde_json::{json, Value};

#[path = "support/kernel_runtime.rs"]
mod kernel_runtime;
use kernel_runtime::kernel_python;

#[path = "support/process_watch.rs"]
mod process_watch;
use process_watch::await_process_gone;

/// A host `fs.read` that reads the host file the request names and records
/// each request it served.
fn fs_read_handler(served: Arc<Mutex<Vec<Value>>>) -> HostRequestHandlers {
    let mut handlers = HostRequestHandlers::new();
    handlers.register(
        "fs.read",
        host_handler(move |payload| {
            let served = Arc::clone(&served);
            async move {
                served.lock().expect("lock").push(payload.data.clone());
                let cwd = PathBuf::from(payload.data["cwd"].as_str().expect("cwd"));
                let path = payload.data["args"]["path"].as_str().expect("path");
                let absolute = cwd.join(path);
                let text = std::fs::read_to_string(&absolute)?;
                Ok(json!({
                    "version": "read@1",
                    "path": path,
                    "absolute": absolute,
                    "kind": "file",
                    "rendered": text,
                    "text": text,
                    "diags": [],
                    "warnings": [],
                }))
            }
        }),
    );
    handlers
}

async fn cell(manager: &ReplKernelManager, code: &str) -> String {
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
    result.stdout.trim_end().to_owned()
}

#[tokio::test]
async fn the_stub_runs_unchanged_under_a_wrapper_and_fs_paths_map_through_the_mounts() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path().canonicalize().expect("canonical tempdir");
    let host = root.join("host");
    let sandbox = root.join("sandbox");
    std::fs::create_dir_all(&host).expect("host dir");
    std::fs::create_dir_all(&sandbox).expect("sandbox dir");
    std::fs::write(host.join("note.txt"), "hello from the host\n").expect("host note");
    std::fs::write(sandbox.join("note.txt"), "the sandbox's own copy\n").expect("sandbox note");

    let served = Arc::new(Mutex::new(Vec::new()));
    let bootstrap = build_rlm_bootstrap_code(&[]);
    let manager = ReplKernelManager::new(KernelManagerOptions {
        python: None,
        cwd: Some(host.clone()),
        env: HashMap::from([("EUKHE_CHAT_MEMORY".to_owned(), "1".to_owned())]),
        session_id: Some("transport-test".to_owned()),
        host_handlers: fs_read_handler(Arc::clone(&served)),
        python_skills: Vec::new(),
        on_background_work_settled: None,
        snapshot: None,
        bootstrap_code: Some(bootstrap.clone()),
        stderr_log_path: None,
        transport: KernelTransport::Wrapped(KernelWrapper {
            argv_prefix: ["setsid", "-w", "sh", "-c", "exec \"$@\"", "wrapper"]
                .map(str::to_owned)
                .to_vec(),
            command: WrapperCommand::Argv,
            python: kernel_python().to_string_lossy().into_owned(),
            path_map: PathMap::new(vec![PathMount {
                sandbox: sandbox.clone(),
                host: host.clone(),
            }]),
            env: Vec::new(),
        }),
        kept_credentials: eukhe_core::kernel::shared::KeptCredentials::default(),
    });
    manager
        .start(KernelStartOptions::default())
        .await
        .expect("the wrapped kernel starts");
    cell(&manager, &bootstrap).await;

    // The unchanged stub serves cells in the sandbox's cwd, owned by its
    // stdin, with the kernel env the launch set and no host journal.
    let seen = cell(
        &manager,
        "import os\nprint(os.getcwd())\nprint(os.environ.get('EUKHE_KERNEL_OWNER'), \
         os.environ.get('EUKHE_CHAT_MEMORY'), 'EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL' in os.environ)\n\
         print(open('note.txt').read().strip())\nprint(os.getpid())",
    )
    .await;
    let lines: Vec<&str> = seen.lines().collect();
    let stub_pid: i32 = lines[3].parse().expect("stub pid");
    assert_eq!(
        lines[..3],
        [
            sandbox.to_string_lossy().as_ref(),
            "stdin 1 False",
            "the sandbox's own copy",
        ]
    );

    // fs.* goes through the host with host paths; the reply's paths come
    // back as the sandbox's.
    let read_code = "from rlm.fs import read\ndoc = read('note.txt')\nprint(doc.text.strip())\nprint(doc.absolute)";
    assert_eq!(
        cell(&manager, read_code).await,
        format!(
            "hello from the host\n{}",
            sandbox.join("note.txt").display()
        )
    );
    // A path outside every mount is the typed rejection; no handler runs.
    let refused = cell(
        &manager,
        "from rlm.fs import read, FsError\ntry:\n    read('/etc/hostname')\nexcept FsError as error:\n    print(error.reason, error.version)\n    print(error)",
    )
    .await;
    assert_eq!(
        refused,
        "outside transport@1\nfs.read: /etc/hostname is outside every path the kernel shares with the host"
    );
    assert_eq!(
        *served.lock().expect("lock"),
        vec![json!({
            "type": "fs.read",
            "cwd": host,
            "args": { "path": "note.txt" },
            "cellSourceCode": read_code,
        })]
    );

    // The kill signals the wrapper's group; the stub, in its own session,
    // ends through its closed stdin.
    let wrapper_pid = manager.process_id().expect("wrapper pid");
    assert_ne!(wrapper_pid, stub_pid);
    manager.kill();
    await_process_gone(stub_pid).await;
    await_process_gone(wrapper_pid).await;
}
