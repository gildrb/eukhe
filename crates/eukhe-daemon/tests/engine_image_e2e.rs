//! The `eukhe-daemon` binary is the whole engine image: besides the
//! supervisor and its session workers it serves `tiny-worker`, the shared
//! tiny-model worker a session spawns from its own executable
//! (`eukhe_core::tiny::worker_exe`). A host that bundles only this binary
//! runs every engine process.

use std::process::Command;

/// The exit code and stderr of `eukhe-daemon <args>`.
fn run_daemon(args: &[&str]) -> (Option<i32>, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_eukhe-daemon"))
        .args(args)
        .env_remove("EUKHE_TINY_WORKER_IDLE_MS")
        .output()
        .expect("run eukhe-daemon");
    (
        output.status.code(),
        String::from_utf8(output.stderr).expect("utf-8 stderr"),
    )
}

#[test]
fn the_daemon_binary_dispatches_tiny_worker_to_the_tiny_worker_entry() {
    let agent_dir = tempfile::tempdir().expect("agent dir");
    let agent_dir = agent_dir.path().to_str().expect("utf-8 temp path");
    assert_eq!(
        [
            run_daemon(&["tiny-worker"]),
            run_daemon(&[
                "tiny-worker",
                "no-such-model",
                "--backend",
                "onnx",
                "--agent-dir",
                agent_dir,
            ]),
        ],
        [
            (
                Some(2),
                "tiny-worker: missing <model>\nusage: eukhe tiny-worker <model> --backend onnx \
                 --agent-dir DIR [--device D] [--dtype T] [--runtime-library P] [--idle-secs N]\n"
                    .to_owned(),
            ),
            (
                Some(2),
                "tiny-worker: no local model \"no-such-model\" in the catalog\n".to_owned(),
            ),
        ]
    );
}
