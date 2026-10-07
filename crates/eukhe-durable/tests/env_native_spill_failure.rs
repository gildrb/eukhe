//! `fails rather than silently losing a requested spill` of
//! `test/env-node.test.ts`.
//!
//! The TS test subclasses the environment so `createTempFile` returns a path
//! in a missing directory. Rust has no subclassing; pointing `TMPDIR` at a
//! missing directory makes the spill's temporary file fail the same way. That
//! changes the process environment, so this test runs alone in its own binary.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::env::{
    ExecCommand, ExecutionErrorCode, NativeExecutionEnv, NativeExecutionEnvOptions, Shell,
    ShellExecOptions, ShellSpillOptions,
};

#[tokio::test]
async fn fails_rather_than_silently_losing_a_requested_spill() {
    let dir = tempfile::Builder::new()
        .prefix("pi-durable-env-")
        .tempdir()
        .expect("temp dir");
    let root = dir.path().to_str().expect("utf-8 temp dir").to_owned();
    // Edition 2021; this binary runs no other test.
    std::env::set_var("TMPDIR", format!("{root}/missing"));
    let env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: root,
        ..NativeExecutionEnvOptions::default()
    });
    let options = ShellExecOptions {
        spill: Some(ShellSpillOptions {
            after_bytes: 10,
            after_lines: 10,
        }),
        ..ShellExecOptions::default()
    };
    let result = env
        .exec(
            &ExecCommand::Shell("printf 12345678901234567890".to_owned()),
            &options,
            &BACKGROUND_CONTEXT,
        )
        .await;
    let error = result.expect_err("the spill failure fails the command");
    assert_eq!(error.code, ExecutionErrorCode::Unknown);
    assert!(
        error
            .message
            .contains("Failed to preserve complete shell output"),
        "{}",
        error.message
    );
}
