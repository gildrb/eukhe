//! `uses stdin command transport for legacy WSL bash paths` of
//! `test/env-node.test.ts`. It changes the process's working directory and
//! `PATH`, so it runs alone in its own test binary.

use std::os::unix::fs::PermissionsExt;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::env::{
    ExecCommand, FileSystem, NativeExecutionEnv, NativeExecutionEnvOptions, Shell, ShellExecOptions,
};
use std::sync::{Arc, Mutex, PoisonError};

#[tokio::test]
async fn uses_stdin_command_transport_for_legacy_wsl_bash_paths() {
    let dir = tempfile::Builder::new()
        .prefix("pi-durable-env-")
        .tempdir()
        .expect("temp dir");
    let root = dir.path().to_str().expect("utf-8 temp dir").to_owned();
    let cx = &*BACKGROUND_CONTEXT;
    let shell_path = "C:\\Windows\\System32\\bash.exe";
    let env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: root.clone(),
        ..NativeExecutionEnvOptions::default()
    });
    env.write_file(
        shell_path,
        b"#!/bin/sh\nprintf 'args:%s\\n' \"$*\" >&2\nexec /bin/bash \"$@\"\n",
        cx,
    )
    .await
    .expect("write fake WSL bash");
    std::fs::set_permissions(
        format!("{root}/{shell_path}"),
        std::fs::Permissions::from_mode(0o755),
    )
    .expect("chmod");

    let original_cwd = std::env::current_dir().expect("cwd");
    let original_path = std::env::var_os("PATH").unwrap_or_default();
    std::env::set_current_dir(&root).expect("chdir");
    let mut path = std::ffi::OsString::from(&root);
    path.push(":");
    path.push(&original_path);
    // Edition 2021; this binary runs no other test.
    std::env::set_var("PATH", &path);

    let wsl_env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: root.clone(),
        shell_path: Some(shell_path.to_owned()),
        ..NativeExecutionEnvOptions::default()
    });
    let output = Arc::new(Mutex::new(String::new()));
    let sink = Arc::clone(&output);
    let options = ShellExecOptions {
        on_output: Some(Arc::new(move |text, _cx, _info| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push_str(text);
            Ok(())
        })),
        ..ShellExecOptions::default()
    };
    let name_expansion = concat!("$", "{name}");
    let command = ExecCommand::Shell(format!("name='World'; echo \"Hello, {name_expansion}!\""));
    let result = wsl_env.exec(&command, &options, cx).await;

    std::env::set_current_dir(original_cwd).expect("restore cwd");
    std::env::set_var("PATH", original_path);

    let result = result.expect("exec");
    let output = output
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert!(output.contains("Hello, World!"), "{output}");
    assert!(output.contains("args:-s"), "{output}");
    assert_eq!(result.exit_code, 0);
}
