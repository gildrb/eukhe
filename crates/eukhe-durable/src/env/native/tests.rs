//! Port of `test/env-node-spill.test.ts`. The TS test mocks
//! `createWriteStream` to make every spill write slow and backpressured; the
//! port slows spill writes through the crate-internal [`SpillHook`].

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::BACKGROUND_CONTEXT;

use super::exec::SpillHook;
use super::{NativeExecutionEnv, NativeExecutionEnvOptions};
use crate::env::{ExecCommand, FileSystem, Shell, ShellExecOptions, ShellSpillOptions};

/// Longer than the shell's post-exit stdio grace period plus the descendant's
/// delayed write.
const SPILL_WRITE_DELAY: Duration = Duration::from_millis(600);

#[tokio::test(flavor = "multi_thread")]
async fn keeps_inherited_stdio_open_past_the_exit_grace_period_while_a_spill_write_is_pending() {
    let dir = tempfile::Builder::new()
        .prefix("pi-durable-env-spill-")
        .tempdir()
        .expect("temp dir");
    let writes = Arc::new(AtomicUsize::new(0));
    let mut env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: dir.path().to_str().expect("utf-8 temp dir").to_owned(),
        ..NativeExecutionEnvOptions::default()
    });
    env.spill_hook = Some(SpillHook {
        write_delay: SPILL_WRITE_DELAY,
        writes: Arc::clone(&writes),
    });
    // The shell exits after the first chunk crosses the spill threshold and
    // backpressures the spill. A background descendant retains stdout and
    // writes after the post-exit grace period. Without the pending-spill
    // guard, settlement destroys stdout before that descendant output is read.
    let command = "printf '%020d' 0 | tr 0 a; (sleep 0.2; printf '%01000d' 0 | tr 0 b) &";

    let output = Arc::new(Mutex::new(String::new()));
    let sink = Arc::clone(&output);
    let options = ShellExecOptions {
        spill: Some(ShellSpillOptions {
            after_bytes: 10,
            after_lines: 10,
        }),
        on_output: Some(Arc::new(move |text, _cx, _info| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push_str(text);
            Ok(())
        })),
        ..ShellExecOptions::default()
    };
    let result = tokio::time::timeout(
        Duration::from_secs(10),
        env.exec(
            &ExecCommand::Shell(command.to_owned()),
            &options,
            &BACKGROUND_CONTEXT,
        ),
    )
    .await
    .expect("settles within 10 s")
    .expect("exec");

    assert!(writes.load(Ordering::SeqCst) > 0);
    assert_eq!(
        output.lock().unwrap_or_else(PoisonError::into_inner).len(),
        1020
    );
    let spill_path = result.spill_path.expect("spill path");
    let spilled = env
        .read_text_file(&spill_path, &BACKGROUND_CONTEXT)
        .await
        .expect("read spill");
    assert_eq!(spilled, format!("{}{}", "a".repeat(20), "b".repeat(1000)));
    if let Some(parent) = std::path::Path::new(&spill_path).parent() {
        std::fs::remove_dir_all(parent).expect("remove spill dir");
    }
}

/// An entry removed between the directory scan and its `lstat` is left out
/// of the listing instead of failing it (the read-only session view lists a
/// live owner's directory, whose `.reclaim` temporaries are renamed away at
/// any moment). The scan's names here include one gone by the `lstat`.
#[tokio::test]
async fn a_listed_entry_removed_before_its_lstat_is_left_out() {
    let dir = tempfile::tempdir().expect("temp dir");
    std::fs::write(dir.path().join("doc-4.jsonl"), "").expect("write the kept entry");
    let directory = dir.path().to_str().expect("UTF-8 temp path");
    let names = vec!["doc-4.jsonl".to_owned(), "doc-4.jsonl.reclaim".to_owned()];
    let infos = super::listed_entry_infos(directory, names, &BACKGROUND_CONTEXT)
        .await
        .expect("the listing survives the vanished entry");
    let listed: Vec<&str> = infos.iter().map(|info| info.name.as_str()).collect();
    assert_eq!(listed, ["doc-4.jsonl"]);
}
