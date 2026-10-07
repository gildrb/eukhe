//! Port of `test/env-node-conformance.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::env::{
    CreateDirOptions, ExecutionEnv, FileErrorCode, FileSystem, NativeExecutionEnv,
    NativeExecutionEnvOptions, NativeWatchOptions, OpenBinaryReaderOptions, RemoveOptions,
    WatchChange, WatchMode, WatchTarget,
};
use eukhe_durable::testing::{run_env_conformance, EnvConformanceOptions, EnvConformanceProvider};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

fn temp_dir(prefix: &str) -> (tempfile::TempDir, String) {
    let dir = tempfile::Builder::new()
        .prefix(prefix)
        .tempdir()
        .expect("temp dir");
    let path = dir.path().to_str().expect("utf-8 temp dir").to_owned();
    (dir, path)
}

fn native(cwd: &str, watch: NativeWatchOptions) -> NativeExecutionEnv {
    NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: cwd.to_owned(),
        watch,
        ..NativeExecutionEnvOptions::default()
    })
}

fn provider(watch: NativeWatchOptions) -> EnvConformanceProvider {
    Arc::new(move |test| {
        let watch = watch.clone();
        Box::pin(async move {
            let (dir, cwd) = temp_dir("pi-durable-env-conformance-");
            let env: Arc<dyn ExecutionEnv> = Arc::new(native(&cwd, watch));
            test(env).await;
            drop(dir);
        })
    })
}

#[tokio::test(flavor = "multi_thread")]
async fn native_execution_env_conformance() {
    run_env_conformance(
        "NativeExecutionEnv conformance",
        EnvConformanceOptions {
            with_env: provider(NativeWatchOptions::default()),
            shell: None,
            symlinks: None,
        },
    )
    .await;
}

#[tokio::test(flavor = "multi_thread")]
async fn native_execution_env_conformance_with_polling_watches() {
    run_env_conformance(
        "NativeExecutionEnv conformance with polling watches",
        EnvConformanceOptions {
            with_env: provider(NativeWatchOptions {
                mode: Some(WatchMode::Polling),
                poll_interval_ms: Some(100),
                max_directories: None,
            }),
            shell: None,
            symlinks: None,
        },
    )
    .await;
}

// NativeExecutionEnv watch limits

#[tokio::test(flavor = "multi_thread")]
async fn refuses_a_tree_over_the_directory_budget_and_stops_with_an_error_when_one_grows_past_it() {
    let (_dir, cwd) = temp_dir("pi-durable-env-watch-");
    let env = native(
        &cwd,
        NativeWatchOptions {
            max_directories: Some(3),
            ..NativeWatchOptions::default()
        },
    );
    env.create_dir("tree/a/b", CreateDirOptions::default(), cx())
        .await
        .expect("mkdir");
    env.create_dir("tree/c", CreateDirOptions::default(), cx())
        .await
        .expect("mkdir");
    let targets = [WatchTarget {
        path: "tree".to_owned(),
        recursive: true,
        ..WatchTarget::default()
    }];
    let refused = env.watch(&targets, Arc::new(|_change| {}), cx()).await;
    assert_eq!(
        refused.err().map(|error| error.code),
        Some(FileErrorCode::Invalid)
    );

    env.remove(
        "tree/c",
        RemoveOptions {
            recursive: true,
            force: false,
        },
        cx(),
    )
    .await
    .expect("rm");
    let changes = Arc::new(Mutex::new(Vec::new()));
    let sink = Arc::clone(&changes);
    let watcher = env
        .watch(
            &targets,
            Arc::new(move |change: WatchChange| {
                sink.lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(change);
            }),
            cx(),
        )
        .await
        .expect("watch");
    env.create_dir("tree/d", CreateDirOptions::default(), cx())
        .await
        .expect("mkdir");
    let deadline = tokio::time::Instant::now() + Duration::from_millis(3000);
    loop {
        let errored = changes
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .iter()
            .any(|change| matches!(change, WatchChange::Error(_)));
        if errored || tokio::time::Instant::now() >= deadline {
            break;
        }
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    let last = changes
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .last()
        .cloned();
    assert!(
        matches!(&last, Some(WatchChange::Error(error)) if error.code == FileErrorCode::Invalid),
        "{last:?}"
    );
    watcher.close(cx()).await;
}

// NativeExecutionEnv readers

#[tokio::test]
async fn reads_ranges_spanning_several_internal_chunks_exactly() {
    let (_dir, cwd) = temp_dir("pi-durable-env-readers-");
    let bytes: Vec<u8> = (0..(5 * 1024 * 1024 / 2))
        .map(|index: usize| u8::try_from((index * 31) % 251).expect("below 251"))
        .collect();
    std::fs::write(format!("{cwd}/big.bin"), &bytes).expect("write");
    let env = native(&cwd, NativeWatchOptions::default());
    let reader = env
        .open_binary_reader("big.bin", OpenBinaryReaderOptions::default(), cx())
        .await
        .expect("open");
    #[allow(clippy::cast_precision_loss, reason = "a 2.5 MiB length is exact")]
    let length = (bytes.len() + 10) as f64;
    let all = reader.read(0.0, length, cx()).await.expect("read");
    assert_eq!(all.len(), bytes.len());
    assert_eq!(all, bytes);
    let middle_start = 1024 * 1024 - 3;
    #[allow(clippy::cast_precision_loss, reason = "a 1 MiB offset is exact")]
    let middle = reader
        .read(middle_start as f64, 7.0, cx())
        .await
        .expect("read");
    assert_eq!(middle, bytes[middle_start..middle_start + 7].to_vec());
    reader.close(cx()).await;
}

#[tokio::test]
async fn refuses_a_fifo_without_waiting_for_a_writer() {
    let (_dir, cwd) = temp_dir("pi-durable-env-readers-");
    nix::unistd::mkfifo(
        format!("{cwd}/pipe").as_str(),
        nix::sys::stat::Mode::S_IRWXU,
    )
    .expect("mkfifo");
    let result = native(&cwd, NativeWatchOptions::default())
        .open_binary_reader("pipe", OpenBinaryReaderOptions::default(), cx())
        .await;
    assert_eq!(
        result.err().map(|error| error.code),
        Some(FileErrorCode::Invalid)
    );
}
