//! Port of `test/env-node.test.ts` (Linux and macOS cases).

use std::collections::BTreeMap;
use std::fmt::Write;
use std::os::unix::fs::symlink;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::{with_abort_signal, AbortController, Context, BACKGROUND_CONTEXT};
use eukhe_durable::env::{
    CreateDirOptions, ExecCommand, ExecutionError, ExecutionErrorCode, FileError, FileErrorCode,
    FileKind, FileSystem, NativeExecutionEnv, NativeExecutionEnvOptions, ReadTextLinesOptions,
    RemoveOptions, Shell, ShellExecOptions, ShellExecResult, ShellSpillOptions, TempFileOptions,
    TextLine,
};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

fn aborted_context() -> Context {
    let controller = AbortController::new();
    controller.abort(None);
    with_abort_signal(&controller.signal(), cx())
}

/// A fresh directory, removed on drop.
struct Fixture {
    _dir: tempfile::TempDir,
    root: String,
}

fn temp_root() -> Fixture {
    let dir = tempfile::Builder::new()
        .prefix("pi-durable-env-")
        .tempdir()
        .expect("temp dir");
    let root = dir.path().to_str().expect("utf-8 temp dir").to_owned();
    Fixture { _dir: dir, root }
}

fn native(root: &str) -> NativeExecutionEnv {
    NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: root.to_owned(),
        ..NativeExecutionEnvOptions::default()
    })
}

#[track_caller]
fn get<T, E: std::fmt::Debug>(result: Result<T, E>) -> T {
    match result {
        Ok(value) => value,
        Err(error) => panic!("unexpected failure: {error:?}"),
    }
}

#[track_caller]
fn file_error<T: std::fmt::Debug>(result: Result<T, FileError>) -> FileError {
    match result {
        Ok(value) => panic!("expected a FileError, got {value:?}"),
        Err(error) => error,
    }
}

#[track_caller]
fn exec_error<T: std::fmt::Debug>(result: Result<T, ExecutionError>) -> ExecutionError {
    match result {
        Ok(value) => panic!("expected an ExecutionError, got {value:?}"),
        Err(error) => error,
    }
}

/// The code of a failed file operation.
fn code<T>(result: Result<T, FileError>) -> Option<FileErrorCode> {
    result.err().map(|error| error.code)
}

fn shell(command: &str) -> ExecCommand {
    ExecCommand::Shell(command.to_owned())
}

/// Removes a spill's temporary directory.
fn remove_spill_dir(spill_path: &str) {
    if let Some(parent) = std::path::Path::new(spill_path).parent() {
        let _ = std::fs::remove_dir_all(parent);
    }
}

async fn collect_shell_output(
    env: &NativeExecutionEnv,
    command: &str,
    options: ShellExecOptions,
    context: &Context,
) -> (Result<ShellExecResult, ExecutionError>, String) {
    let output = Arc::new(Mutex::new(String::new()));
    let sink = Arc::clone(&output);
    let options = ShellExecOptions {
        on_output: Some(Arc::new(move |text, _cx, _info| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push_str(text);
            Ok(())
        })),
        ..options
    };
    let result = env.exec(&shell(command), &options, context).await;
    let output = output
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    (result, output)
}

// NativeExecutionEnv filesystem

#[tokio::test]
async fn reads_writes_lists_and_removes_files_and_directories() {
    let fixture = temp_root();
    let root = &fixture.root;
    let env = native(root);
    assert_eq!(
        get(env.absolute_path("nested/child", cx()).await),
        format!("{root}/nested/child")
    );
    assert_eq!(
        get(env.join_path(&[root, "nested", "child"], cx()).await),
        format!("{root}/nested/child")
    );
    get(env
        .create_dir("nested/child", CreateDirOptions::default(), cx())
        .await);
    get(env.write_file("nested/child/file.txt", b"hel", cx()).await);
    get(env.append_file("nested/child/file.txt", b"lo", cx()).await);
    assert_eq!(
        get(env.read_text_file("nested/child/file.txt", cx()).await),
        "hello"
    );
    assert_eq!(
        get(env
            .read_text_lines(
                "nested/child/file.txt",
                ReadTextLinesOptions {
                    max_lines: Some(1.0)
                },
                cx()
            )
            .await),
        vec!["hello".to_owned()]
    );
    assert_eq!(
        get(env.read_binary_file("nested/child/file.txt", cx()).await),
        b"hello"
    );

    let entries = get(env.list_dir("nested/child", cx()).await);
    assert_eq!(entries.len(), 1);
    let entry = &entries[0];
    assert_eq!(entry.name, "file.txt");
    assert_eq!(entry.path, format!("{root}/nested/child/file.txt"));
    assert_eq!(entry.kind, FileKind::File);
    assert_eq!(entry.size, 5);
    assert!(entry.mtime_ms.is_finite());

    assert!(get(env.exists("nested/child/file.txt", cx()).await));
    get(env
        .remove("nested/child/file.txt", RemoveOptions::default(), cx())
        .await);
    assert!(!get(env.exists("nested/child/file.txt", cx()).await));
}

#[tokio::test]
async fn expands_home_relative_paths_and_file_urls() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let home = std::env::home_dir().expect("home dir");
    assert_eq!(
        get(env.absolute_path("~/pi-node-env-test", cx()).await),
        format!("{}/pi-node-env-test", home.to_str().expect("utf-8 home"))
    );
    let file_path = format!("{}/file with spaces.txt", fixture.root);
    let url = url::Url::from_file_path(&file_path).expect("file URL");
    assert_eq!(get(env.absolute_path(url.as_str(), cx()).await), file_path);
}

#[tokio::test]
async fn returns_file_info_for_files_directories_and_symlinks_without_following_symlinks() {
    let fixture = temp_root();
    let root = &fixture.root;
    let env = native(root);
    get(env
        .create_dir("dir", CreateDirOptions { recursive: true }, cx())
        .await);
    get(env.write_file("dir/file.txt", b"hello", cx()).await);
    symlink(format!("{root}/dir/file.txt"), format!("{root}/file-link")).expect("symlink");
    symlink(format!("{root}/dir"), format!("{root}/dir-link")).expect("symlink");

    let dir = get(env.file_info("dir", cx()).await);
    assert_eq!(
        (dir.name.as_str(), dir.path.clone(), dir.kind),
        ("dir", format!("{root}/dir"), FileKind::Directory)
    );
    let file = get(env.file_info("dir/file.txt", cx()).await);
    assert_eq!(
        (file.name.as_str(), file.path.clone(), file.kind, file.size),
        (
            "file.txt",
            format!("{root}/dir/file.txt"),
            FileKind::File,
            5
        )
    );
    let file_link = get(env.file_info("file-link", cx()).await);
    assert_eq!(
        (
            file_link.name.as_str(),
            file_link.path.clone(),
            file_link.kind
        ),
        ("file-link", format!("{root}/file-link"), FileKind::Symlink)
    );
    let dir_link = get(env.file_info("dir-link", cx()).await);
    assert_eq!(
        (dir_link.name.as_str(), dir_link.path.clone(), dir_link.kind),
        ("dir-link", format!("{root}/dir-link"), FileKind::Symlink)
    );
    let real = std::fs::canonicalize(format!("{root}/dir/file.txt")).expect("realpath");
    assert_eq!(
        get(env.canonical_path("file-link", cx()).await),
        real.to_str().expect("utf-8")
    );
}

#[tokio::test]
async fn lists_symlinks_as_symlinks() {
    let fixture = temp_root();
    let root = &fixture.root;
    let env = native(root);
    get(env.write_file("target.txt", b"hello", cx()).await);
    symlink(format!("{root}/target.txt"), format!("{root}/link.txt")).expect("symlink");

    let mut entries: Vec<(String, FileKind)> = get(env.list_dir(".", cx()).await)
        .into_iter()
        .map(|entry| (entry.name, entry.kind))
        .collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    assert_eq!(
        entries,
        vec![
            ("link.txt".to_owned(), FileKind::Symlink),
            ("target.txt".to_owned(), FileKind::File)
        ]
    );
}

#[tokio::test]
async fn stops_reading_text_lines_at_the_requested_limit() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("file.txt", b"one\ntwo\nthree", cx()).await);
    assert_eq!(
        get(env
            .read_text_lines(
                "file.txt",
                ReadTextLinesOptions {
                    max_lines: Some(1.0)
                },
                cx()
            )
            .await),
        vec!["one".to_owned()]
    );
}

#[tokio::test]
async fn returns_file_error_for_missing_paths_and_keeps_exists_false_for_missing_paths() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let error = file_error(env.file_info("missing.txt", cx()).await);
    assert_eq!(FileError::NAME, "FileError");
    assert_eq!(error.code, FileErrorCode::NotFound);
    assert_eq!(error.path, Some(format!("{}/missing.txt", fixture.root)));
    assert!(!get(env.exists("missing.txt", cx()).await));
}

#[tokio::test]
async fn returns_file_error_for_listing_non_directories() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("file.txt", b"hello", cx()).await);
    let error = file_error(env.list_dir("file.txt", cx()).await);
    assert_eq!(error.code, FileErrorCode::NotDirectory);
}

#[tokio::test]
async fn appends_to_new_files_and_creates_parent_directories() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.append_file("new/nested/file.txt", b"a", cx()).await);
    get(env.append_file("new/nested/file.txt", b"b", cx()).await);
    assert_eq!(
        get(env.read_text_file("new/nested/file.txt", cx()).await),
        "ab"
    );
}

#[tokio::test]
async fn atomically_renames_a_file_and_replaces_the_destination() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("source.txt", b"new", cx()).await);
    get(env.write_file("destination.txt", b"old", cx()).await);

    get(env.rename_file("source.txt", "destination.txt", cx()).await);

    assert!(!get(env.exists("source.txt", cx()).await));
    assert_eq!(
        get(env.read_text_file("destination.txt", cx()).await),
        "new"
    );
}

#[tokio::test]
async fn reports_the_source_path_when_rename_fails_because_the_source_is_missing() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("destination.txt", b"unchanged", cx()).await);

    let error = file_error(
        env.rename_file("missing-source.txt", "destination.txt", cx())
            .await,
    );

    assert_eq!(error.code, FileErrorCode::NotFound);
    assert_eq!(
        error.path,
        Some(format!("{}/missing-source.txt", fixture.root))
    );
    assert_eq!(
        get(env.read_text_file("destination.txt", cx()).await),
        "unchanged"
    );
}

#[tokio::test]
async fn creates_temporary_directories_and_files() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let temp_dir = get(env.create_temp_dir(Some("node-env-test-"), cx()).await);
    assert!(std::fs::metadata(&temp_dir).is_ok());
    let temp_file = get(env
        .create_temp_file(
            TempFileOptions {
                prefix: Some("prefix-".to_owned()),
                suffix: Some(".txt".to_owned()),
            },
            cx(),
        )
        .await);
    assert!(std::fs::metadata(&temp_file).is_ok());
    #[allow(
        clippy::case_sensitive_file_extension_comparisons,
        reason = "the TS assertion is a plain suffix check"
    )]
    let has_suffix = temp_file.ends_with(".txt");
    assert!(has_suffix);
    assert_eq!(get(env.read_text_file(&temp_file, cx()).await), "");
    std::fs::remove_dir_all(&temp_dir).expect("remove temp dir");
    remove_spill_dir(&temp_file);
}

#[tokio::test]
async fn honors_create_dir_recursive_false_and_remove_recursive_force_options() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let error = file_error(
        env.create_dir("missing/child", CreateDirOptions { recursive: false }, cx())
            .await,
    );
    assert_eq!(error.code, FileErrorCode::NotFound);

    get(env.write_file("dir/child/file.txt", b"hello", cx()).await);
    let remove_directory = env
        .remove(
            "dir",
            RemoveOptions {
                recursive: false,
                force: false,
            },
            cx(),
        )
        .await;
    assert!(remove_directory.is_err());
    get(env
        .remove(
            "dir",
            RemoveOptions {
                recursive: true,
                force: false,
            },
            cx(),
        )
        .await);
    assert!(!get(env.exists("dir", cx()).await));

    let remove_missing = env
        .remove(
            "missing",
            RemoveOptions {
                recursive: false,
                force: false,
            },
            cx(),
        )
        .await;
    assert!(remove_missing.is_err());
    get(env
        .remove(
            "missing",
            RemoveOptions {
                recursive: false,
                force: true,
            },
            cx(),
        )
        .await);
}

#[tokio::test]
async fn returns_aborted_results_without_side_effects_for_pre_aborted_file_operations() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("file.txt", b"hello", cx()).await);
    let context = aborted_context();
    let context = &context;

    let aborted = Some(FileErrorCode::Aborted);
    let (
        read_text,
        read_lines,
        read_binary,
        open_reader,
        write,
        append,
        truncate,
        flush,
        rename,
        info,
        list,
        canonical,
        exists,
        create_dir,
        remove,
        temp_dir,
        temp_file,
    ) = tokio::join!(
        env.read_text_file("file.txt", context),
        env.read_text_lines("file.txt", ReadTextLinesOptions::default(), context),
        env.read_binary_file("file.txt", context),
        env.open_text_line_reader("file.txt", context),
        env.write_file("other.txt", b"hello", context),
        env.append_file("file.txt", b" world", context),
        env.truncate_file("file.txt", 1.0, context),
        env.flush_file("file.txt", context),
        env.rename_file("file.txt", "renamed.txt", context),
        env.file_info("file.txt", context),
        env.list_dir(".", context),
        env.canonical_path("file.txt", context),
        env.exists("file.txt", context),
        env.create_dir("dir", CreateDirOptions::default(), context),
        env.remove("file.txt", RemoveOptions::default(), context),
        env.create_temp_dir(None, context),
        env.create_temp_file(TempFileOptions::default(), context),
    );
    assert_eq!(code(read_text), aborted);
    assert_eq!(code(read_lines), aborted);
    assert_eq!(code(read_binary), aborted);
    assert_eq!(code(open_reader), aborted);
    assert_eq!(code(write), aborted);
    assert_eq!(code(append), aborted);
    assert_eq!(code(truncate), aborted);
    assert_eq!(code(flush), aborted);
    assert_eq!(code(rename), aborted);
    assert_eq!(code(info), aborted);
    assert_eq!(code(list), aborted);
    assert_eq!(code(canonical), aborted);
    assert_eq!(code(exists), aborted);
    assert_eq!(code(create_dir), aborted);
    assert_eq!(code(remove), aborted);
    assert_eq!(code(temp_dir), aborted);
    assert_eq!(code(temp_file), aborted);
    assert_eq!(get(env.read_text_file("file.txt", cx()).await), "hello");
    let names: Vec<String> = get(env.list_dir(".", cx()).await)
        .into_iter()
        .map(|entry| entry.name)
        .collect();
    assert_eq!(names, vec!["file.txt".to_owned()]);
}

#[tokio::test]
async fn truncates_and_extends_files_to_exact_byte_sizes() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let bytes = [0x61, 0xc3, 0xa9, 0x0a, 0x62, 0x0a];
    get(env.write_file("file.bin", &bytes, cx()).await);

    // Truncation is byte-exact even when the boundary splits a UTF-8 sequence.
    get(env.truncate_file("file.bin", 2.0, cx()).await);
    assert_eq!(
        get(env.read_binary_file("file.bin", cx()).await),
        vec![0x61, 0xc3]
    );

    get(env.truncate_file("file.bin", 4.0, cx()).await);
    assert_eq!(
        get(env.read_binary_file("file.bin", cx()).await),
        vec![0x61, 0xc3, 0, 0]
    );

    get(env.truncate_file("file.bin", 0.0, cx()).await);
    assert_eq!(get(env.file_info("file.bin", cx()).await).size, 0);
}

#[tokio::test]
async fn rejects_invalid_truncation_sizes_and_never_creates_missing_files() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("file.txt", b"hello", cx()).await);
    for size in [-1.0, 1.5, f64::NAN, f64::INFINITY, 9_007_199_254_740_992.0] {
        let error = file_error(env.truncate_file("file.txt", size, cx()).await);
        assert_eq!(error.code, FileErrorCode::Invalid);
        assert_eq!(error.path, Some(format!("{}/file.txt", fixture.root)));
    }
    assert_eq!(get(env.read_text_file("file.txt", cx()).await), "hello");

    let error = file_error(env.truncate_file("missing.txt", 0.0, cx()).await);
    assert_eq!(error.code, FileErrorCode::NotFound);
    assert_eq!(error.path, Some(format!("{}/missing.txt", fixture.root)));
    assert!(!get(env.exists("missing.txt", cx()).await));
}

#[tokio::test]
async fn flushes_existing_files_without_changing_content_and_reports_missing_paths() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("file.txt", b"durable", cx()).await);
    get(env.flush_file("file.txt", cx()).await);
    assert_eq!(get(env.read_text_file("file.txt", cx()).await), "durable");

    let error = file_error(env.flush_file("missing.txt", cx()).await);
    assert_eq!(error.code, FileErrorCode::NotFound);
    assert_eq!(error.path, Some(format!("{}/missing.txt", fixture.root)));
    assert!(!get(env.exists("missing.txt", cx()).await));

    get(env
        .create_dir("dir", CreateDirOptions::default(), cx())
        .await);
    assert_eq!(
        file_error(env.flush_file("dir", cx()).await).code,
        FileErrorCode::IsDirectory
    );
}

/// The TS test spies on `FileHandle.prototype.sync` to inject an `EIO`; Rust
/// cannot intercept `fsync`, so this checks the observable part: the flush
/// goes through a handle that is closed afterwards.
#[cfg(target_os = "linux")]
#[tokio::test]
async fn syncs_through_an_opened_handle_and_always_closes_the_handle() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("file.txt", b"durable", cx()).await);
    let path = std::fs::canonicalize(format!("{}/file.txt", fixture.root)).expect("realpath");
    for _ in 0..3 {
        get(env.flush_file("file.txt", cx()).await);
    }
    let open = std::fs::read_dir("/proc/self/fd")
        .expect("fd list")
        .filter_map(Result::ok)
        .filter_map(|entry| std::fs::read_link(entry.path()).ok())
        .any(|target| target == path);
    assert!(!open, "the flushed file is not left open");
}

#[tokio::test]
async fn cleanup_is_best_effort() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    FileSystem::cleanup(&env, cx()).await;
}

// NativeExecutionEnv text line reader

#[tokio::test]
async fn reports_whether_each_line_was_newline_terminated_and_preserves_carriage_returns() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env
        .write_file("lines.txt", b"one\r\n\ntwo\npartial", cx())
        .await);
    let reader = get(env.open_text_line_reader("lines.txt", cx()).await);
    let mut lines = Vec::new();
    while let Some(line) = get(reader.read_line(cx()).await) {
        lines.push(line);
    }
    let line = |text: &str, terminated| TextLine {
        text: text.to_owned(),
        terminated,
    };
    assert_eq!(
        lines,
        vec![
            line("one\r", true),
            line("", true),
            line("two", true),
            line("partial", false)
        ]
    );
    assert_eq!(get(reader.read_line(cx()).await), None);
    reader.close(cx()).await;
}

#[tokio::test]
async fn returns_no_lines_for_an_empty_file_and_one_terminated_empty_line_for_a_lone_newline() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("empty.txt", b"", cx()).await);
    get(env.write_file("newline.txt", b"\n", cx()).await);

    let empty = get(env.open_text_line_reader("empty.txt", cx()).await);
    assert_eq!(get(empty.read_line(cx()).await), None);
    empty.close(cx()).await;

    let newline = get(env.open_text_line_reader("newline.txt", cx()).await);
    assert_eq!(
        get(newline.read_line(cx()).await),
        Some(TextLine {
            text: String::new(),
            terminated: true
        })
    );
    assert_eq!(get(newline.read_line(cx()).await), None);
    newline.close(cx()).await;
}

#[tokio::test]
async fn decodes_multi_byte_characters_split_across_read_chunks_and_lines_longer_than_one_chunk() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    // The reader uses 64 KiB chunks; place a four-byte character across the
    // first boundary.
    let first = format!("{}😀tail", "a".repeat(64 * 1024 - 2));
    let second = "é".repeat(100_000);
    get(env
        .write_file("large.txt", format!("{first}\n{second}").as_bytes(), cx())
        .await);
    let reader = get(env.open_text_line_reader("large.txt", cx()).await);
    assert_eq!(
        get(reader.read_line(cx()).await),
        Some(TextLine {
            text: first,
            terminated: true
        })
    );
    assert_eq!(
        get(reader.read_line(cx()).await),
        Some(TextLine {
            text: second,
            terminated: false
        })
    );
    assert_eq!(get(reader.read_line(cx()).await), None);
    reader.close(cx()).await;
}

/// The TS test spies on `FileHandle.prototype.read` to abort while a read is
/// pending. Rust cannot gate the read; the observable contract is the same:
/// an aborted read consumes nothing.
#[tokio::test]
async fn rejects_an_aborted_read_without_consuming_its_bytes() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("lines.txt", b"one\ntwo\n", cx()).await);
    let reader = get(env.open_text_line_reader("lines.txt", cx()).await);
    assert_eq!(
        file_error(reader.read_line(&aborted_context()).await).code,
        FileErrorCode::Aborted
    );
    assert_eq!(
        get(reader.read_line(cx()).await),
        Some(TextLine {
            text: "one".to_owned(),
            terminated: true
        })
    );
    assert_eq!(
        get(reader.read_line(cx()).await),
        Some(TextLine {
            text: "two".to_owned(),
            terminated: true
        })
    );
    assert_eq!(get(reader.read_line(cx()).await), None);
    reader.close(cx()).await;
}

#[tokio::test]
async fn rejects_reads_after_close_and_closes_idempotently() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    get(env.write_file("lines.txt", b"one\n", cx()).await);
    let reader = get(env.open_text_line_reader("lines.txt", cx()).await);
    reader.close(cx()).await;
    reader.close(cx()).await;
    let error = file_error(reader.read_line(cx()).await);
    assert_eq!(error.code, FileErrorCode::Invalid);
    assert_eq!(error.path, Some(format!("{}/lines.txt", fixture.root)));
}

#[tokio::test]
async fn reports_missing_files_when_opening_a_reader() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let Err(error) = env.open_text_line_reader("missing.txt", cx()).await else {
        panic!("expected a FileError");
    };
    assert_eq!(error.code, FileErrorCode::NotFound);
    assert_eq!(error.path, Some(format!("{}/missing.txt", fixture.root)));
}

// NativeExecutionEnv shell

#[tokio::test]
async fn executes_commands_in_cwd_with_env_overrides() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let (result, output) = collect_shell_output(
        &env,
        r#"printf '%s' "$NODE_ENV_TEST" > cwd-marker.txt; printf '%s:%s' "$PWD" "$NODE_ENV_TEST""#,
        ShellExecOptions {
            env: Some(BTreeMap::from([(
                "NODE_ENV_TEST".to_owned(),
                "ok".to_owned(),
            )])),
            ..ShellExecOptions::default()
        },
        cx(),
    )
    .await;
    assert_eq!(get(result).exit_code, 0);
    assert_eq!(
        std::fs::read_to_string(format!("{}/cwd-marker.txt", fixture.root)).expect("marker"),
        "ok"
    );
    let real = std::fs::canonicalize(&fixture.root).expect("realpath");
    assert_eq!(output, format!("{}:ok", real.to_str().expect("utf-8")));
}

async fn applies_string_shell_environment_overrides(
    overrides: Option<BTreeMap<String, String>>,
    expected_session_file: &str,
) {
    let fixture = temp_root();
    let env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: fixture.root.clone(),
        shell_env: Some(BTreeMap::from([
            (
                "PI_SESSION_FILE".to_owned(),
                "/stale/parent.jsonl".to_owned(),
            ),
            ("PI_CODING_AGENT".to_owned(), "true".to_owned()),
            (
                "PI_NODE_ENV_PRESERVED_TEST".to_owned(),
                "preserved".to_owned(),
            ),
        ])),
        ..NativeExecutionEnvOptions::default()
    });
    let (result, output) = collect_shell_output(
        &env,
        r#"printf '%s:%s|%s|%s' "${PI_SESSION_FILE+x}" "${PI_SESSION_FILE-}" "$PI_CODING_AGENT" "$PI_NODE_ENV_PRESERVED_TEST""#,
        ShellExecOptions {
            env: overrides,
            ..ShellExecOptions::default()
        },
        cx(),
    )
    .await;
    get(result);
    assert_eq!(output, format!("{expected_session_file}|true|preserved"));
}

#[tokio::test]
async fn applies_string_shell_environment_overrides_when_a_missing_override_preserves_the_base_value(
) {
    applies_string_shell_environment_overrides(None, "x:/stale/parent.jsonl").await;
}

#[tokio::test]
async fn applies_string_shell_environment_overrides_when_an_empty_override_shadows_the_base_value()
{
    applies_string_shell_environment_overrides(
        Some(BTreeMap::from([(
            "PI_SESSION_FILE".to_owned(),
            String::new(),
        )])),
        "x:",
    )
    .await;
}

#[tokio::test]
async fn applies_string_shell_environment_overrides_when_a_string_override_replaces_the_base_value()
{
    applies_string_shell_environment_overrides(
        Some(BTreeMap::from([(
            "PI_SESSION_FILE".to_owned(),
            "/sessions/current.jsonl".to_owned(),
        )])),
        "x:/sessions/current.jsonl",
    )
    .await;
}

#[tokio::test]
async fn can_replace_rather_than_inherit_the_default_shell_environment() {
    let fixture = temp_root();
    let inherited_key = "PI_NODE_ENV_INHERITED_TEST";
    let configured_key = "PI_NODE_ENV_CONFIGURED_TEST";
    let explicit_key = "PI_NODE_ENV_EXPLICIT_TEST";
    // Edition 2021: setting a variable no other test reads.
    std::env::set_var(inherited_key, "host");
    let env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: fixture.root.clone(),
        shell_env: Some(BTreeMap::from([(
            configured_key.to_owned(),
            "configured".to_owned(),
        )])),
        ..NativeExecutionEnvOptions::default()
    });
    let (result, output) = collect_shell_output(
        &env,
        &format!(r#"printf '%s:%s:%s' "${{{inherited_key}-}}" "${{{configured_key}-}}" "${{{explicit_key}-}}""#),
        ShellExecOptions {
            inherit_env: Some(false),
            env: Some(BTreeMap::from([(explicit_key.to_owned(), "explicit".to_owned())])),
            ..ShellExecOptions::default()
        },
        cx(),
    )
    .await;
    std::env::remove_var(inherited_key);
    get(result);
    assert_eq!(output, "::explicit");
}

#[tokio::test]
async fn cleanup_terminates_active_shell_processes() {
    let fixture = temp_root();
    let env = Arc::new(native(&fixture.root));
    let running = Arc::clone(&env);
    let execution = tokio::spawn(async move {
        running
            .exec(
                &shell("touch started; sleep 60"),
                &ShellExecOptions::default(),
                cx(),
            )
            .await
    });
    let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
    while !get(env.exists("started", cx()).await) {
        assert!(
            tokio::time::Instant::now() < deadline,
            "Condition not met within 10000ms"
        );
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
    Shell::cleanup(env.as_ref(), cx()).await;
    let result = tokio::time::timeout(Duration::from_secs(3), execution)
        .await
        .expect("settles within 3000ms")
        .expect("exec task");
    assert!(result.is_ok());
}

#[tokio::test]
async fn streams_combined_stdout_and_stderr() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let (result, output) = collect_shell_output(
        &env,
        "printf out; printf err >&2",
        ShellExecOptions::default(),
        cx(),
    )
    .await;
    assert_eq!(
        get(result),
        ShellExecResult {
            exit_code: 0,
            spill_path: None
        }
    );
    assert!(output.contains("out"));
    assert!(output.contains("err"));
}

/// The TS test writes the halves of 😀 from `node -e`; `printf` does the same
/// without needing Node.
#[tokio::test]
async fn decodes_utf8_split_across_raw_process_chunks() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let (_, output) = collect_shell_output(
        &env,
        r"printf '\360\237'; sleep 0.05; printf '\230\200'",
        ShellExecOptions::default(),
        cx(),
    )
    .await;
    assert_eq!(output, "😀");
}

#[tokio::test]
async fn reports_a_missing_working_directory_before_spawning() {
    let fixture = temp_root();
    let env = native(&format!("{}/missing", fixture.root));
    let error = exec_error(
        env.exec(&shell("printf ok"), &ShellExecOptions::default(), cx())
            .await,
    );
    assert_eq!(error.code, ExecutionErrorCode::SpawnError);
    assert!(error.message.contains("Working directory does not exist"));
}

#[tokio::test]
async fn returns_non_zero_command_exit_codes_as_successful_execution_results() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let result = get(env
        .exec(&shell("exit 7"), &ShellExecOptions::default(), cx())
        .await);
    assert_eq!(
        result,
        ShellExecResult {
            exit_code: 7,
            spill_path: None
        }
    );
}

// Regression test for https://github.com/earendil-works/pi/issues/8992
#[tokio::test]
async fn maps_signal_killed_processes_to_a_non_zero_exit_code() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let result = get(env
        .exec(&shell("kill -9 $$"), &ShellExecOptions::default(), cx())
        .await);
    assert_eq!(result.exit_code, 128 + 9);
}

#[tokio::test]
async fn returns_timeout_errors_for_commands_exceeding_the_timeout() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let options = ShellExecOptions {
        timeout: Some(0.01),
        ..ShellExecOptions::default()
    };
    let error = exec_error(env.exec(&shell("sleep 5"), &options, cx()).await);
    assert_eq!(error.code, ExecutionErrorCode::Timeout);
}

#[tokio::test]
async fn rejects_invalid_timeouts_before_spawning() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    for timeout in [0.0, -1.0, f64::NAN, f64::INFINITY, 2_147_484.0] {
        let options = ShellExecOptions {
            timeout: Some(timeout),
            ..ShellExecOptions::default()
        };
        let error = exec_error(env.exec(&shell("touch spawned"), &options, cx()).await);
        assert_eq!(error.code, ExecutionErrorCode::Timeout);
        assert!(error.message.contains("Invalid timeout"));
    }
    assert!(!get(env.exists("spawned", cx()).await));
}

#[tokio::test]
async fn returns_callback_errors_from_exec_stream_handlers() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let options = ShellExecOptions {
        on_output: Some(Arc::new(|_text, _cx, _info| Err("callback failed".into()))),
        ..ShellExecOptions::default()
    };
    let error = exec_error(env.exec(&shell("printf out"), &options, cx()).await);
    assert_eq!(error.code, ExecutionErrorCode::CallbackError);
    assert_eq!(error.message, "callback failed");
}

#[tokio::test]
async fn returns_shell_unavailable_and_spawn_errors() {
    let fixture = temp_root();
    let missing_shell_env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: fixture.root.clone(),
        shell_path: Some(format!("{}/missing-shell", fixture.root)),
        ..NativeExecutionEnvOptions::default()
    });
    let error = exec_error(
        missing_shell_env
            .exec(&shell("printf ok"), &ShellExecOptions::default(), cx())
            .await,
    );
    assert_eq!(error.code, ExecutionErrorCode::ShellUnavailable);

    let shell_path = format!("{}/not-executable-shell", fixture.root);
    let env = native(&fixture.root);
    get(env.write_file(&shell_path, b"not executable", cx()).await);
    let spawn_error_env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: fixture.root.clone(),
        shell_path: Some(shell_path),
        ..NativeExecutionEnvOptions::default()
    });
    let error = exec_error(
        spawn_error_env
            .exec(&shell("printf ok"), &ShellExecOptions::default(), cx())
            .await,
    );
    assert_eq!(error.code, ExecutionErrorCode::SpawnError);
}

#[tokio::test]
async fn returns_an_aborted_result_for_pre_aborted_and_aborted_commands() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let error = exec_error(
        env.exec(
            &shell("touch spawned"),
            &ShellExecOptions::default(),
            &aborted_context(),
        )
        .await,
    );
    assert_eq!(error.code, ExecutionErrorCode::Aborted);
    assert!(!get(env.exists("spawned", cx()).await));

    let controller = AbortController::new();
    let context = with_abort_signal(&controller.signal(), cx());
    let options = ShellExecOptions::default();
    let command = shell("sleep 5");
    let pending = env.exec(&command, &options, &context);
    controller.abort(None);
    let error = exec_error(pending.await);
    assert_eq!(error.code, ExecutionErrorCode::Aborted);
}

#[tokio::test]
async fn does_not_create_a_spill_before_output_crosses_its_thresholds() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let options = ShellExecOptions {
        spill: Some(ShellSpillOptions {
            after_bytes: 100,
            after_lines: 10,
        }),
        ..ShellExecOptions::default()
    };
    let result = get(env.exec(&shell("printf short"), &options, cx()).await);
    assert_eq!(result.spill_path, None);
}

#[tokio::test]
async fn preserves_exact_raw_bytes_in_the_spill_while_streaming_decoded_text() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let options = ShellExecOptions {
        spill: Some(ShellSpillOptions {
            after_bytes: 1,
            after_lines: 10,
        }),
        ..ShellExecOptions::default()
    };
    let result = get(env
        .exec(&shell(r"printf '\146\200\000\157'"), &options, cx())
        .await);
    let spill_path = result.spill_path.expect("spill path");
    assert_eq!(
        get(env.read_binary_file(&spill_path, cx()).await),
        vec![0x66, 0x80, 0x00, 0x6f]
    );
    remove_spill_dir(&spill_path);
}

#[tokio::test]
async fn reports_the_spill_of_a_command_that_times_out() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let options = ShellExecOptions {
        timeout: Some(0.3),
        spill: Some(ShellSpillOptions {
            after_bytes: 10,
            after_lines: 10,
        }),
        ..ShellExecOptions::default()
    };
    let error = exec_error(
        env.exec(
            &shell("printf 12345678901234567890; sleep 5"),
            &options,
            cx(),
        )
        .await,
    );
    assert_eq!(error.code, ExecutionErrorCode::Timeout);
    let spill_path = error.spill_path.expect("spill path");
    assert_eq!(
        get(env.read_text_file(&spill_path, cx()).await),
        "12345678901234567890"
    );
    remove_spill_dir(&spill_path);
}

/// The TS test writes `'x'.repeat(500000)` from `node -e`.
#[tokio::test]
async fn preserves_complete_large_output_in_the_spill() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let size = 500_000;
    let options = ShellExecOptions {
        spill: Some(ShellSpillOptions {
            after_bytes: 10,
            after_lines: 10,
        }),
        ..ShellExecOptions::default()
    };
    let result = get(env
        .exec(
            &shell(&format!("head -c {size} /dev/zero | tr '\\0' x")),
            &options,
            cx(),
        )
        .await);
    let spill_path = result.spill_path.expect("spill path");
    assert_eq!(get(env.read_text_file(&spill_path, cx()).await).len(), size);
    remove_spill_dir(&spill_path);
}

#[tokio::test]
async fn streams_every_line_and_spills_them_all_once_output_crosses_its_line_threshold() {
    let fixture = temp_root();
    let env = native(&fixture.root);
    let (result, output) = collect_shell_output(
        &env,
        "i=1; while [ $i -le 15000 ]; do echo line-$i; i=$((i+1)); done",
        ShellExecOptions {
            spill: Some(ShellSpillOptions {
                after_bytes: 1024 * 1024,
                after_lines: 100,
            }),
            ..ShellExecOptions::default()
        },
        cx(),
    )
    .await;
    let result = get(result);
    let mut expected = String::new();
    for index in 1..=15000 {
        writeln!(expected, "line-{index}").expect("write to a String");
    }
    assert_eq!(output, expected);
    let spill_path = result.spill_path.expect("spill path");
    let spilled = get(env
        .read_text_lines(&spill_path, ReadTextLinesOptions::default(), cx())
        .await);
    assert_eq!(spilled.len(), 15000);
    assert_eq!(spilled.last().map(String::as_str), Some("line-15000"));
    remove_spill_dir(&spill_path);
}
