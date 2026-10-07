//! Port of `testing/env-conformance.ts` and of `registerEnvConformance` of
//! `testing/runner.ts`.

use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::{with_abort_signal, AbortController, Context, BACKGROUND_CONTEXT};
use futures::future::BoxFuture;
use tokio::time::Instant;

use super::types::{EnvConformanceCase, EnvConformanceOptions, EnvTest};
use crate::env::{
    CreateDirOptions, DirPage, ExecCommand, ExecutionEnv, ExecutionError, FileError, FileInfo,
    FileKind, FileWatcher, LineRange, OpenBinaryReaderOptions, OutputStream, RemoveOptions,
    ShellExecOptions, ShellExecResult, ShellOutputWindow, Utf8Decoder, WatchChange, WatchExclude,
    WatchMode, WatchTarget,
};

/// What a runner allows a case without its own timeout (Vitest's default).
const DEFAULT_TIMEOUT_MS: u64 = 5_000;

fn context() -> &'static Context {
    &BACKGROUND_CONTEXT
}

fn aborted_context() -> Context {
    let controller = AbortController::new();
    controller.abort(None);
    with_abort_signal(&controller.signal(), context())
}

/// The `code` of a failed result, as the TS string.
trait ErrorCode {
    fn code_str(&self) -> &'static str;
}

impl ErrorCode for FileError {
    fn code_str(&self) -> &'static str {
        self.code.as_str()
    }
}

impl ErrorCode for ExecutionError {
    fn code_str(&self) -> &'static str {
        self.code.as_str()
    }
}

fn error_code<T, E: ErrorCode>(result: &Result<T, E>) -> Option<&'static str> {
    result.as_ref().err().map(ErrorCode::code_str)
}

/// `getOrThrow`.
#[track_caller]
fn get<T, E: std::fmt::Debug>(result: Result<T, E>) -> T {
    match result {
        Ok(value) => value,
        Err(error) => panic!("unexpected failure: {error:?}"),
    }
}

/// `new TextDecoder().decode(bytes)`.
fn decode(bytes: &[u8]) -> String {
    let text = Utf8Decoder::new().decode_all(bytes);
    match text.strip_prefix('\u{feff}') {
        Some(rest) => rest.to_owned(),
        None => text,
    }
}

/// `new TextDecoder("utf-8", { ignoreBOM: from > 0 }).decode(bytes.subarray(from, to))`.
fn decode_range(bytes: &[u8], from: u64, to: u64) -> String {
    let from = usize::try_from(from).unwrap_or(usize::MAX).min(bytes.len());
    let to = usize::try_from(to).unwrap_or(usize::MAX).min(bytes.len());
    let slice = bytes.get(from..to.max(from)).unwrap_or_default();
    if from > 0 {
        Utf8Decoder::new().decode_all(slice)
    } else {
        decode(slice)
    }
}

/// JS `array.slice(start, end)` for non-negative bounds.
fn slice<T: Clone>(items: &[T], start: usize, end: Option<usize>) -> Vec<T> {
    let end = end.unwrap_or(items.len()).min(items.len());
    let start = start.min(end);
    items[start..end].to_vec()
}

async fn read_all(
    env: &dyn ExecutionEnv,
    path: &str,
    max_entries: f64,
) -> (Vec<Vec<FileInfo>>, bool) {
    let reader = get(env.open_dir_reader(path, context()).await);
    let mut pages = Vec::new();
    let mut done = false;
    for _ in 0..1000 {
        let next: DirPage = get(reader.next(max_entries, context()).await);
        pages.push(next.entries);
        if next.done {
            done = true;
            break;
        }
    }
    reader.close(context()).await;
    (pages, done)
}

/// Whether a change reports `path`: an overflow, or a reported path at or
/// above it.
fn covers(change: &WatchChange, path: &str) -> bool {
    match change {
        WatchChange::Overflow => true,
        WatchChange::Error(_) => false,
        WatchChange::Paths(paths) => paths.iter().any(|reported| {
            path == reported
                || path.starts_with(&format!("{reported}/"))
                || path.starts_with(&format!("{reported}\\"))
        }),
    }
}

/// A watch of `targets` while a case changes files: the TS `watching` helper.
struct Watching {
    env: Arc<dyn ExecutionEnv>,
    changes: Arc<Mutex<Vec<WatchChange>>>,
    watcher: Box<dyn FileWatcher>,
}

impl Watching {
    async fn start(env: &Arc<dyn ExecutionEnv>, targets: &[WatchTarget]) -> Self {
        let changes = Arc::new(Mutex::new(Vec::new()));
        let sink = Arc::clone(&changes);
        let on_change = Arc::new(move |change: WatchChange| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(change);
        });
        let watcher = get(env.watch(targets, on_change, context()).await);
        Self {
            env: Arc::clone(env),
            changes,
            watcher,
        }
    }

    fn changes(&self) -> Vec<WatchChange> {
        self.changes
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    async fn absolute(&self, path: &str) -> String {
        get(self.env.absolute_path(path, context()).await)
    }

    /// Wait up to three seconds for a change, after `change` started, that
    /// reports `path`.
    async fn expect_change<F: Future<Output = ()>>(&self, path: &str, change: F) {
        let target = self.absolute(path).await;
        let from = self.changes().len();
        change.await;
        let deadline = Instant::now() + Duration::from_millis(3000);
        loop {
            let changes = self.changes();
            if changes[from..].iter().any(|entry| covers(entry, &target)) {
                return;
            }
            assert!(
                Instant::now() <= deadline,
                "No change reported {target}; got {:?}",
                &changes[from..]
            );
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    }

    async fn close(self) {
        self.watcher.close(context()).await;
    }
}

/// Stdout and stderr of a command, collected through `on_output`.
struct Collected {
    result: Result<ShellExecResult, ExecutionError>,
    stdout: String,
    stderr: String,
}

async fn exec_collect(
    env: &dyn ExecutionEnv,
    command: ExecCommand,
    cwd: Option<&str>,
) -> Collected {
    let output = Arc::new(Mutex::new((String::new(), String::new())));
    let sink = Arc::clone(&output);
    let options = ShellExecOptions {
        cwd: cwd.map(str::to_owned),
        on_output: Some(Arc::new(move |text, _cx, info| {
            let mut output = sink.lock().unwrap_or_else(PoisonError::into_inner);
            match info.stream {
                OutputStream::Stdout => output.0.push_str(text),
                OutputStream::Stderr => output.1.push_str(text),
            }
            Ok(())
        })),
        ..ShellExecOptions::default()
    };
    let result = env.exec(&command, &options, context()).await;
    let (stdout, stderr) = output
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    Collected {
        result,
        stdout,
        stderr,
    }
}

fn argv(shell: &[String], rest: &[&str]) -> ExecCommand {
    ExecCommand::Argv(
        shell
            .iter()
            .cloned()
            .chain(rest.iter().map(|arg| (*arg).to_owned()))
            .collect(),
    )
}

fn target(path: &str) -> WatchTarget {
    WatchTarget {
        path: path.to_owned(),
        ..WatchTarget::default()
    }
}

fn recursive(path: &str) -> WatchTarget {
    WatchTarget {
        path: path.to_owned(),
        recursive: true,
        ..WatchTarget::default()
    }
}

/// Builds cases bound to one provider.
struct Cases {
    options: EnvConformanceOptions,
    cases: Vec<EnvConformanceCase>,
}

impl Cases {
    fn add<F, Fut>(&mut self, name: &'static str, timeout_ms: Option<u64>, test: F)
    where
        F: Fn(Arc<dyn ExecutionEnv>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = ()> + Send + 'static,
    {
        let with_env = Arc::clone(&self.options.with_env);
        let test = Arc::new(test);
        self.cases.push(EnvConformanceCase {
            name,
            timeout_ms,
            run: Arc::new(move || {
                let test = Arc::clone(&test);
                let body: EnvTest = Box::new(move |env| Box::pin(test(env)));
                with_env(body)
            }),
        });
    }

    fn case<F, Fut>(&mut self, name: &'static str, test: F)
    where
        F: Fn(Arc<dyn ExecutionEnv>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = ()> + Send + 'static,
    {
        self.add(name, None, test);
    }

    /// Watch cases wait up to three seconds per step, longer than test runners
    /// allow by default.
    fn watch_case<F, Fut>(&mut self, name: &'static str, test: F)
    where
        F: Fn(Arc<dyn ExecutionEnv>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = ()> + Send + 'static,
    {
        self.add(name, Some(30_000), test);
    }
}

/// Creates runner-independent cases for an [`ExecutionEnv`]. The provider must
/// call its test exactly once per case with an environment whose `cwd` is a
/// fresh, empty, writable directory.
#[must_use]
pub fn create_env_conformance(options: EnvConformanceOptions) -> Vec<EnvConformanceCase> {
    let shell: Arc<[String]> = options
        .shell
        .clone()
        .unwrap_or_else(|| vec!["sh".to_owned(), "-c".to_owned()])
        .into();
    let symlinks = options.symlinks.unwrap_or(true);
    let mut cases = Cases {
        options,
        cases: Vec::new(),
    };
    add_binary_reader_cases(&mut cases);
    add_line_scan_cases(&mut cases);
    add_binary_reader_refusal_cases(&mut cases);
    add_dir_reader_cases(&mut cases);
    add_dir_reader_refusal_cases(&mut cases);
    add_watch_cases(&mut cases);
    add_watch_replacement_cases(&mut cases);
    add_watch_close_cases(&mut cases);
    add_exec_cases(&mut cases, &shell);
    add_windowed_exec_cases(&mut cases, &shell);
    if symlinks {
        add_symlink_cases(&mut cases, &shell);
    }
    cases.cases
}

fn add_binary_reader_cases(cases: &mut Cases) {
    cases.case(
        "binary reader reads byte ranges of the opened file",
        |env| async move {
            get(env.write_file("data.txt", b"hello world", context()).await);
            let reader = get(env
                .open_binary_reader("data.txt", OpenBinaryReaderOptions::default(), context())
                .await);
            let info = get(reader.info(context()).await);
            assert_eq!(info.name, "data.txt");
            assert_eq!(info.kind, FileKind::File);
            assert_eq!(info.size, 11);
            assert_eq!(
                decode(&get(reader.read(0.0, 5.0, context()).await)),
                "hello"
            );
            assert_eq!(
                decode(&get(reader.read(6.0, 100.0, context()).await)),
                "world"
            );
            assert_eq!(get(reader.read(11.0, 4.0, context()).await).len(), 0);
            assert_eq!(get(reader.read(50.0, 1.0, context()).await).len(), 0);
            assert_eq!(get(reader.read(3.0, 0.0, context()).await).len(), 0);
            assert_eq!(
                error_code(&reader.read(-1.0, 1.0, context()).await),
                Some("invalid")
            );
            assert_eq!(
                error_code(&reader.read(0.0, 1.5, context()).await),
                Some("invalid")
            );
            assert_eq!(
                error_code(&reader.read(0.0, 1.0, &aborted_context()).await),
                Some("aborted")
            );
            reader.close(context()).await;
            reader.close(context()).await;
            assert_eq!(
                error_code(&reader.read(0.0, 1.0, context()).await),
                Some("invalid")
            );
            assert_eq!(error_code(&reader.info(context()).await), Some("invalid"));
        },
    );
}

fn add_line_scan_cases(cases: &mut Cases) {
    cases.case(
        "binary reader scans lines like decoding the whole file",
        |env| async move {
            // A byte-order mark, an invalid sequence before a newline, an empty
            // line, a later U+FEFF, and no final newline.
            let bytes: &[u8] = &[
                0xef, 0xbb, 0xbf, 0x61, 0x0a, 0xe2, 0x82, 0x0a, 0x0a, 0xef, 0xbb, 0xbf, 0x62, 0x0a,
                0xc3, 0xa9,
            ];
            get(env.write_file("lines.txt", bytes, context()).await);
            let whole = decode(bytes);
            let lines: Vec<&str> = whole.split('\n').collect();
            let reader = get(env
                .open_binary_reader("lines.txt", OpenBinaryReaderOptions::default(), context())
                .await);
            let ranges: [(usize, Option<usize>); 6] = [
                (0, None),
                (0, Some(1)),
                (1, Some(3)),
                (2, Some(3)),
                (3, None),
                (4, Some(9)),
            ];
            for (start_line, end_line) in ranges {
                #[allow(clippy::cast_precision_loss, reason = "small test line numbers")]
                let range = LineRange {
                    start_line: start_line as f64,
                    end_line: end_line.map(|end| end as f64),
                };
                let scan = get(reader.scan_lines(range, context()).await);
                let selected = slice(&lines, start_line, end_line).join("\n");
                assert_eq!(scan.newlines, (lines.len() - 1) as u64);
                assert_eq!(decode_range(bytes, scan.start, scan.end), selected);
                assert_eq!(scan.selected_bytes, selected.len() as u64);
                assert_eq!(
                    decode_range(bytes, scan.start, scan.first_line_end),
                    lines[start_line]
                );
                assert_eq!(scan.first_line_bytes, lines[start_line].len() as u64);
            }
            let past = get(reader
                .scan_lines(
                    LineRange {
                        start_line: 9.0,
                        end_line: None,
                    },
                    context(),
                )
                .await);
            assert_eq!(past.start, bytes.len() as u64);
            assert_eq!(past.end, bytes.len() as u64);
            assert_eq!(past.selected_bytes, 0);
            assert_eq!(
                error_code(
                    &reader
                        .scan_lines(
                            LineRange {
                                start_line: 2.0,
                                end_line: Some(2.0)
                            },
                            context()
                        )
                        .await
                ),
                Some("invalid")
            );
            reader.close(context()).await;
        },
    );
}

fn add_binary_reader_refusal_cases(cases: &mut Cases) {
    cases.case(
        "binary reader keeps reading the file it opened after a rename",
        |env| async move {
            get(env.write_file("a.txt", b"one", context()).await);
            let reader = get(env
                .open_binary_reader("a.txt", OpenBinaryReaderOptions::default(), context())
                .await);
            get(env.rename_file("a.txt", "b.txt", context()).await);
            get(env.write_file("a.txt", b"two", context()).await);
            assert_eq!(decode(&get(reader.read(0.0, 10.0, context()).await)), "one");
            reader.close(context()).await;
        },
    );

    cases.case(
        "binary reader refuses directories, missing files and aborted opens",
        |env| async move {
            get(env
                .create_dir("dir", CreateDirOptions::default(), context())
                .await);
            get(env.write_file("file.txt", b"x", context()).await);
            let options = OpenBinaryReaderOptions::default();
            assert_eq!(
                error_code(&env.open_binary_reader("dir", options, context()).await),
                Some("is_directory")
            );
            assert_eq!(
                error_code(
                    &env.open_binary_reader("missing.txt", options, context())
                        .await
                ),
                Some("not_found")
            );
            assert_eq!(
                error_code(
                    &env.open_binary_reader("file.txt", options, &aborted_context())
                        .await
                ),
                Some("aborted")
            );
        },
    );
}

fn add_dir_reader_cases(cases: &mut Cases) {
    cases.case(
        "directory reader pages every entry exactly once",
        |env| async move {
            let names = ["a.txt", "b.txt", "c.txt", "d.txt", "e.txt"];
            for name in names {
                get(env.write_file(name, name.as_bytes(), context()).await);
            }
            get(env
                .create_dir("sub", CreateDirOptions::default(), context())
                .await);
            let (pages, done) = read_all(env.as_ref(), ".", 2.0).await;
            assert!(done, "directory reader reached the end");
            for page in &pages {
                assert!(page.len() <= 2, "page within maxEntries");
            }
            let entries: Vec<FileInfo> = pages.into_iter().flatten().collect();
            let mut listed: Vec<&str> = entries.iter().map(|entry| entry.name.as_str()).collect();
            listed.sort_unstable();
            let mut expected: Vec<&str> = names.iter().copied().chain(["sub"]).collect();
            expected.sort_unstable();
            assert_eq!(listed, expected);
            assert_eq!(
                entries
                    .iter()
                    .find(|entry| entry.name == "sub")
                    .map(|entry| entry.kind),
                Some(FileKind::Directory)
            );
            let a = entries
                .iter()
                .find(|entry| entry.name == "a.txt")
                .expect("a.txt listed");
            assert_eq!((a.kind, a.size), (FileKind::File, 5));
        },
    );

    cases.case(
        "directory reader reports the end and refuses use after close",
        |env| async move {
            get(env
                .create_dir("empty", CreateDirOptions::default(), context())
                .await);
            let reader = get(env.open_dir_reader("empty", context()).await);
            let end = DirPage {
                entries: Vec::new(),
                done: true,
            };
            assert_eq!(get(reader.next(10.0, context()).await), end);
            assert_eq!(get(reader.next(10.0, context()).await), end);
            assert_eq!(
                error_code(&reader.next(0.0, context()).await),
                Some("invalid")
            );
            assert_eq!(
                error_code(&reader.next(1.0, &aborted_context()).await),
                Some("aborted")
            );
            reader.close(context()).await;
            reader.close(context()).await;
            assert_eq!(
                error_code(&reader.next(1.0, context()).await),
                Some("invalid")
            );
        },
    );
}

fn add_dir_reader_refusal_cases(cases: &mut Cases) {
    cases.case(
        "directory reader refuses missing paths and files",
        |env| async move {
            get(env.write_file("file.txt", b"x", context()).await);
            assert_eq!(
                error_code(&env.open_dir_reader("missing", context()).await),
                Some("not_found")
            );
            assert_eq!(
                error_code(&env.open_dir_reader("file.txt", context()).await),
                Some("not_directory")
            );
            assert_eq!(
                error_code(&env.open_dir_reader(".", &aborted_context()).await),
                Some("aborted")
            );
        },
    );

    cases.case(
        "directory reader skips entries removed during enumeration",
        |env| async move {
            get(env
                .create_dir("dir", CreateDirOptions::default(), context())
                .await);
            for name in ["x", "y", "z"] {
                get(env
                    .write_file(&format!("dir/{name}"), name.as_bytes(), context())
                    .await);
            }
            let reader = get(env.open_dir_reader("dir", context()).await);
            for name in ["x", "y", "z"] {
                get(env
                    .remove(&format!("dir/{name}"), RemoveOptions::default(), context())
                    .await);
            }
            let mut entries = Vec::new();
            for _ in 0..10 {
                let next = get(reader.next(10.0, context()).await);
                entries.extend(next.entries);
                if next.done {
                    break;
                }
            }
            assert_eq!(entries, Vec::new());
            reader.close(context()).await;
        },
    );
}

async fn write(env: &dyn ExecutionEnv, path: &str, content: &str) {
    get(env.write_file(path, content.as_bytes(), context()).await);
}

fn add_watch_cases(cases: &mut Cases) {
    cases.watch_case(
        "watch reports a missing file's creation, changes, replacement and removal",
        |env| async move {
            let watching = Watching::start(&env, &[target("AGENTS.md")]).await;
            watching
                .expect_change("AGENTS.md", write(env.as_ref(), "AGENTS.md", "one"))
                .await;
            watching
                .expect_change("AGENTS.md", write(env.as_ref(), "AGENTS.md", "two!"))
                .await;
            // Editors replace a file by renaming a new one over it.
            watching
                .expect_change("AGENTS.md", async {
                    write(env.as_ref(), "AGENTS.md.tmp", "three").await;
                    get(env
                        .rename_file("AGENTS.md.tmp", "AGENTS.md", context())
                        .await);
                })
                .await;
            watching
                .expect_change("AGENTS.md", write(env.as_ref(), "AGENTS.md", "four"))
                .await;
            watching
                .expect_change("AGENTS.md", async {
                    get(env
                        .remove("AGENTS.md", RemoveOptions::default(), context())
                        .await);
                })
                .await;
            watching.close().await;
        },
    );

    cases.watch_case(
        "watch reports a missing target whose ancestors are created",
        |env| async move {
            let watching = Watching::start(&env, &[target("a/b/c/AGENTS.md")]).await;
            watching
                .expect_change(
                    "a/b/c/AGENTS.md",
                    write(env.as_ref(), "a/b/c/AGENTS.md", "x"),
                )
                .await;
            watching.close().await;
        },
    );

    cases.watch_case(
        "watch follows directories created together with their contents",
        |env| async move {
            get(env
                .create_dir("skills", CreateDirOptions::default(), context())
                .await);
            let watching = Watching::start(&env, &[recursive("skills")]).await;
            // Written before any watcher on the new directories can exist.
            watching
                .expect_change(
                    "skills/a/b/SKILL.md",
                    write(env.as_ref(), "skills/a/b/SKILL.md", "one"),
                )
                .await;
            watching
                .expect_change(
                    "skills/a/b/SKILL.md",
                    write(env.as_ref(), "skills/a/b/SKILL.md", "two!"),
                )
                .await;
            watching
                .expect_change(
                    "skills/a/b/c/SKILL.md",
                    write(env.as_ref(), "skills/a/b/c/SKILL.md", "deeper"),
                )
                .await;
            watching.close().await;
        },
    );

    cases.watch_case(
        "watch keeps watching a path whose parent is renamed and recreated",
        |env| async move {
            write(env.as_ref(), "proj/.pi/skills/x.md", "x").await;
            let watching = Watching::start(&env, &[recursive("proj/.pi/skills")]).await;
            watching
                .expect_change("proj/.pi/skills", async {
                    get(env.rename_file("proj/.pi", "proj/old", context()).await);
                })
                .await;
            watching
                .expect_change(
                    "proj/.pi/skills/y.md",
                    write(env.as_ref(), "proj/.pi/skills/y.md", "y"),
                )
                .await;
            watching
                .expect_change(
                    "proj/.pi/skills/y.md",
                    write(env.as_ref(), "proj/.pi/skills/y.md", "yy"),
                )
                .await;
            watching.close().await;
        },
    );
}

fn add_watch_replacement_cases(cases: &mut Cases) {
    cases.watch_case(
        "watch skips excluded entries and reports a rename out of them",
        |env| async move {
            get(env
                .create_dir("skills", CreateDirOptions::default(), context())
                .await);
            let targets = [WatchTarget {
                path: "skills".to_owned(),
                recursive: true,
                exclude: WatchExclude {
                    hidden: true,
                    names: vec!["node_modules".to_owned()],
                },
            }];
            let watching = Watching::start(&env, &targets).await;
            write(env.as_ref(), "skills/node_modules/dep/SKILL.md", "dep").await;
            write(env.as_ref(), "skills/.SKILL.md.tmp", "draft").await;
            watching
                .expect_change("skills/SKILL.md", async {
                    get(env
                        .rename_file("skills/.SKILL.md.tmp", "skills/SKILL.md", context())
                        .await);
                })
                .await;
            let hidden = [
                watching.absolute("skills/node_modules").await,
                watching.absolute("skills/.SKILL.md.tmp").await,
            ];
            for change in watching.changes() {
                let WatchChange::Paths(paths) = change else {
                    continue;
                };
                for path in paths {
                    assert!(
                        !hidden.iter().any(
                            |excluded| path == *excluded || path.starts_with(excluded.as_str())
                        ),
                        "excluded {path}"
                    );
                }
            }
            watching.close().await;
        },
    );

    cases.watch_case(
        "watch keeps recursive coverage where a non-recursive target overlaps",
        |env| async move {
            write(env.as_ref(), "skills/a/one.md", "one").await;
            let watching = Watching::start(&env, &[target("skills"), recursive("skills")]).await;
            watching
                .expect_change(
                    "skills/a/two.md",
                    write(env.as_ref(), "skills/a/two.md", "two"),
                )
                .await;
            watching.close().await;
        },
    );

    cases.watch_case(
        "watch follows a directory replaced at the same path",
        |env| async move {
            write(env.as_ref(), "skills/a/x.md", "x").await;
            let watching = Watching::start(&env, &[recursive("skills")]).await;
            watching
                .expect_change("skills/a", async {
                    get(env.rename_file("skills/a", "skills-old", context()).await);
                    get(env
                        .create_dir("skills/a", CreateDirOptions::default(), context())
                        .await);
                })
                .await;
            watching
                .expect_change("skills/a/y.md", write(env.as_ref(), "skills/a/y.md", "y"))
                .await;
            watching
                .expect_change("skills/a/y.md", write(env.as_ref(), "skills/a/y.md", "yy"))
                .await;
            watching.close().await;
        },
    );
}

fn add_watch_close_cases(cases: &mut Cases) {
    cases.watch_case("watch stops reporting once closed", |env| async move {
        let changes = Arc::new(Mutex::new(Vec::new()));
        let sink = Arc::clone(&changes);
        let on_change = Arc::new(move |change: WatchChange| {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(change);
        });
        let watcher = get(env.watch(&[target("file.txt")], on_change, context()).await);
        assert!(
            matches!(watcher.mode(), WatchMode::Native | WatchMode::Polling),
            "watcher reports its mode"
        );
        watcher.close(context()).await;
        watcher.close(context()).await;
        write(env.as_ref(), "file.txt", "x").await;
        tokio::time::sleep(Duration::from_millis(300)).await;
        assert!(changes
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .is_empty());
    });
}

fn add_exec_cases(cases: &mut Cases, shell: &Arc<[String]>) {
    let sh = Arc::clone(shell);
    cases.case(
        "argv exec passes arguments to the program without shell parsing",
        move |env| {
            let sh = Arc::clone(&sh);
            async move {
                let hostile = "it's $(touch pwned) `touch pwned` *; touch pwned";
                let collected = exec_collect(
                    env.as_ref(),
                    argv(
                        &sh,
                        &[r#"printf "%s|%s" "$1" "$2""#, "argv0", hostile, "a b"],
                    ),
                    None,
                )
                .await;
                assert_eq!(get(collected.result).exit_code, 0);
                assert_eq!(collected.stdout, format!("{hostile}|a b"));
                assert!(!get(env.exists("pwned", context()).await));
            }
        },
    );

    let sh = Arc::clone(shell);
    cases.case(
        "exec reports the stream of every chunk in both forms",
        move |env| {
            let sh = Arc::clone(&sh);
            async move {
                let script = "printf out; printf err >&2; printf more";
                let argv = exec_collect(env.as_ref(), argv(&sh, &[script]), None).await;
                assert_eq!(get(argv.result).exit_code, 0);
                assert_eq!(argv.stdout, "outmore");
                assert_eq!(argv.stderr, "err");
                let string =
                    exec_collect(env.as_ref(), ExecCommand::Shell(script.to_owned()), None).await;
                assert_eq!(get(string.result).exit_code, 0);
                assert_eq!(string.stdout, "outmore");
                assert_eq!(string.stderr, "err");
            }
        },
    );

    let sh = Arc::clone(shell);
    cases.case("argv exec honors cwd and exit codes", move |env| {
        let sh = Arc::clone(&sh);
        async move {
            get(env
                .create_dir("sub", CreateDirOptions::default(), context())
                .await);
            let made = exec_collect(
                env.as_ref(),
                argv(&sh, &["printf x > made.txt; exit 3"]),
                Some("sub"),
            )
            .await;
            assert_eq!(get(made.result).exit_code, 3);
            assert_eq!(
                get(env.read_text_file("sub/made.txt", context()).await),
                "x"
            );
        }
    });

    cases.case(
        "argv exec reports missing programs and empty argv as spawn errors",
        |env| async move {
            let missing =
                ExecCommand::Argv(vec!["pi-durable-conformance-missing-program".to_owned()]);
            let options = ShellExecOptions::default();
            assert_eq!(
                error_code(&env.exec(&missing, &options, context()).await),
                Some("spawn_error")
            );
            assert_eq!(
                error_code(
                    &env.exec(&ExecCommand::Argv(Vec::new()), &options, context())
                        .await
                ),
                Some("spawn_error")
            );
        },
    );
}

fn add_windowed_exec_cases(cases: &mut Cases, shell: &Arc<[String]>) {
    let sh = Arc::clone(shell);
    cases.case(
        "windowed exec keeps the exact tail and counts what it skips",
        move |env| {
            let sh = Arc::clone(&sh);
            async move {
                let lines = 2000;
                let window = ShellOutputWindow {
                    max_bytes: 200,
                    max_lines: 5,
                    min_interval_ms: 0.0,
                    bytes_per_second: 1_000_000_000.0,
                };
                // (bytes, newlines, tail, skip violations)
                let state = Arc::new(Mutex::new((
                    0_usize,
                    0_usize,
                    String::new(),
                    Vec::<String>::new(),
                )));
                let sink = Arc::clone(&state);
                let options = ShellExecOptions {
                    window: Some(window),
                    on_output: Some(Arc::new(move |text, _cx, info| {
                        let mut state = sink.lock().unwrap_or_else(PoisonError::into_inner);
                        let newlines = text.matches('\n').count();
                        if let Some(skipped) = info.skipped {
                            state.0 += usize::try_from(skipped.bytes).unwrap_or(usize::MAX);
                            state.1 += usize::try_from(skipped.newlines).unwrap_or(usize::MAX);
                            if !(text.len() as u64 > window.max_bytes
                                || newlines as u64 > window.max_lines)
                            {
                                state.3.push(text.to_owned());
                            }
                            state.2.clear();
                        }
                        state.0 += text.len();
                        state.1 += newlines;
                        state.2.push_str(text);
                        Ok(())
                    })),
                    ..ShellExecOptions::default()
                };
                let script =
                    format!("i=0; while [ $i -lt {lines} ]; do echo line-$i; i=$((i+1)); done");
                let result = env.exec(&argv(&sh, &[&script]), &options, context()).await;
                assert_eq!(get(result).exit_code, 0);
                let state = state.lock().unwrap_or_else(PoisonError::into_inner);
                assert!(
                    state.3.is_empty(),
                    "a skip is followed by more than the window"
                );
                let expected: Vec<String> =
                    (0..lines).map(|index| format!("line-{index}\n")).collect();
                assert_eq!(state.0, expected.concat().len());
                assert_eq!(state.1, lines);
                assert!(
                    state.2.ends_with(&expected[expected.len() - 5..].concat()),
                    "the delivered output ends with the tail"
                );
            }
        },
    );

    let sh = Arc::clone(shell);
    cases.case("argv exec distinguishes timeout from abort", move |env| {
        let sh = Arc::clone(&sh);
        async move {
            let timeout = ShellExecOptions {
                timeout: Some(0.1),
                ..ShellExecOptions::default()
            };
            let timed_out = env
                .exec(&argv(&sh, &["sleep 2"]), &timeout, context())
                .await;
            assert_eq!(error_code(&timed_out), Some("timeout"));
            let controller = AbortController::new();
            let cx = with_abort_signal(&controller.signal(), context());
            let abort = tokio::spawn(async move {
                tokio::time::sleep(Duration::from_millis(100)).await;
                controller.abort(None);
            });
            let running = env
                .exec(&argv(&sh, &["sleep 2"]), &ShellExecOptions::default(), &cx)
                .await;
            assert_eq!(error_code(&running), Some("aborted"));
            get(abort.await);
        }
    });
}

fn add_symlink_cases(cases: &mut Cases, shell: &Arc<[String]>) {
    let sh = Arc::clone(shell);
    cases.case(
        "binary reader follows symlinks unless noFollow refuses the final one",
        move |env| {
            let sh = Arc::clone(&sh);
            async move {
                write(env.as_ref(), "target.txt", "target").await;
                get(env
                    .create_dir("sub", CreateDirOptions::default(), context())
                    .await);
                write(env.as_ref(), "sub/inner.txt", "inner").await;
                let linked = env
                    .exec(
                        &argv(&sh, &["ln -s target.txt link.txt && ln -s sub dirlink"]),
                        &ShellExecOptions::default(),
                        context(),
                    )
                    .await;
                assert_eq!(get(linked).exit_code, 0);

                let followed = get(env
                    .open_binary_reader("link.txt", OpenBinaryReaderOptions::default(), context())
                    .await);
                assert_eq!(
                    decode(&get(followed.read(0.0, 10.0, context()).await)),
                    "target"
                );
                followed.close(context()).await;

                let no_follow = OpenBinaryReaderOptions { no_follow: true };
                assert_eq!(
                    error_code(
                        &env.open_binary_reader("link.txt", no_follow, context())
                            .await
                    ),
                    Some("invalid")
                );

                // Only the final component is refused; earlier symlinked directories
                // still resolve.
                let inner = get(env
                    .open_binary_reader("dirlink/inner.txt", no_follow, context())
                    .await);
                assert_eq!(
                    decode(&get(inner.read(0.0, 10.0, context()).await)),
                    "inner"
                );
                inner.close(context()).await;
            }
        },
    );

    let sh = Arc::clone(shell);
    cases.watch_case(
        "watch reports changes to the file a watched symbolic link points to",
        move |env| {
            let sh = Arc::clone(&sh);
            async move {
                write(env.as_ref(), "data/real.md", "one").await;
                get(env
                    .create_dir("config", CreateDirOptions::default(), context())
                    .await);
                let linked = env
                    .exec(
                        &argv(&sh, &["ln -s ../data/real.md config/AGENTS.md"]),
                        &ShellExecOptions::default(),
                        context(),
                    )
                    .await;
                assert_eq!(get(linked).exit_code, 0);
                let watching = Watching::start(&env, &[target("config/AGENTS.md")]).await;
                watching
                    .expect_change(
                        "config/AGENTS.md",
                        write(env.as_ref(), "data/real.md", "two!"),
                    )
                    .await;
                watching.close().await;
            }
        },
    );
}

/// Run every case against `options.with_env`, concurrently, each within its
/// timeout (5 s by default, like Vitest), the Rust counterpart of
/// `registerEnvConformance`.
///
/// # Panics
///
/// Panics after all cases ran when any failed or timed out, listing them under
/// `suite`.
pub async fn run_env_conformance(suite: &str, options: EnvConformanceOptions) {
    let cases = create_env_conformance(options);
    let mut running: Vec<(&'static str, BoxFuture<'static, Result<(), String>>)> = Vec::new();
    for case in &cases {
        let timeout = Duration::from_millis(case.timeout_ms.unwrap_or(DEFAULT_TIMEOUT_MS));
        let task = tokio::spawn(case.run());
        running.push((
            case.name,
            Box::pin(async move {
                match tokio::time::timeout(timeout, task).await {
                    Err(_) => Err(format!("timed out after {} ms", timeout.as_millis())),
                    Ok(Err(error)) => Err(panic_message(error)),
                    Ok(Ok(())) => Ok(()),
                }
            }),
        ));
    }
    let mut failures = Vec::new();
    for (name, outcome) in running {
        if let Err(message) = outcome.await {
            failures.push(format!("{suite} > {name}: {message}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} conformance case(s) failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

fn panic_message(error: tokio::task::JoinError) -> String {
    match error.try_into_panic() {
        Ok(panic) => panic
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_owned()))
            .unwrap_or_else(|| "panicked".to_owned()),
        Err(error) => error.to_string(),
    }
}
