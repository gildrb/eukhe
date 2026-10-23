//! The bridge between the commit log of [`JsonlStorage`] and its Bend model
//! (`bend/log.bend`, whose laws `PROOF.bend` proves): both run the same
//! scenarios and must print the same transcript, byte for byte.
//!
//! A scenario is a list of epochs (`bridge/bridge_log.bend` documents the
//! events). Each epoch opens the storage with fsync over [`CrashFs`], a
//! native file system that does the first `p` steps (appends, file
//! flushes, directory flushes) and then loses power: every later step
//! fails. The epoch commits until a commit fails, prints the sequences it
//! acknowledged, and then applies the power loss to the real files: each
//! file keeps its flushed bytes and the first `k` bytes that are not
//! flushed; with `drop`, each directory entry not flushed goes too. A
//! plain open then prints the sequences it reads.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, JsonValue};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::json;

use super::{CommitHistory, JsonlStorage, JsonlStorageOptions};
use crate::env::{
    BinaryReader, CreateDirOptions, DirReader, FileError, FileErrorCode, FileInfo, FileSystem,
    FileWatcher, NativeExecutionEnv, NativeExecutionEnvOptions, OnWatchChange,
    OpenBinaryReaderOptions, ReadTextLinesOptions, RemoveOptions, TempFileOptions, TextLineReader,
    WatchTarget,
};
use crate::testing::bridge::{compare, Rng, Scenario};
use crate::types::{Storage, StorageWrite, ROOT_CONVERSATION_ID};

/// What the power loss of [`CrashFs`] knows of the files.
#[derive(Default)]
struct Disk {
    /// The steps that still succeed.
    left: usize,
    /// The power is off: every step fails.
    off: bool,
    /// The flushed length of each file the storage wrote or truncated.
    flushed: HashMap<PathBuf, u64>,
    /// The entries created and not flushed into their directory yet.
    fresh: Vec<PathBuf>,
    /// The bytes of each append to `main.jsonl`, in order.
    markers: Vec<Vec<u8>>,
}

/// A native file system that loses power after `left` steps (see the
/// module docs). Only the calls of an fsync commit log are modelled: a
/// write, a rename or a remove panics.
struct CrashFs {
    inner: NativeExecutionEnv,
    disk: Mutex<Disk>,
}

fn lost(path: &str) -> FileError {
    FileError::new(FileErrorCode::Unknown, "power loss", Some(path.to_owned()))
}

fn size_of(path: &Path) -> u64 {
    std::fs::metadata(path).map_or(0, |metadata| metadata.len())
}

impl CrashFs {
    fn new(cwd: &Path, steps: usize) -> Arc<Self> {
        Arc::new(Self {
            inner: NativeExecutionEnv::new(NativeExecutionEnvOptions {
                cwd: cwd.to_string_lossy().into_owned(),
                ..NativeExecutionEnvOptions::default()
            }),
            disk: Mutex::new(Disk {
                left: steps,
                ..Disk::default()
            }),
        })
    }

    fn disk(&self) -> std::sync::MutexGuard<'_, Disk> {
        self.disk.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Take one step, or fail when the power is off (or goes off now).
    fn step(&self, path: &str) -> Result<(), FileError> {
        let mut disk = self.disk();
        if disk.off || disk.left == 0 {
            disk.off = true;
            return Err(lost(path));
        }
        disk.left -= 1;
        Ok(())
    }

    /// The bytes of `path` not flushed: its size beyond its flushed length.
    fn unflushed(&self, path: &Path) -> u64 {
        let flushed = self.disk().flushed.get(path).copied();
        size_of(path).saturating_sub(flushed.unwrap_or_else(|| size_of(path)))
    }

    /// Apply the power loss: keep the flushed bytes of each file and the
    /// first `keep` bytes after them; with `drop`, remove each entry not
    /// flushed into its directory.
    fn power_loss(&self, keep: u64, drop: bool) {
        let disk = self.disk();
        for (path, flushed) in &disk.flushed {
            let size = size_of(path);
            if size > flushed + keep {
                let file = std::fs::OpenOptions::new()
                    .write(true)
                    .open(path)
                    .expect("open a file to cut");
                file.set_len(flushed + keep).expect("cut a file");
            }
        }
        if drop {
            for path in disk.fresh.iter().rev() {
                let removed = if path.is_dir() {
                    std::fs::remove_dir_all(path)
                } else {
                    std::fs::remove_file(path)
                };
                match removed {
                    Ok(()) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => panic!("drop {}: {error}", path.display()),
                }
            }
        }
    }
}

impl FileSystem for CrashFs {
    fn id(&self) -> &str {
        self.inner.id()
    }
    fn cwd(&self) -> &str {
        FileSystem::cwd(&self.inner)
    }
    fn absolute_path<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        self.inner.absolute_path(path, cx)
    }
    fn join_path<'a>(
        &'a self,
        parts: &'a [&'a str],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        self.inner.join_path(parts, cx)
    }
    fn read_text_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        self.inner.read_text_file(path, cx)
    }
    fn open_text_line_reader<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn TextLineReader>, FileError>> {
        self.inner.open_text_line_reader(path, cx)
    }
    fn read_text_lines<'a>(
        &'a self,
        path: &'a str,
        options: ReadTextLinesOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<String>, FileError>> {
        self.inner.read_text_lines(path, options, cx)
    }
    fn read_binary_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<u8>, FileError>> {
        self.inner.read_binary_file(path, cx)
    }
    fn open_binary_reader<'a>(
        &'a self,
        path: &'a str,
        options: OpenBinaryReaderOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn BinaryReader>, FileError>> {
        self.inner.open_binary_reader(path, options, cx)
    }
    fn write_file<'a>(
        &'a self,
        path: &'a str,
        _content: &'a [u8],
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        panic!("bend/log.bend models no write of {path}")
    }
    fn append_file<'a>(
        &'a self,
        path: &'a str,
        content: &'a [u8],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            self.step(path)?;
            let file = PathBuf::from(path);
            if !file.exists() {
                self.disk().fresh.push(file.clone());
            }
            self.disk()
                .flushed
                .entry(file.clone())
                .or_insert_with(|| size_of(&file));
            if file.file_name().is_some_and(|name| name == "main.jsonl") {
                self.disk().markers.push(content.to_vec());
            }
            self.inner.append_file(path, content, cx).await
        }
        .boxed()
    }
    fn truncate_file<'a>(
        &'a self,
        path: &'a str,
        size: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            self.inner.truncate_file(path, size, cx).await?;
            // An open cuts a torn tail; the model takes the cut as durable.
            let file = PathBuf::from(path);
            let size = size_of(&file);
            self.disk()
                .flushed
                .entry(file)
                .and_modify(|flushed| *flushed = (*flushed).min(size))
                .or_insert(size);
            Ok(())
        }
        .boxed()
    }
    fn flush_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            self.step(path)?;
            self.inner.flush_file(path, cx).await?;
            let file = PathBuf::from(path);
            let size = size_of(&file);
            self.disk().flushed.insert(file, size);
            Ok(())
        }
        .boxed()
    }
    fn flush_directory<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            self.step(path)?;
            self.inner.flush_directory(path, cx).await?;
            let dir = Path::new(path);
            self.disk()
                .fresh
                .retain(|entry| entry.parent() != Some(dir));
            Ok(())
        }
        .boxed()
    }
    fn rename_file<'a>(
        &'a self,
        source_path: &'a str,
        _destination_path: &'a str,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        panic!("bend/log.bend models no rename of {source_path}")
    }
    fn file_info<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<FileInfo, FileError>> {
        self.inner.file_info(path, cx)
    }
    fn list_dir<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<FileInfo>, FileError>> {
        self.inner.list_dir(path, cx)
    }
    fn open_dir_reader<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn DirReader>, FileError>> {
        self.inner.open_dir_reader(path, cx)
    }
    fn watch<'a>(
        &'a self,
        targets: &'a [WatchTarget],
        on_change: OnWatchChange,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn FileWatcher>, FileError>> {
        self.inner.watch(targets, on_change, cx)
    }
    fn canonical_path<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        self.inner.canonical_path(path, cx)
    }
    fn exists<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<bool, FileError>> {
        self.inner.exists(path, cx)
    }
    fn create_dir<'a>(
        &'a self,
        path: &'a str,
        options: CreateDirOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            let dir = PathBuf::from(path);
            if !dir.exists() {
                self.disk().fresh.push(dir);
            }
            self.inner.create_dir(path, options, cx).await
        }
        .boxed()
    }
    fn remove<'a>(
        &'a self,
        path: &'a str,
        _options: RemoveOptions,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        panic!("bend/log.bend models no remove of {path}")
    }
    fn create_temp_dir<'a>(
        &'a self,
        prefix: Option<&'a str>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        self.inner.create_temp_dir(prefix, cx)
    }
    fn create_temp_file<'a>(
        &'a self,
        options: TempFileOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        self.inner.create_temp_file(options, cx)
    }
    fn cleanup<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()> {
        FileSystem::cleanup(&self.inner, cx)
    }
}

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

fn write(value: serde_json::Value) -> StorageWrite {
    from_json(&JsonValue::from(value)).expect("a valid write")
}

/// The sequences a plain open of `dir` reads.
async fn read_back(dir: &str) -> Vec<u64> {
    let fs = Arc::new(NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: dir.to_owned(),
        ..NativeExecutionEnvOptions::default()
    }));
    let storage = JsonlStorage::open(
        dir,
        fs,
        cx(),
        JsonlStorageOptions {
            fsync: false,
            history: CommitHistory::Keep,
        },
    )
    .await
    .expect("an open after the crash");
    let seqs = storage
        .take_history()
        .into_iter()
        .map(|commit| commit.seq.get())
        .collect();
    storage.close(cx()).await.expect("close");
    seqs
}

fn show(head: &str, seqs: &[u64]) -> String {
    let mut text = head.to_owned();
    for seq in seqs {
        let _ = write!(text, " {seq}");
    }
    text.push('\n');
    text
}

/// How many bytes not flushed a crash keeps.
#[derive(Clone, Copy)]
enum Keep {
    /// A number drawn from the generator: 0, 1, all but one, all, or any.
    Drawn,
    /// Exactly this many.
    Bytes(u64),
}

/// One epoch of a scenario: the commits it tries, the steps before the
/// crash, the bytes the crash keeps, whether it drops the entries.
struct Epoch {
    commits: usize,
    steps: usize,
    keep: Keep,
    drop: bool,
}

/// Run `epochs` on a fresh storage; return the events and the transcript.
async fn run(name: String, epochs: &[Epoch], rng: &mut Rng) -> Scenario {
    let root = tempfile::tempdir().expect("temp dir");
    let sessions = root.path().join("sessions");
    std::fs::create_dir(&sessions).expect("sessions dir");
    let dir = sessions.join("s");
    let dir_text = dir.to_string_lossy().into_owned();
    let main = dir.join("main.jsonl");
    let (mut events, mut transcript) = (String::new(), String::new());
    let mut has_root = false;
    let mut entry: u64 = 1000;
    for epoch in epochs {
        let fs = CrashFs::new(&sessions, epoch.steps);
        let mut acked = Vec::new();
        if let Ok(storage) = JsonlStorage::open(
            &dir_text,
            fs.clone(),
            cx(),
            JsonlStorageOptions {
                fsync: true,
                history: CommitHistory::Drop,
            },
        )
        .await
        {
            for _ in 0..epoch.commits {
                let value = if has_root {
                    entry += 1;
                    let kind = "k".repeat(usize::try_from(rng.range(1, 40)).unwrap_or(1));
                    json!({
                        "type": "entry",
                        "value": { "id": entry, "conversationId": ROOT_CONVERSATION_ID.get(), "kind": kind },
                    })
                } else {
                    json!({ "type": "conversation", "value": { "id": ROOT_CONVERSATION_ID.get() } })
                };
                match storage.commit(&[write(value)], cx()).await {
                    Ok(seq) => {
                        has_root = true;
                        acked.push(seq.get());
                    }
                    Err(_) => break,
                }
            }
        }
        let pending = fs.unflushed(&main);
        let keep = match epoch.keep {
            Keep::Bytes(bytes) => bytes,
            Keep::Drawn => match rng.below(5) {
                0 => 0,
                1 => 1.min(pending),
                2 => pending.saturating_sub(1),
                3 => pending,
                _ => rng.range(0, pending + 3),
            },
        };
        let _ = writeln!(events, "e {} {keep} {}", epoch.steps, u8::from(epoch.drop));
        for marker in &fs.disk().markers {
            let value: serde_json::Value =
                serde_json::from_slice(marker).expect("a marker is JSON");
            let seq = value["seq"].as_u64().expect("a marker has its seq");
            let _ = writeln!(events, "c {seq} {}", marker.len());
        }
        transcript.push_str(&show("a", &acked));
        fs.power_loss(keep, epoch.drop);
        let read = read_back(&dir_text).await;
        has_root = !read.is_empty();
        transcript.push_str(&show("r", &read));
    }
    Scenario {
        name,
        events,
        transcript,
    }
}

/// The steps of an epoch with `commits` commits that runs to its end:
/// the parent flush, then three steps for the first commit (append,
/// flush, directory flush) and two for each other one.
fn steps_of(commits: usize) -> usize {
    match commits {
        0 => 1,
        more => 2 * more + 2,
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn the_commit_log_runs_as_its_model() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let mut scenarios = Vec::new();
    // Every crash point of a first epoch of three commits, each with no
    // byte, a torn line or the whole line kept, with and without the
    // directory entries dropped; a second epoch then commits again.
    for steps in 0..=steps_of(3) + 1 {
        for keep in [Keep::Bytes(0), Keep::Bytes(7), Keep::Drawn] {
            for drop in [false, true] {
                let epochs = [
                    Epoch {
                        commits: 3,
                        steps,
                        keep,
                        drop,
                    },
                    Epoch {
                        commits: 2,
                        steps: steps_of(2),
                        keep: Keep::Drawn,
                        drop,
                    },
                ];
                let name = format!("point {steps} drop {drop}");
                scenarios.push(run(name, &epochs, &mut rng).await);
            }
        }
    }
    // Random histories of up to four epochs.
    for at in 0..120 {
        let epochs: Vec<Epoch> = (0..rng.range(1, 4))
            .map(|_| {
                let commits = usize::try_from(rng.range(0, 4)).unwrap_or(0);
                Epoch {
                    commits,
                    steps: usize::try_from(
                        rng.range(0, 1 + u64::try_from(steps_of(commits)).unwrap_or(0)),
                    )
                    .unwrap_or(0),
                    keep: Keep::Drawn,
                    drop: rng.chance(50),
                }
            })
            .collect();
        scenarios.push(run(format!("random {at}"), &epochs, &mut rng).await);
    }
    compare("bridge/bridge_log.bend", scenarios);
}
