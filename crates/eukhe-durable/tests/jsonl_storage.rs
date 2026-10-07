//! Port of `test/jsonl-storage.test.ts` ("Pico `JsonlStorage` publication and
//! recovery"; the storage conformance registrations live with the shared
//! conformance suite).

use std::io::Write as _;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::errors::StorageError;
use eukhe_durable::ids::mint;
use eukhe_durable::storage::jsonl::{open_native_jsonl_storage, JsonlStorage, JsonlStorageOptions};
use eukhe_durable::types::{
    AnyTaskRecord, DocumentAddress, DocumentId, DocumentPoint, DocumentScope, EntryId, Seq,
    Storage, StorageWrite, TaskId, ROOT_CONVERSATION_ID,
};
use serde_json::{json, Value};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::env::{
    BinaryReader, CreateDirOptions, DirReader, ExecCommand, ExecutionError, FileError,
    FileErrorCode, FileInfo, FileSystem, FileWatcher, NativeExecutionEnv,
    NativeExecutionEnvOptions, OnWatchChange, OpenBinaryReaderOptions, ReadTextLinesOptions,
    RemoveOptions, Shell, ShellExecOptions, ShellExecResult, TempFileOptions, TextLineReader,
    WatchTarget,
};
use futures::future::BoxFuture;
use futures::FutureExt;

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Operation {
    Append,
    Flush,
    Write,
    Rename,
    Remove,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Before,
    After,
    Short,
}

#[derive(Clone, Copy, Debug)]
struct Failure {
    operation: Operation,
    call: usize,
    mode: Mode,
}

#[derive(Default)]
struct Observations {
    operations: Vec<String>,
    failure: Option<Failure>,
    append_calls: usize,
    flush_calls: usize,
    write_calls: usize,
    rename_calls: usize,
    remove_calls: usize,
}

/// A native environment that records file mutations and injects one failure.
struct InstrumentedEnv {
    inner: NativeExecutionEnv,
    observations: Mutex<Observations>,
}

fn basename(path: &str) -> &str {
    path.rsplit('/').next().unwrap_or(path)
}

fn injected(message: &str, path: &str) -> FileError {
    FileError::new(FileErrorCode::Unknown, message, Some(path.to_owned()))
}

/// Half the bytes of `content`, at least one.
fn partial(content: &[u8]) -> &[u8] {
    &content[..std::cmp::max(1, content.len() / 2)]
}

impl InstrumentedEnv {
    fn new(directory: &str) -> Arc<Self> {
        Arc::new(Self {
            inner: native(directory),
            observations: Mutex::new(Observations::default()),
        })
    }

    fn observations(&self) -> std::sync::MutexGuard<'_, Observations> {
        self.observations
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    fn fail(&self, failure: Failure) {
        let mut observations = self.observations();
        *observations = Observations::default();
        observations.failure = Some(failure);
    }

    fn clear(&self) {
        *self.observations() = Observations::default();
    }

    fn operations(&self) -> Vec<String> {
        self.observations().operations.clone()
    }

    /// Count one call, record it, and return the failure mode when this call
    /// fails.
    fn observe(&self, operation: Operation, label: String) -> Option<Mode> {
        let mut observations = self.observations();
        let calls = match operation {
            Operation::Append => &mut observations.append_calls,
            Operation::Flush => &mut observations.flush_calls,
            Operation::Write => &mut observations.write_calls,
            Operation::Rename => &mut observations.rename_calls,
            Operation::Remove => &mut observations.remove_calls,
        };
        *calls += 1;
        let call = *calls;
        observations.operations.push(label);
        observations
            .failure
            .filter(|failure| failure.operation == operation && failure.call == call)
            .map(|failure| failure.mode)
    }
}

impl FileSystem for InstrumentedEnv {
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
        content: &'a [u8],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            let label = format!("write:{}", basename(path));
            match self.observe(Operation::Write, label) {
                None => self.inner.write_file(path, content, cx).await,
                Some(Mode::Before) => Err(injected("injected write failure", path)),
                Some(Mode::Short) => {
                    self.inner.write_file(path, partial(content), cx).await?;
                    Err(injected("injected short write", path))
                }
                Some(Mode::After) => {
                    self.inner.write_file(path, content, cx).await?;
                    Err(injected("injected post-write failure", path))
                }
            }
        }
        .boxed()
    }
    fn append_file<'a>(
        &'a self,
        path: &'a str,
        content: &'a [u8],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            let label = format!("append:{}", basename(path));
            match self.observe(Operation::Append, label) {
                None => self.inner.append_file(path, content, cx).await,
                Some(Mode::Before) => Err(injected("injected append failure", path)),
                Some(Mode::Short) => {
                    self.inner.append_file(path, partial(content), cx).await?;
                    Err(injected("injected short append", path))
                }
                Some(Mode::After) => {
                    self.inner.append_file(path, content, cx).await?;
                    Err(injected("injected post-append failure", path))
                }
            }
        }
        .boxed()
    }
    fn truncate_file<'a>(
        &'a self,
        path: &'a str,
        size: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        self.inner.truncate_file(path, size, cx)
    }
    fn flush_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            let label = format!("flush:{}", basename(path));
            match self.observe(Operation::Flush, label) {
                None => self.inner.flush_file(path, cx).await,
                Some(Mode::After) => {
                    self.inner.flush_file(path, cx).await?;
                    Err(injected("injected flush failure", path))
                }
                Some(Mode::Before | Mode::Short) => Err(injected("injected flush failure", path)),
            }
        }
        .boxed()
    }
    fn rename_file<'a>(
        &'a self,
        source_path: &'a str,
        destination_path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            let label = format!(
                "rename:{}->{}",
                basename(source_path),
                basename(destination_path)
            );
            match self.observe(Operation::Rename, label) {
                None => {
                    self.inner
                        .rename_file(source_path, destination_path, cx)
                        .await
                }
                Some(Mode::After) => {
                    self.inner
                        .rename_file(source_path, destination_path, cx)
                        .await?;
                    Err(injected("injected rename failure", source_path))
                }
                Some(Mode::Before | Mode::Short) => {
                    Err(injected("injected rename failure", source_path))
                }
            }
        }
        .boxed()
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
        self.inner.create_dir(path, options, cx)
    }
    fn remove<'a>(
        &'a self,
        path: &'a str,
        options: RemoveOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        async move {
            let label = format!("remove:{}", basename(path));
            match self.observe(Operation::Remove, label) {
                None => self.inner.remove(path, options, cx).await,
                Some(Mode::After) => {
                    self.inner.remove(path, options, cx).await?;
                    Err(injected("injected remove failure", path))
                }
                Some(Mode::Before | Mode::Short) => Err(injected("injected remove failure", path)),
            }
        }
        .boxed()
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

impl Shell for InstrumentedEnv {
    fn exec<'a>(
        &'a self,
        command: &'a ExecCommand,
        options: &'a ShellExecOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<ShellExecResult, ExecutionError>> {
        self.inner.exec(command, options, cx)
    }
    fn cleanup<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()> {
        Shell::cleanup(&self.inner, cx)
    }
}

fn native(directory: &str) -> NativeExecutionEnv {
    NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: directory.to_owned(),
        ..NativeExecutionEnvOptions::default()
    })
}

/// A fresh directory, removed on drop.
struct TempDirectory {
    _dir: tempfile::TempDir,
    path: String,
}

impl TempDirectory {
    fn join(&self, name: &str) -> String {
        format!("{}/{name}", self.path)
    }
}

fn temp_directory() -> TempDirectory {
    let dir = tempfile::Builder::new()
        .prefix("pi-durable-jsonl-")
        .tempdir()
        .expect("temp dir");
    let path = dir.path().to_str().expect("utf-8 temp dir").to_owned();
    TempDirectory { _dir: dir, path }
}

#[track_caller]
fn get<T, E: std::fmt::Debug>(result: Result<T, E>) -> T {
    match result {
        Ok(value) => value,
        Err(error) => panic!("unexpected failure: {error:?}"),
    }
}

#[track_caller]
fn message<T: std::fmt::Debug>(result: Result<T, StorageError>) -> String {
    match result {
        Ok(value) => panic!("expected a failure, got {value:?}"),
        Err(error) => error.to_string(),
    }
}

async fn try_open(
    directory: &str,
    fs: Arc<dyn FileSystem>,
    fsync: bool,
) -> Result<JsonlStorage, StorageError> {
    JsonlStorage::open(directory, fs, cx(), JsonlStorageOptions { fsync }).await
}

async fn open_storage(directory: &str) -> JsonlStorage {
    get(try_open(directory, Arc::new(native(directory)), false).await)
}

async fn open_native_fsync(directory: &str) -> JsonlStorage {
    get(try_open(directory, Arc::new(native(directory)), true).await)
}

async fn open_instrumented(
    directory: &str,
    env: &Arc<InstrumentedEnv>,
    fsync: bool,
) -> JsonlStorage {
    let fs: Arc<dyn FileSystem> = env.clone();
    get(try_open(directory, fs, fsync).await)
}

fn write(value: Value) -> StorageWrite {
    get(from_json(&JsonValue::from(value)))
}

async fn commit(storage: &JsonlStorage, writes: Vec<Value>) -> Result<u64, StorageError> {
    let writes: Vec<StorageWrite> = writes.into_iter().map(write).collect();
    storage.commit(&writes, cx()).await.map(Seq::get)
}

async fn commit_ok(storage: &JsonlStorage, writes: Vec<Value>) -> u64 {
    get(commit(storage, writes).await)
}

fn pending_task_json(id: TaskId, phase: &str) -> Value {
    json!({
        "id": id.get(),
        "conversationId": ROOT_CONVERSATION_ID.get(),
        "kind": "test.task",
        "version": 1,
        "input": null,
        "state": { "status": "pending", "checkpoint": { "phase": phase } },
        "background": false,
        "abortRequested": false,
    })
}

fn terminal_task_json(id: TaskId) -> Value {
    json!({
        "id": id.get(),
        "conversationId": ROOT_CONVERSATION_ID.get(),
        "kind": "test.task",
        "version": 1,
        "input": null,
        "state": { "status": "terminal", "outcome": { "status": "completed", "result": null } },
        "background": false,
        "abortRequested": false,
    })
}

fn pending_task(id: TaskId, phase: &str) -> AnyTaskRecord {
    get(from_json(&JsonValue::from(pending_task_json(id, phase))))
}

fn terminal_task(id: TaskId) -> AnyTaskRecord {
    get(from_json(&JsonValue::from(terminal_task_json(id))))
}

fn object<const N: usize>(entries: [(&str, Value); N]) -> Value {
    Value::Object(
        entries
            .into_iter()
            .map(|(key, value)| (key.to_owned(), value))
            .collect(),
    )
}

fn task_write(task: Value) -> Value {
    object([("type", json!("task")), ("value", task)])
}

async fn create_root(storage: &JsonlStorage) {
    commit_ok(
        storage,
        vec![json!({ "type": "conversation", "value": { "id": ROOT_CONVERSATION_ID.get() } })],
    )
    .await;
}

fn session_document(id: DocumentId, kind: &str) -> Value {
    json!({ "id": id.get(), "kind": kind, "scope": { "kind": "session" } })
}

fn base(value: Value) -> Value {
    object([
        ("kind", json!("base")),
        ("version", json!(1)),
        ("value", value),
    ])
}

fn delta(ops: Value) -> Value {
    object([
        ("kind", json!("delta")),
        ("version", json!(1)),
        ("ops", ops),
    ])
}

fn create(record: Value, content: Value) -> Value {
    object([
        ("type", json!("document.create")),
        ("record", record),
        ("content", content),
    ])
}

fn change(id: DocumentId, content: Value) -> Value {
    object([
        ("type", json!("document.change")),
        ("id", json!(id.get())),
        ("content", content),
    ])
}

fn retire(id: DocumentId) -> Value {
    json!({ "type": "document.retire", "id": id.get() })
}

async fn mint_task(storage: &JsonlStorage) -> TaskId {
    get(mint::<TaskId, _>(storage).await)
}

async fn mint_document(storage: &JsonlStorage) -> DocumentId {
    get(mint::<DocumentId, _>(storage).await)
}

async fn document_value(
    storage: &JsonlStorage,
    id: DocumentId,
    at: DocumentPoint,
) -> Option<Value> {
    get(storage.document(id, at, cx()).await)
        .map(|stored| Value::from(JsonValue::Object(stored.value)))
}

async fn current_value(storage: &JsonlStorage, id: DocumentId) -> Option<Value> {
    document_value(storage, id, DocumentPoint::Current).await
}

async fn task(storage: &JsonlStorage, id: TaskId) -> Option<AnyTaskRecord> {
    get(storage.task(id, cx()).await)
}

async fn close(storage: &JsonlStorage) {
    get(storage.close(cx()).await);
}

fn read_lines(path: &str) -> Vec<String> {
    let text = get(std::fs::read_to_string(path));
    if text.is_empty() {
        return Vec::new();
    }
    text.trim_end().split('\n').map(str::to_owned).collect()
}

fn file_exists(path: &str) -> bool {
    match std::fs::metadata(path) {
        Ok(_) => true,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
        Err(error) => panic!("stat failed: {error}"),
    }
}

fn file_size(path: &str) -> u64 {
    get(std::fs::metadata(path)).len()
}

fn append_bytes(path: &str, bytes: &[u8]) {
    let mut file = get(std::fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(path));
    get(file.write_all(bytes));
}

fn reclaim_files(directory: &str) -> Vec<String> {
    get(std::fs::read_dir(directory))
        .map(|entry| get(entry).file_name().to_string_lossy().into_owned())
        .filter(|name| name.ends_with(".reclaim"))
        .collect()
}

const fn failure(operation: Operation, call: usize, mode: Mode) -> Failure {
    Failure {
        operation,
        call,
        mode,
    }
}

macro_rules! failure_cases {
    ($runner:ident: $($name:ident => $value:expr),* $(,)?) => {
        $(
            #[tokio::test]
            async fn $name() {
                $runner($value).await;
            }
        )*
    };
}

#[tokio::test]
async fn opens_through_the_node_adapter() {
    let directory = temp_directory();
    let storage =
        get(open_native_jsonl_storage(&directory.path, cx(), JsonlStorageOptions::default()).await);
    create_root(&storage).await;
    let conversation = get(storage.conversation(ROOT_CONVERSATION_ID, cx()).await);
    assert_eq!(
        conversation.map(|record| Value::from(get(to_json(&record)))),
        Some(json!({ "id": ROOT_CONVERSATION_ID.get() }))
    );
}

#[tokio::test]
async fn publishes_every_commit_before_reclaiming_current_only_document_and_terminal_task_sidecars()
{
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let task_id = mint_task(&storage).await;
    let document_id = mint_document(&storage).await;
    commit_ok(
        &storage,
        vec![task_write(pending_task_json(task_id, "ready"))],
    )
    .await;
    commit_ok(
        &storage,
        vec![create(
            session_document(document_id, "test.document"),
            base(json!({ "count": 0 })),
        )],
    )
    .await;
    commit_ok(&storage, vec![change(document_id, delta(json!([])))]).await;
    commit_ok(
        &storage,
        vec![change(document_id, base(json!({ "count": 1 })))],
    )
    .await;
    assert_eq!(
        read_lines(&directory.join(&format!("task-{task_id}.jsonl"))).len(),
        1
    );
    assert_eq!(
        read_lines(&directory.join(&format!("doc-{document_id}.jsonl"))).len(),
        1
    );

    commit_ok(&storage, vec![retire(document_id)]).await;
    commit_ok(&storage, vec![task_write(terminal_task_json(task_id))]).await;

    assert_eq!(read_lines(&directory.join("main.jsonl")).len(), 7);
    assert!(!file_exists(
        &directory.join(&format!("task-{task_id}.jsonl"))
    ));
    assert!(!file_exists(
        &directory.join(&format!("doc-{document_id}.jsonl"))
    ));
    let marker_types: Vec<String> = read_lines(&directory.join("main.jsonl"))
        .iter()
        .map(|line| {
            let marker: Value = get(serde_json::from_str(line));
            marker["type"].as_str().expect("type").to_owned()
        })
        .collect();
    assert_eq!(marker_types, vec!["commit"; 7]);
}

#[tokio::test]
async fn orders_multiple_live_task_replacements_in_one_sidecar_by_commit_ordinal() {
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let task_id = mint_task(&storage).await;
    commit_ok(
        &storage,
        vec![
            task_write(pending_task_json(task_id, "first")),
            task_write(pending_task_json(task_id, "second")),
        ],
    )
    .await;
    assert_eq!(
        read_lines(&directory.join(&format!("task-{task_id}.jsonl"))).len(),
        2
    );

    let reopened = open_storage(&directory.path).await;
    assert_eq!(
        task(&reopened, task_id).await,
        Some(pending_task(task_id, "second"))
    );
}

#[tokio::test]
async fn removes_a_complete_plus_torn_unconfirmed_multi_record_sidecar_append() {
    let directory = temp_directory();
    let env = InstrumentedEnv::new(&directory.path);
    let storage = open_instrumented(&directory.path, &env, false).await;
    create_root(&storage).await;
    let task_id = mint_task(&storage).await;
    env.fail(failure(Operation::Append, 1, Mode::Short));
    let second = format!("second-{}", "x".repeat(512));
    let result = commit(
        &storage,
        vec![
            task_write(pending_task_json(task_id, "first")),
            task_write(pending_task_json(task_id, &second)),
        ],
    )
    .await;
    assert!(message(result).contains("poisoned"));
    let partial = get(std::fs::read(
        directory.join(&format!("task-{task_id}.jsonl")),
    ));
    assert_ne!(partial.last(), Some(&b'\n'));
    assert_eq!(partial.split(|&byte| byte == b'\n').count() - 1, 1);

    let reopened = open_storage(&directory.path).await;
    assert_eq!(task(&reopened, task_id).await, None);
    assert_eq!(
        file_size(&directory.join(&format!("task-{task_id}.jsonl"))),
        0
    );
}

/// The TS case commits an entry whose data is a `bigint`, which
/// `JSON.stringify` rejects. Rust records hold only JSON values, so the
/// closest observable preparation failure is a batch `MemoryStorage` rejects
/// (the same entry ID written twice).
#[tokio::test]
async fn serializes_the_complete_candidate_before_io_and_leaves_preparation_failures_usable() {
    let directory = temp_directory();
    let env = InstrumentedEnv::new(&directory.path);
    let storage = open_instrumented(&directory.path, &env, false).await;
    create_root(&storage).await;
    env.clear();
    let id: EntryId = get(mint::<EntryId, _>(&storage).await);
    let bad = json!({
        "type": "entry",
        "value": { "id": id.get(), "conversationId": ROOT_CONVERSATION_ID.get(), "kind": "bad" },
    });
    assert!(commit(&storage, vec![bad.clone(), bad]).await.is_err());
    assert_eq!(env.operations(), Vec::<String>::new());
    assert_eq!(get(storage.entry(id, cx()).await), None);
    assert_eq!(
        commit_ok(
            &storage,
            vec![json!({
                "type": "entry",
                "value": { "id": id.get(), "conversationId": ROOT_CONVERSATION_ID.get(), "kind": "good" },
            })],
        )
        .await,
        2
    );
}

async fn poisons_after_append_failure_and_recovers_only_confirmed_state(failure: Failure) {
    let directory = temp_directory();
    let env = InstrumentedEnv::new(&directory.path);
    let storage = open_instrumented(&directory.path, &env, false).await;
    create_root(&storage).await;
    let first_id = mint_document(&storage).await;
    let second_id = mint_document(&storage).await;
    env.fail(failure);
    let result = commit(
        &storage,
        vec![
            create(
                session_document(first_id, "first"),
                base(json!({ "text": "α" })),
            ),
            create(
                session_document(second_id, "second"),
                base(json!({ "text": "β" })),
            ),
        ],
    )
    .await;
    assert!(message(result).contains("poisoned"));
    let read = storage
        .document(first_id, DocumentPoint::Current, cx())
        .await;
    assert!(message(read).contains("poisoned"));

    let reopened = open_storage(&directory.path).await;
    let marker_survived = failure.call == 3 && failure.mode == Mode::After;
    assert_eq!(
        current_value(&reopened, first_id).await,
        marker_survived.then(|| json!({ "text": "α" }))
    );
    assert_eq!(
        current_value(&reopened, second_id).await,
        marker_survived.then(|| json!({ "text": "β" }))
    );
}

failure_cases! {
    poisons_after_append_failure_and_recovers_only_confirmed_state:
    poisons_after_before_failure_at_append_1_and_recovers_only_confirmed_state => failure(Operation::Append, 1, Mode::Before),
    poisons_after_after_failure_at_append_1_and_recovers_only_confirmed_state => failure(Operation::Append, 1, Mode::After),
    poisons_after_short_failure_at_append_1_and_recovers_only_confirmed_state => failure(Operation::Append, 1, Mode::Short),
    poisons_after_before_failure_at_append_2_and_recovers_only_confirmed_state => failure(Operation::Append, 2, Mode::Before),
    poisons_after_after_failure_at_append_2_and_recovers_only_confirmed_state => failure(Operation::Append, 2, Mode::After),
    poisons_after_before_failure_at_append_3_and_recovers_only_confirmed_state => failure(Operation::Append, 3, Mode::Before),
    poisons_after_short_failure_at_append_3_and_recovers_only_confirmed_state => failure(Operation::Append, 3, Mode::Short),
    poisons_after_after_failure_at_append_3_and_recovers_only_confirmed_state => failure(Operation::Append, 3, Mode::After),
}

async fn poisons_after_flush_failure_and_never_writes_a_marker(failure: Failure) {
    let directory = temp_directory();
    let env = InstrumentedEnv::new(&directory.path);
    let storage = open_instrumented(&directory.path, &env, true).await;
    create_root(&storage).await;
    let first_id = mint_document(&storage).await;
    let second_id = mint_document(&storage).await;
    env.fail(failure);
    let result = commit(
        &storage,
        vec![
            create(session_document(first_id, "flush.first"), base(json!({}))),
            create(session_document(second_id, "flush.second"), base(json!({}))),
        ],
    )
    .await;
    assert!(message(result).contains("poisoned"));
    let reopened = open_storage(&directory.path).await;
    assert_eq!(current_value(&reopened, first_id).await, None);
    assert_eq!(current_value(&reopened, second_id).await, None);
}

failure_cases! {
    poisons_after_flush_failure_and_never_writes_a_marker:
    poisons_after_before_failure_at_flush_1_and_never_writes_a_marker => failure(Operation::Flush, 1, Mode::Before),
    poisons_after_after_failure_at_flush_1_and_never_writes_a_marker => failure(Operation::Flush, 1, Mode::After),
    poisons_after_before_failure_at_flush_2_and_never_writes_a_marker => failure(Operation::Flush, 2, Mode::Before),
    poisons_after_after_failure_at_flush_2_and_never_writes_a_marker => failure(Operation::Flush, 2, Mode::After),
}

#[tokio::test]
async fn orders_publication_flushes_exactly_and_flushes_main_only_to_authorize_reclamation() {
    for fsync in [false, true] {
        let directory = temp_directory();
        let env = InstrumentedEnv::new(&directory.path);
        let storage = open_instrumented(&directory.path, &env, fsync).await;
        create_root(&storage).await;
        let first_id = mint_document(&storage).await;
        let second_id = mint_document(&storage).await;
        env.clear();
        commit_ok(
            &storage,
            vec![
                create(session_document(second_id, "second"), base(json!({}))),
                create(session_document(first_id, "first"), base(json!({}))),
            ],
        )
        .await;
        let mut expected = vec![
            format!("append:doc-{second_id}.jsonl"),
            format!("append:doc-{first_id}.jsonl"),
        ];
        if fsync {
            expected.push(format!("flush:doc-{second_id}.jsonl"));
            expected.push(format!("flush:doc-{first_id}.jsonl"));
        }
        expected.push("append:main.jsonl".to_owned());
        assert_eq!(env.operations(), expected);

        env.clear();
        commit_ok(
            &storage,
            vec![change(first_id, base(json!({ "checkpoint": true })))],
        )
        .await;
        let mut expected = vec![format!("append:doc-{first_id}.jsonl")];
        if fsync {
            expected.push(format!("flush:doc-{first_id}.jsonl"));
        }
        expected.push("append:main.jsonl".to_owned());
        if fsync {
            expected.push("flush:main.jsonl".to_owned());
        }
        expected.push(format!("write:doc-{first_id}.jsonl.reclaim"));
        if fsync {
            expected.push(format!("flush:doc-{first_id}.jsonl.reclaim"));
        }
        expected.push(format!(
            "rename:doc-{first_id}.jsonl.reclaim->doc-{first_id}.jsonl"
        ));
        assert_eq!(env.operations(), expected);

        env.clear();
        let entry_id: EntryId = get(mint::<EntryId, _>(&storage).await);
        commit_ok(
            &storage,
            vec![json!({
                "type": "entry",
                "value": { "id": entry_id.get(), "conversationId": ROOT_CONVERSATION_ID.get(), "kind": "main-only" },
            })],
        )
        .await;
        assert_eq!(env.operations(), vec!["append:main.jsonl".to_owned()]);

        let task_id = mint_task(&storage).await;
        commit_ok(
            &storage,
            vec![task_write(pending_task_json(task_id, "ready"))],
        )
        .await;
        env.clear();
        commit_ok(&storage, vec![task_write(terminal_task_json(task_id))]).await;
        let mut expected = vec!["append:main.jsonl".to_owned()];
        if fsync {
            expected.push("flush:main.jsonl".to_owned());
        }
        expected.push(format!("remove:task-{task_id}.jsonl"));
        assert_eq!(env.operations(), expected);
    }
}

async fn recovers_a_committed_base_across_reclaim_failure(failure: Failure) {
    let directory = temp_directory();
    let env = InstrumentedEnv::new(&directory.path);
    let storage = open_instrumented(&directory.path, &env, false).await;
    create_root(&storage).await;
    let id = mint_document(&storage).await;
    commit_ok(
        &storage,
        vec![create(
            session_document(id, "test.document"),
            base(json!({ "count": 0 })),
        )],
    )
    .await;
    commit_ok(
        &storage,
        vec![change(id, delta(json!([["s", ["count"], 1]])))],
    )
    .await;

    env.fail(failure);
    assert_eq!(
        commit_ok(&storage, vec![change(id, base(json!({ "count": 2 })))]).await,
        4
    );
    assert_eq!(
        current_value(&storage, id).await,
        Some(json!({ "count": 2 }))
    );
    close(&storage).await;

    let reopened = open_storage(&directory.path).await;
    assert_eq!(
        current_value(&reopened, id).await,
        Some(json!({ "count": 2 }))
    );
    assert_eq!(
        read_lines(&directory.join(&format!("doc-{id}.jsonl"))).len(),
        1
    );
    assert_eq!(reclaim_files(&directory.path), Vec::<String>::new());
}

failure_cases! {
    recovers_a_committed_base_across_reclaim_failure:
    recovers_a_committed_base_across_reclaim_write_before => failure(Operation::Write, 1, Mode::Before),
    recovers_a_committed_base_across_reclaim_write_short => failure(Operation::Write, 1, Mode::Short),
    recovers_a_committed_base_across_reclaim_write_after => failure(Operation::Write, 1, Mode::After),
    recovers_a_committed_base_across_reclaim_rename_before => failure(Operation::Rename, 1, Mode::Before),
    recovers_a_committed_base_across_reclaim_rename_after => failure(Operation::Rename, 1, Mode::After),
}

async fn recovers_document_retirement_reclamation_across_remove(mode: Mode) {
    let directory = temp_directory();
    let env = InstrumentedEnv::new(&directory.path);
    let storage = open_instrumented(&directory.path, &env, false).await;
    create_root(&storage).await;
    let task_id = mint_task(&storage).await;
    let id = mint_document(&storage).await;
    commit_ok(
        &storage,
        vec![
            task_write(pending_task_json(task_id, "ready")),
            create(
                json!({ "id": id.get(), "kind": "task.document", "scope": { "kind": "task", "taskId": task_id.get() } }),
                base(json!({ "count": 1 })),
            ),
        ],
    )
    .await;
    env.fail(failure(Operation::Remove, 1, mode));
    assert_eq!(commit_ok(&storage, vec![retire(id)]).await, 3);
    assert_eq!(current_value(&storage, id).await, None);
    close(&storage).await;

    let reopened = open_storage(&directory.path).await;
    assert_eq!(current_value(&reopened, id).await, None);
    assert_eq!(
        task(&reopened, task_id).await,
        Some(pending_task(task_id, "ready"))
    );
    assert!(!file_exists(&directory.join(&format!("doc-{id}.jsonl"))));
    assert_eq!(reclaim_files(&directory.path), Vec::<String>::new());
}

failure_cases! {
    recovers_document_retirement_reclamation_across_remove:
    recovers_document_retirement_reclamation_across_remove_before => Mode::Before,
    recovers_document_retirement_reclamation_across_remove_after => Mode::After,
}

async fn defers_reclamation_after_authorizing_main_flush_failure(mode: Mode) {
    let directory = temp_directory();
    let env = InstrumentedEnv::new(&directory.path);
    let storage = open_instrumented(&directory.path, &env, true).await;
    create_root(&storage).await;
    let id = mint_document(&storage).await;
    commit_ok(
        &storage,
        vec![create(
            session_document(id, "test.document"),
            base(json!({ "count": 0 })),
        )],
    )
    .await;
    env.fail(failure(Operation::Flush, 2, mode));
    assert_eq!(
        commit_ok(&storage, vec![change(id, base(json!({ "count": 2 })))]).await,
        3
    );
    assert_eq!(
        env.operations(),
        vec![
            format!("append:doc-{id}.jsonl"),
            format!("flush:doc-{id}.jsonl"),
            "append:main.jsonl".to_owned(),
            "flush:main.jsonl".to_owned(),
        ]
    );
    assert_eq!(
        current_value(&storage, id).await,
        Some(json!({ "count": 2 }))
    );
    assert_eq!(
        read_lines(&directory.join(&format!("doc-{id}.jsonl"))).len(),
        2
    );
    close(&storage).await;

    let recovery_env = InstrumentedEnv::new(&directory.path);
    recovery_env.fail(failure(Operation::Flush, 1, mode));
    let deferred = open_instrumented(&directory.path, &recovery_env, true).await;
    assert_eq!(
        current_value(&deferred, id).await,
        Some(json!({ "count": 2 }))
    );
    assert_eq!(
        recovery_env.operations(),
        vec!["flush:main.jsonl".to_owned()]
    );
    assert_eq!(
        read_lines(&directory.join(&format!("doc-{id}.jsonl"))).len(),
        2
    );
    close(&deferred).await;

    let reclaimed = open_native_fsync(&directory.path).await;
    assert_eq!(
        current_value(&reclaimed, id).await,
        Some(json!({ "count": 2 }))
    );
    assert_eq!(
        read_lines(&directory.join(&format!("doc-{id}.jsonl"))).len(),
        1
    );
}

failure_cases! {
    defers_reclamation_after_authorizing_main_flush_failure:
    defers_reclamation_after_authorizing_main_flush_before_failure => Mode::Before,
    defers_reclamation_after_authorizing_main_flush_after_failure => Mode::After,
}

async fn keeps_a_committed_base_usable_after_reclaim_temp_flush_failure(mode: Mode) {
    let directory = temp_directory();
    let env = InstrumentedEnv::new(&directory.path);
    let storage = open_instrumented(&directory.path, &env, true).await;
    create_root(&storage).await;
    let id = mint_document(&storage).await;
    commit_ok(
        &storage,
        vec![create(
            session_document(id, "test.document"),
            base(json!({ "count": 0 })),
        )],
    )
    .await;
    env.fail(failure(Operation::Flush, 3, mode));
    assert_eq!(
        commit_ok(&storage, vec![change(id, base(json!({ "count": 2 })))]).await,
        3
    );
    env.clear();
    commit_ok(
        &storage,
        vec![change(id, delta(json!([["s", ["count"], 3]])))],
    )
    .await;
    close(&storage).await;

    let reopened = open_native_fsync(&directory.path).await;
    assert_eq!(
        current_value(&reopened, id).await,
        Some(json!({ "count": 3 }))
    );
    assert_eq!(
        read_lines(&directory.join(&format!("doc-{id}.jsonl"))).len(),
        2
    );
}

failure_cases! {
    keeps_a_committed_base_usable_after_reclaim_temp_flush_failure:
    keeps_a_committed_base_usable_after_reclaim_temp_flush_before_failure => Mode::Before,
    keeps_a_committed_base_usable_after_reclaim_temp_flush_after_failure => Mode::After,
}

async fn recovers_terminal_task_reclamation_across_remove(mode: Mode) {
    let directory = temp_directory();
    let env = InstrumentedEnv::new(&directory.path);
    let storage = open_instrumented(&directory.path, &env, false).await;
    create_root(&storage).await;
    let id = mint_task(&storage).await;
    commit_ok(&storage, vec![task_write(pending_task_json(id, "ready"))]).await;
    env.fail(failure(Operation::Remove, 1, mode));
    assert_eq!(
        commit_ok(&storage, vec![task_write(terminal_task_json(id))]).await,
        3
    );
    assert_eq!(task(&storage, id).await, Some(terminal_task(id)));
    close(&storage).await;

    let reopened = open_storage(&directory.path).await;
    assert_eq!(task(&reopened, id).await, Some(terminal_task(id)));
    assert!(!file_exists(&directory.join(&format!("task-{id}.jsonl"))));
    assert_eq!(reclaim_files(&directory.path), Vec::<String>::new());
}

failure_cases! {
    recovers_terminal_task_reclamation_across_remove:
    recovers_terminal_task_reclamation_across_remove_before => Mode::Before,
    recovers_terminal_task_reclamation_across_remove_after => Mode::After,
}

#[tokio::test]
async fn appends_later_deltas_to_the_replacement_sidecar_after_a_current_only_base() {
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let id = mint_document(&storage).await;
    commit_ok(
        &storage,
        vec![create(
            session_document(id, "test.document"),
            base(json!({ "count": 0 })),
        )],
    )
    .await;
    commit_ok(&storage, vec![change(id, base(json!({ "count": 10 })))]).await;
    commit_ok(
        &storage,
        vec![change(id, delta(json!([["s", ["count"], 11]])))],
    )
    .await;
    assert_eq!(
        read_lines(&directory.join(&format!("doc-{id}.jsonl"))).len(),
        2
    );
    let reopened = open_storage(&directory.path).await;
    assert_eq!(
        current_value(&reopened, id).await,
        Some(json!({ "count": 11 }))
    );
}

#[tokio::test]
async fn never_reclaims_rewindable_document_history_including_after_a_base_and_retirement() {
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let id = mint_document(&storage).await;
    let record = json!({
        "id": id.get(),
        "kind": "rewindable",
        "scope": { "kind": "conversation", "conversationId": ROOT_CONVERSATION_ID.get() },
        "history": "rewindable",
        "fork": "asOf",
    });
    let created_at = commit_ok(&storage, vec![create(record, base(json!({ "count": 0 })))]).await;
    let changed_at = commit_ok(
        &storage,
        vec![change(id, delta(json!([["s", ["count"], 1]])))],
    )
    .await;
    commit_ok(&storage, vec![change(id, base(json!({ "count": 2 })))]).await;
    commit_ok(&storage, vec![retire(id)]).await;

    assert_eq!(
        read_lines(&directory.join(&format!("doc-{id}.jsonl"))).len(),
        3
    );
    let reopened = open_storage(&directory.path).await;
    assert_eq!(
        document_value(
            &reopened,
            id,
            DocumentPoint::At(Seq::from_number(created_at))
        )
        .await,
        Some(json!({ "count": 0 }))
    );
    assert_eq!(
        document_value(
            &reopened,
            id,
            DocumentPoint::At(Seq::from_number(changed_at))
        )
        .await,
        Some(json!({ "count": 1 }))
    );
    assert_eq!(current_value(&reopened, id).await, None);
    assert_eq!(
        read_lines(&directory.join(&format!("doc-{id}.jsonl"))).len(),
        3
    );
}

#[tokio::test]
async fn reclaims_retired_task_session_and_latest_conversation_document_sidecars() {
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let task_id = mint_task(&storage).await;
    let session_id = mint_document(&storage).await;
    let latest_id = mint_document(&storage).await;
    let task_document_id = mint_document(&storage).await;
    let created_at = commit_ok(
        &storage,
        vec![
            task_write(pending_task_json(task_id, "ready")),
            create(session_document(session_id, "session"), base(json!({}))),
            create(
                json!({
                    "id": latest_id.get(),
                    "kind": "latest",
                    "scope": { "kind": "conversation", "conversationId": ROOT_CONVERSATION_ID.get() },
                    "history": "latest",
                    "fork": "current",
                }),
                base(json!({})),
            ),
            create(
                json!({ "id": task_document_id.get(), "kind": "task", "scope": { "kind": "task", "taskId": task_id.get() } }),
                base(json!({})),
            ),
        ],
    )
    .await;
    let retired_at = commit_ok(
        &storage,
        vec![
            retire(session_id),
            retire(latest_id),
            retire(task_document_id),
            task_write(terminal_task_json(task_id)),
        ],
    )
    .await;
    for file in [
        format!("doc-{session_id}.jsonl"),
        format!("doc-{latest_id}.jsonl"),
        format!("doc-{task_document_id}.jsonl"),
        format!("task-{task_id}.jsonl"),
    ] {
        assert!(!file_exists(&directory.join(&file)), "{file} exists");
    }

    let reopened = open_storage(&directory.path).await;
    assert_eq!(task(&reopened, task_id).await, Some(terminal_task(task_id)));
    assert_eq!(current_value(&reopened, session_id).await, None);
    assert_eq!(current_value(&reopened, latest_id).await, None);
    assert_eq!(current_value(&reopened, task_document_id).await, None);
    let address = DocumentAddress {
        kind: "session".to_owned(),
        scope: DocumentScope::Session,
        key: None,
    };
    let found = get(reopened
        .find_document(
            &address,
            DocumentPoint::At(Seq::from_number(created_at)),
            cx(),
        )
        .await)
    .expect("session document at creation");
    assert_eq!(found.id, session_id);
    assert_eq!(found.created_at, Seq::from_number(created_at));
    assert_eq!(found.retired_at, Some(Seq::from_number(retired_at)));
    assert_eq!(
        get(reopened
            .find_document(
                &address,
                DocumentPoint::At(Seq::from_number(retired_at)),
                cx()
            )
            .await),
        None
    );
}

#[tokio::test]
async fn truncates_torn_utf_8_tails_at_exact_byte_offsets_and_reuses_the_unconfirmed_sequence() {
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let document_id = mint_document(&storage).await;
    commit_ok(
        &storage,
        vec![create(
            session_document(document_id, "test.document"),
            base(json!({ "text": "kept" })),
        )],
    )
    .await;
    let sidecar_path = directory.join(&format!("doc-{document_id}.jsonl"));
    let main_path = directory.join("main.jsonl");
    let sidecar_size = file_size(&sidecar_path);
    let main_size = file_size(&main_path);
    let torn = "{\"text\":\"€".as_bytes();
    append_bytes(&sidecar_path, &torn[..torn.len() - 1]);
    append_bytes(&main_path, &torn[..torn.len() - 1]);

    let reopened = open_storage(&directory.path).await;
    assert_eq!(file_size(&sidecar_path), sidecar_size);
    assert_eq!(file_size(&main_path), main_size);
    assert_eq!(
        commit_ok(&reopened, vec![change(document_id, delta(json!([])))]).await,
        3
    );
}

#[tokio::test]
async fn removes_complete_unconfirmed_sidecar_tails_without_resurrecting_terminal_tasks() {
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let task_id = mint_task(&storage).await;
    commit_ok(
        &storage,
        vec![task_write(pending_task_json(task_id, "ready"))],
    )
    .await;
    commit_ok(&storage, vec![task_write(terminal_task_json(task_id))]).await;
    let sidecar_path = directory.join(&format!("task-{task_id}.jsonl"));
    assert!(!file_exists(&sidecar_path));
    let line = json!({
        "format": 1,
        "type": "record",
        "seq": 4,
        "ordinal": 0,
        "payload": { "type": "task", "value": pending_task_json(task_id, "stale") },
    });
    append_bytes(&sidecar_path, format!("{line}\n").as_bytes());

    let reopened = open_storage(&directory.path).await;
    assert!(!file_exists(&sidecar_path));
    assert_eq!(task(&reopened, task_id).await, Some(terminal_task(task_id)));
    assert_eq!(commit_ok(&reopened, vec![]).await, 4);
}

#[tokio::test]
async fn fails_open_when_confirmed_sidecar_data_is_missing() {
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let document_id = mint_document(&storage).await;
    commit_ok(
        &storage,
        vec![create(
            session_document(document_id, "test.document"),
            base(json!({})),
        )],
    )
    .await;
    get(std::fs::write(
        directory.join(&format!("doc-{document_id}.jsonl")),
        "",
    ));
    let opened = try_open(&directory.path, Arc::new(native(&directory.path)), false).await;
    assert!(message(opened).contains("Missing confirmed sidecar record"));
}

#[tokio::test]
async fn rejects_a_confirmed_record_after_an_unconfirmed_sidecar_record() {
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let document_id = mint_document(&storage).await;
    commit_ok(
        &storage,
        vec![create(
            session_document(document_id, "test.document"),
            base(json!({ "count": 0 })),
        )],
    )
    .await;
    commit_ok(
        &storage,
        vec![change(document_id, delta(json!([["s", ["count"], 1]])))],
    )
    .await;
    let path = directory.join(&format!("doc-{document_id}.jsonl"));
    let lines = read_lines(&path);
    let unconfirmed = json!({
        "format": 1,
        "type": "record",
        "seq": 2,
        "ordinal": 999,
        "payload": { "type": "document", "id": document_id.get(), "content": delta(json!([])) },
    });
    get(std::fs::write(
        &path,
        format!("{}\n{unconfirmed}\n{}\n", lines[0], lines[1]),
    ));
    let opened = try_open(&directory.path, Arc::new(native(&directory.path)), false).await;
    assert!(message(opened).contains("Confirmed record follows an unconfirmed tail"));
}

#[tokio::test]
async fn rejects_non_increasing_main_commit_sequences() {
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let path = directory.join("main.jsonl");
    let content = get(std::fs::read(&path));
    append_bytes(&path, &content);

    let opened = try_open(&directory.path, Arc::new(native(&directory.path)), false).await;
    assert!(message(opened).contains("Commit sequence does not strictly increase"));
}

#[tokio::test]
async fn rejects_structurally_invalid_confirmed_document_content() {
    let directory = temp_directory();
    let storage = open_storage(&directory.path).await;
    create_root(&storage).await;
    let document_id = mint_document(&storage).await;
    commit_ok(
        &storage,
        vec![create(
            session_document(document_id, "test.document"),
            base(json!({})),
        )],
    )
    .await;
    let path = directory.join(&format!("doc-{document_id}.jsonl"));
    let mut record: Value = get(serde_json::from_str(
        get(std::fs::read_to_string(&path)).trim(),
    ));
    record["payload"]["content"]
        .as_object_mut()
        .expect("content object")
        .remove("value");
    get(std::fs::write(&path, format!("{record}\n")));

    let opened = try_open(&directory.path, Arc::new(native(&directory.path)), false).await;
    assert!(message(opened).contains("Invalid document content"));
}

#[tokio::test]
async fn rejects_malformed_complete_main_and_sidecar_lines() {
    let main_directory = temp_directory();
    let main_storage = open_storage(&main_directory.path).await;
    create_root(&main_storage).await;
    append_bytes(&main_directory.join("main.jsonl"), b"{bad}\n");
    let opened = try_open(
        &main_directory.path,
        Arc::new(native(&main_directory.path)),
        false,
    )
    .await;
    assert!(message(opened).contains("Malformed complete main.jsonl"));

    let sidecar_directory = temp_directory();
    let sidecar_storage = open_storage(&sidecar_directory.path).await;
    create_root(&sidecar_storage).await;
    get(std::fs::write(
        sidecar_directory.join("doc-99.jsonl"),
        "{bad}\n",
    ));
    let opened = try_open(
        &sidecar_directory.path,
        Arc::new(native(&sidecar_directory.path)),
        false,
    )
    .await;
    assert!(message(opened).contains("Malformed complete doc-99.jsonl"));
}
