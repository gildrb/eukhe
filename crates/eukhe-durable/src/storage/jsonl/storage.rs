//! Portable JSONL implementation of the storage contract. Port of
//! `storage/jsonl/storage.ts`.
//!
//! `main.jsonl` holds one commit marker per line; non-terminal task records and
//! document contents live in `task-<id>.jsonl` / `doc-<id>.jsonl` sidecars that
//! a marker confirms by `(seq, ordinal)`. Writes are classified on their JSON
//! form, exactly as the TS backend sees its JS objects.

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::sync::{Arc, Mutex, PoisonError};

use crate::env::{CreateDirOptions, FileError, FileErrorCode, FileKind, FileSystem, RemoveOptions};
use crate::errors::StorageError;
use crate::storage::{MemoryStorage, PreparedMemoryCommit};
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationQuery, ConversationRecord, Cursor, DocumentAddress,
    DocumentId, DocumentPoint, DocumentQuery, DocumentRecord, EntryId, EntryQuery, EntryRecord,
    Page, Seq, Storage, StorageWrite, StoredDocument, StoredEntry, SubmissionId, SubmissionQuery,
    SubmissionRecord, TaskId, TaskQuery,
};
use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue, MAX_SAFE_INTEGER};
use futures::future::{try_join_all, BoxFuture};

const FORMAT_VERSION: f64 = 1.0;
const MAIN_FILE: &str = "main.jsonl";
const RECLAIM_SUFFIX: &str = ".reclaim";
const JSONL_SUFFIX: &str = ".jsonl";

type Cause = Arc<dyn Error + Send + Sync + 'static>;

/// Options of [`JsonlStorage::open`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct JsonlStorageOptions {
    /// Flush every affected sidecar before appending the main marker. Defaults
    /// to false.
    pub fsync: bool,
}

/// Committed JSONL data that cannot be recovered (TS `JsonlCorruptionError`).
#[derive(Clone, Debug, thiserror::Error)]
#[error("{message}")]
pub struct JsonlCorruptionError {
    message: String,
    #[source]
    cause: Option<Cause>,
}

impl JsonlCorruptionError {
    /// The JS `error.name`.
    pub const NAME: &'static str = "JsonlCorruptionError";

    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            cause: None,
        }
    }

    fn caused(message: impl Into<String>, cause: Cause) -> Self {
        Self {
            message: message.into(),
            cause: Some(cause),
        }
    }

    /// The error message.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }

    /// The JS `error.cause`.
    #[must_use]
    pub fn cause(&self) -> Option<&Cause> {
        self.cause.as_ref()
    }
}

/// A publication I/O failure left the files in an unknown state; every later
/// call fails with the same error until the storage is reopened (TS
/// `JsonlStoragePoisonedError`).
#[derive(Clone, Debug, thiserror::Error)]
#[error("JSONL storage is poisoned and must be reopened")]
pub struct JsonlStoragePoisonedError {
    #[source]
    cause: Cause,
}

impl JsonlStoragePoisonedError {
    /// The JS `error.name`.
    pub const NAME: &'static str = "JsonlStoragePoisonedError";

    /// The failure that poisoned the storage.
    #[must_use]
    pub fn cause(&self) -> &Cause {
        &self.cause
    }
}

/// A filesystem failure of one JSONL action: the TS `errorFromFile` error
/// (`JSONL <action> failed: <message>`, caused by the [`FileError`]).
#[derive(Clone, Debug, thiserror::Error)]
#[error("JSONL {action} failed: {}", .cause.message)]
pub struct JsonlFileError {
    action: String,
    #[source]
    cause: FileError,
}

impl JsonlFileError {
    /// The failed file operation.
    #[must_use]
    pub fn cause(&self) -> &FileError {
        &self.cause
    }
}

/// The TS `throw new Error("JsonlStorage is closed")`.
#[derive(Clone, Copy, Debug, thiserror::Error)]
#[error("JsonlStorage is closed")]
struct ClosedError;

fn error_from_file(action: impl Into<String>, error: FileError) -> JsonlFileError {
    JsonlFileError {
        action: action.into(),
        cause: error,
    }
}

fn failed(error: impl Error + Send + Sync + 'static) -> StorageError {
    StorageError::failed(error)
}

fn corruption(message: impl Into<String>) -> StorageError {
    failed(JsonlCorruptionError::new(message))
}

/// JS `Number.isSafeInteger`, returning the integer.
fn safe_integer(value: Option<&JsonValue>) -> Option<i64> {
    let number = value?.as_f64()?;
    if number.fract() != 0.0 || number.abs() > MAX_SAFE_INTEGER {
        return None;
    }
    // Lossless: an integral value within ±(2^53 - 1).
    #[allow(clippy::cast_possible_truncation)]
    Some(number as i64)
}

fn get<'a>(value: &'a JsonValue, key: &str) -> Option<&'a JsonValue> {
    value.as_object().and_then(|object| object.get(key))
}

fn is_object(value: Option<&JsonValue>) -> bool {
    value.is_some_and(JsonValue::is_object)
}

fn type_of(value: &JsonValue) -> Option<&str> {
    get(value, "type").and_then(JsonValue::as_str)
}

fn status_of(task: &JsonValue) -> Option<&str> {
    get(task, "state")
        .and_then(|state| get(state, "status"))
        .and_then(JsonValue::as_str)
}

fn is_terminal(task: &JsonValue) -> bool {
    status_of(task) == Some("terminal")
}

fn sidecar_file_name(kind: &str, id: i64) -> String {
    format!("{kind}-{id}{JSONL_SUFFIX}")
}

/// `^(?:doc|task)-(?:0|[1-9]\d*)\.jsonl$`.
fn is_sidecar_file_name(name: &str) -> bool {
    name.strip_suffix(JSONL_SUFFIX).is_some_and(is_sidecar_stem)
}

/// `^(?:doc|task)-(?:0|[1-9]\d*)\.jsonl\.reclaim$`.
fn is_reclaim_file_name(name: &str) -> bool {
    name.strip_suffix(RECLAIM_SUFFIX)
        .is_some_and(is_sidecar_file_name)
}

fn is_sidecar_stem(stem: &str) -> bool {
    let Some(digits) = stem
        .strip_prefix("doc-")
        .or_else(|| stem.strip_prefix("task-"))
    else {
        return false;
    };
    digits == "0"
        || (!digits.is_empty()
            && !digits.starts_with('0')
            && digits.bytes().all(|byte| byte.is_ascii_digit()))
}

/// TS `isCurrentOnly` on a JSON `DocumentCreate`.
fn is_current_only(record: &JsonValue) -> bool {
    let scope_kind = get(record, "scope")
        .and_then(|scope| get(scope, "kind"))
        .and_then(JsonValue::as_str);
    let history = get(record, "history").and_then(JsonValue::as_str);
    scope_kind != Some("conversation") || history == Some("latest")
}

type SidecarKey = (String, i64, i64);

fn sidecar_key(file: &str, seq: i64, ordinal: i64) -> SidecarKey {
    (file.to_owned(), seq, ordinal)
}

fn json_line(value: &JsonValue) -> String {
    format!("{value}\n")
}

/// A `document.create` that `MemoryStorage` resolved from a `document.copy`:
/// TS builds its content as the literal `{ kind: "base", version, value }`,
/// so its keys serialize kind-first.
fn resolved_copy_json(write: &JsonValue) -> JsonValue {
    let Some(content) = get(write, "content") else {
        return write.clone();
    };
    let reordered = object([
        (
            "kind",
            get(content, "kind").cloned().unwrap_or(JsonValue::Null),
        ),
        (
            "version",
            get(content, "version").cloned().unwrap_or(JsonValue::Null),
        ),
        (
            "value",
            get(content, "value").cloned().unwrap_or(JsonValue::Null),
        ),
    ]);
    let mut write = write.clone();
    if let Some(fields) = write.as_object_mut() {
        fields.insert("content", reordered);
    }
    write
}

fn object<const N: usize>(entries: [(&str, JsonValue); N]) -> JsonValue {
    JsonValue::Object(Arc::new(entries.into_iter().collect::<JsonObject>()))
}

fn number(value: i64) -> JsonValue {
    // Ids, sequences, and ordinals are safe integers.
    JsonValue::try_from(value).unwrap_or(JsonValue::Null)
}

/// `Map.set` on an insertion-ordered map: replace in place or append.
fn set_ordered<K: PartialEq, V>(entries: &mut Vec<(K, V)>, key: K, value: V) {
    if let Some(entry) = entries.iter_mut().find(|(existing, _)| *existing == key) {
        entry.1 = value;
    } else {
        entries.push((key, value));
    }
}

/// `Set.add` on an insertion-ordered set.
fn add_ordered<K: PartialEq>(entries: &mut Vec<K>, key: K) {
    if !entries.contains(&key) {
        entries.push(key);
    }
}

/// One operation of a validated commit marker.
#[derive(Clone, Debug)]
enum MainOperation {
    /// `conversation`, `entry`, or `submission`: replayed as written.
    Record(JsonValue),
    /// A terminal task, inline in the marker.
    Task {
        id: i64,
        write: JsonValue,
    },
    TaskSidecar {
        id: i64,
        ordinal: i64,
    },
    DocumentCreate {
        id: i64,
        record: JsonValue,
        ordinal: i64,
    },
    DocumentChange {
        id: i64,
        ordinal: i64,
    },
    DocumentRetire {
        id: i64,
        write: JsonValue,
    },
}

#[derive(Clone, Debug)]
struct MainMarker {
    seq: i64,
    writes: Vec<MainOperation>,
}

#[derive(Clone, Debug)]
enum SidecarPayload {
    Task { id: i64, value: JsonValue },
    Document { id: i64, content: JsonValue },
}

#[derive(Clone, Debug)]
struct SidecarRecord {
    /// The parsed line, re-serialized verbatim when reclamation retains it.
    raw: JsonValue,
    seq: i64,
    ordinal: i64,
    payload: SidecarPayload,
}

impl SidecarRecord {
    fn is_base_of(&self, id: i64) -> bool {
        matches!(
            &self.payload,
            SidecarPayload::Document { id: payload_id, content }
                if *payload_id == id
                    && get(content, "kind").and_then(JsonValue::as_str) == Some("base")
        )
    }
}

#[derive(Clone, Debug)]
struct ParsedLine<T> {
    value: T,
    start: usize,
}

#[derive(Clone, Debug)]
struct ParsedFile<T> {
    path: String,
    lines: Vec<ParsedLine<T>>,
}

#[derive(Clone, Debug)]
struct EncodedCommit {
    marker: String,
    /// File name → appended text, in first-write order.
    sidecars: Vec<(String, String)>,
}

impl EncodedCommit {
    fn sidecar(&self, file: &str) -> Option<&str> {
        self.sidecars
            .iter()
            .find(|(name, _)| name == file)
            .map(|(_, content)| content.as_str())
    }
}

fn parse_json(text: &str, description: &str) -> Result<JsonValue, StorageError> {
    JsonValue::parse(text).map_err(|error| {
        failed(JsonlCorruptionError::caused(
            format!("Malformed complete {description}"),
            Arc::new(error),
        ))
    })
}

fn validate_main_operation(
    value: &JsonValue,
    description: &str,
) -> Result<MainOperation, StorageError> {
    let Some(kind) = type_of(value) else {
        return Err(corruption(format!("Invalid write in {description}")));
    };
    match kind {
        "conversation" | "entry" | "submission" => {
            let inner = get(value, "value");
            if !is_object(inner) || safe_integer(inner.and_then(|v| get(v, "id"))).is_none() {
                return Err(corruption(format!("Invalid {kind} write in {description}")));
            }
            Ok(MainOperation::Record(value.clone()))
        }
        "task" => {
            let inner = get(value, "value");
            let id = safe_integer(inner.and_then(|v| get(v, "id")));
            let state = inner.and_then(|v| get(v, "state"));
            match (inner, id) {
                (Some(task), Some(id))
                    if task.is_object() && is_object(state) && is_terminal(task) =>
                {
                    Ok(MainOperation::Task {
                        id,
                        write: value.clone(),
                    })
                }
                _ => Err(corruption(format!(
                    "Invalid terminal task write in {description}"
                ))),
            }
        }
        "document.retire" => match safe_integer(get(value, "id")) {
            Some(id) => Ok(MainOperation::DocumentRetire {
                id,
                write: value.clone(),
            }),
            None => Err(corruption(format!(
                "Invalid document retirement in {description}"
            ))),
        },
        "task.sidecar" => match (
            safe_integer(get(value, "id")),
            safe_integer(get(value, "ordinal")),
        ) {
            (Some(id), Some(ordinal)) if ordinal >= 0 => {
                Ok(MainOperation::TaskSidecar { id, ordinal })
            }
            _ => Err(corruption(format!(
                "Invalid task sidecar write in {description}"
            ))),
        },
        "document.create" => {
            let record = get(value, "record");
            match (
                record,
                safe_integer(record.and_then(|r| get(r, "id"))),
                safe_integer(get(value, "ordinal")),
            ) {
                (Some(record), Some(id), Some(ordinal)) if record.is_object() && ordinal >= 0 => {
                    Ok(MainOperation::DocumentCreate {
                        id,
                        record: record.clone(),
                        ordinal,
                    })
                }
                _ => Err(corruption(format!(
                    "Invalid document creation in {description}"
                ))),
            }
        }
        "document.change" => match (
            safe_integer(get(value, "id")),
            safe_integer(get(value, "ordinal")),
        ) {
            (Some(id), Some(ordinal)) if ordinal >= 0 => {
                Ok(MainOperation::DocumentChange { id, ordinal })
            }
            _ => Err(corruption(format!(
                "Invalid document change in {description}"
            ))),
        },
        _ => Err(corruption(format!("Unknown write type in {description}"))),
    }
}

fn parse_main_marker(text: &str, line: usize) -> Result<MainMarker, StorageError> {
    let description = format!("{MAIN_FILE} line {line}");
    let value = parse_json(text, &description)?;
    let seq = safe_integer(get(&value, "seq"));
    let writes = get(&value, "writes").and_then(JsonValue::as_array);
    let (Some(seq), Some(writes)) = (seq, writes) else {
        return Err(corruption(format!(
            "Invalid commit marker in {description}"
        )));
    };
    if get(&value, "format").and_then(JsonValue::as_f64) != Some(FORMAT_VERSION)
        || type_of(&value) != Some("commit")
        || seq < 1
    {
        return Err(corruption(format!(
            "Invalid commit marker in {description}"
        )));
    }
    let writes = writes
        .iter()
        .map(|write| validate_main_operation(write, &description))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(MainMarker { seq, writes })
}

fn validate_document_content(
    value: Option<&JsonValue>,
    description: &str,
) -> Result<(), StorageError> {
    let invalid = || corruption(format!("Invalid document content in {description}"));
    let Some(content) = value.filter(|content| content.is_object()) else {
        return Err(invalid());
    };
    match safe_integer(get(content, "version")) {
        Some(version) if version >= 1 => {}
        _ => return Err(invalid()),
    }
    match get(content, "kind").and_then(JsonValue::as_str) {
        Some("base") if is_object(get(content, "value")) => Ok(()),
        Some("delta") if get(content, "ops").is_some_and(JsonValue::is_array) => Ok(()),
        _ => Err(invalid()),
    }
}

fn parse_sidecar_record(
    text: &str,
    file: &str,
    line: usize,
) -> Result<SidecarRecord, StorageError> {
    let description = format!("{file} line {line}");
    let value = parse_json(text, &description)?;
    let invalid = || corruption(format!("Invalid sidecar record in {description}"));
    let seq = safe_integer(get(&value, "seq")).ok_or_else(invalid)?;
    let ordinal = safe_integer(get(&value, "ordinal")).ok_or_else(invalid)?;
    let payload = get(&value, "payload").filter(|payload| payload.is_object());
    if get(&value, "format").and_then(JsonValue::as_f64) != Some(FORMAT_VERSION)
        || type_of(&value) != Some("record")
        || seq < 1
        || ordinal < 0
    {
        return Err(invalid());
    }
    let Some((payload, payload_type)) =
        payload.and_then(|payload| type_of(payload).map(|kind| (payload, kind)))
    else {
        return Err(invalid());
    };
    let payload = match payload_type {
        "task" => {
            let task = get(payload, "value").filter(|task| task.is_object());
            let id = safe_integer(task.and_then(|task| get(task, "id")));
            match (task, id) {
                (Some(task), Some(id)) if is_object(get(task, "state")) && !is_terminal(task) => {
                    SidecarPayload::Task {
                        id,
                        value: task.clone(),
                    }
                }
                _ => {
                    return Err(corruption(format!(
                        "Invalid live task record in {description}"
                    )))
                }
            }
        }
        "document" => {
            let Some(id) = safe_integer(get(payload, "id")) else {
                return Err(corruption(format!(
                    "Invalid document record in {description}"
                )));
            };
            let content = get(payload, "content");
            validate_document_content(content, &description)?;
            SidecarPayload::Document {
                id,
                content: content.cloned().unwrap_or(JsonValue::Null),
            }
        }
        _ => {
            return Err(corruption(format!(
                "Unknown sidecar record type in {description}"
            )))
        }
    };
    Ok(SidecarRecord {
        raw: value,
        seq,
        ordinal,
        payload,
    })
}

/// Mutable bookkeeping; never locked across an `.await`.
#[derive(Default)]
struct State {
    closed: bool,
    poison: Option<Arc<JsonlStoragePoisonedError>>,
    current_only_documents: HashSet<i64>,
    live_task_sidecars: HashSet<i64>,
}

/// Portable JSONL implementation of the storage contract.
pub struct JsonlStorage {
    fs: Arc<dyn FileSystem>,
    directory: String,
    main_path: String,
    fsync: bool,
    memory: MemoryStorage,
    state: Mutex<State>,
}

impl std::fmt::Debug for JsonlStorage {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("JsonlStorage")
            .field("directory", &self.directory)
            .field("fsync", &self.fsync)
            .finish_non_exhaustive()
    }
}

impl JsonlStorage {
    /// Open or create a JSONL storage directory using the supplied filesystem.
    ///
    /// # Errors
    /// Fails when the directory cannot be prepared or read, or when its
    /// committed data is corrupt ([`JsonlCorruptionError`]).
    pub async fn open(
        directory: &str,
        fs: Arc<dyn FileSystem>,
        cx: &Context,
        options: JsonlStorageOptions,
    ) -> Result<Self, StorageError> {
        let absolute = fs
            .absolute_path(directory, cx)
            .await
            .map_err(|error| failed(error_from_file("path resolution", error)))?;
        fs.create_dir(&absolute, CreateDirOptions { recursive: true }, cx)
            .await
            .map_err(|error| failed(error_from_file("directory creation", error)))?;
        let main_path = fs
            .join_path(&[absolute.as_str(), MAIN_FILE], cx)
            .await
            .map_err(|error| failed(error_from_file("path join", error)))?;
        let storage = Self {
            fs,
            directory: absolute,
            main_path,
            fsync: options.fsync,
            memory: MemoryStorage::new(),
            state: Mutex::new(State::default()),
        };
        storage.recover(cx).await?;
        Ok(storage)
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    async fn commit_writes(
        &self,
        writes: &[StorageWrite],
        cx: &Context,
    ) -> Result<Seq, StorageError> {
        self.assert_usable()?;
        let prepared = self.memory.prepare_commit(writes, None)?;
        let json_writes = prepared
            .writes()
            .iter()
            .enumerate()
            .map(|(index, write)| {
                let json = to_json(write)?;
                Ok(if prepared.is_resolved_copy(index) {
                    resolved_copy_json(&json)
                } else {
                    json
                })
            })
            .collect::<Result<Vec<_>, eukhe_chord::json::JsonError>>()
            .map_err(failed)?;
        let seq = i64::try_from(prepared.seq().get()).map_err(failed)?;
        let encoded = Self::encode_commit(seq, &json_writes);
        let reclamations = self.plan_reclamations(&json_writes, &encoded);
        let paths = try_join_all(
            encoded
                .sidecars
                .iter()
                .map(|(file, _)| self.resolve_file(file, cx)),
        )
        .await?;

        for ((file, content), path) in encoded.sidecars.iter().zip(&paths) {
            if let Err(error) = self.fs.append_file(path, content.as_bytes(), cx).await {
                return Err(self.poison(error_from_file(format!("append to {file}"), error)));
            }
        }
        if self.fsync {
            for ((file, _), path) in encoded.sidecars.iter().zip(&paths) {
                if let Err(error) = self.fs.flush_file(path, cx).await {
                    return Err(self.poison(error_from_file(format!("flush of {file}"), error)));
                }
            }
        }
        if let Err(error) = self
            .fs
            .append_file(&self.main_path, encoded.marker.as_bytes(), cx)
            .await
        {
            return Err(self.poison(error_from_file(format!("append to {MAIN_FILE}"), error)));
        }
        let seq = prepared.apply();
        self.adopt_sidecar_state(&json_writes);
        self.reclaim_sidecars(&reclamations, cx).await;
        Ok(seq)
    }

    #[allow(clippy::too_many_lines)] // One switch over the TS write types.
    fn encode_commit(seq: i64, writes: &[JsonValue]) -> EncodedCommit {
        let mut main_writes: Vec<JsonValue> = Vec::new();
        let mut records: Vec<(String, Vec<JsonValue>)> = Vec::new();
        let mut next_ordinal: i64 = 0;
        let mut add_sidecar = |file: String, payload: JsonValue| -> i64 {
            let ordinal = next_ordinal;
            next_ordinal += 1;
            let record = object([
                ("format", number(1)),
                ("type", "record".into()),
                ("seq", number(seq)),
                ("ordinal", number(ordinal)),
                ("payload", payload),
            ]);
            if let Some((_, file_records)) = records.iter_mut().find(|(name, _)| *name == file) {
                file_records.push(record);
            } else {
                records.push((file, vec![record]));
            }
            ordinal
        };

        for write in writes {
            match type_of(write) {
                Some("conversation" | "entry" | "submission" | "document.retire") => {
                    main_writes.push(write.clone());
                }
                Some("task") => {
                    let value = get(write, "value").cloned().unwrap_or(JsonValue::Null);
                    if is_terminal(&value) {
                        main_writes.push(write.clone());
                    } else {
                        let id = value.get("id").cloned().unwrap_or(JsonValue::Null);
                        let ordinal = add_sidecar(
                            sidecar_file_name("task", safe_integer(Some(&id)).unwrap_or(0)),
                            object([("type", "task".into()), ("value", value)]),
                        );
                        main_writes.push(object([
                            ("type", "task.sidecar".into()),
                            ("id", id),
                            ("ordinal", number(ordinal)),
                        ]));
                    }
                }
                Some("document.create") => {
                    let record = get(write, "record").cloned().unwrap_or(JsonValue::Null);
                    let id = record.get("id").cloned().unwrap_or(JsonValue::Null);
                    let ordinal = add_sidecar(
                        sidecar_file_name("doc", safe_integer(Some(&id)).unwrap_or(0)),
                        object([
                            ("type", "document".into()),
                            ("id", id),
                            (
                                "content",
                                get(write, "content").cloned().unwrap_or(JsonValue::Null),
                            ),
                        ]),
                    );
                    main_writes.push(object([
                        ("type", "document.create".into()),
                        ("record", record),
                        ("ordinal", number(ordinal)),
                    ]));
                }
                Some("document.change") => {
                    let id = get(write, "id").cloned().unwrap_or(JsonValue::Null);
                    let ordinal = add_sidecar(
                        sidecar_file_name("doc", safe_integer(Some(&id)).unwrap_or(0)),
                        object([
                            ("type", "document".into()),
                            ("id", id.clone()),
                            (
                                "content",
                                get(write, "content").cloned().unwrap_or(JsonValue::Null),
                            ),
                        ]),
                    );
                    main_writes.push(object([
                        ("type", "document.change".into()),
                        ("id", id),
                        ("ordinal", number(ordinal)),
                    ]));
                }
                // Prepared commits contain no `document.copy`; the TS switch
                // has no other cases.
                _ => {}
            }
        }

        let sidecars = records
            .into_iter()
            .map(|(file, file_records)| {
                let content = file_records.iter().map(json_line).collect::<String>();
                (file, content)
            })
            .collect();
        let marker = object([
            ("format", number(1)),
            ("type", "commit".into()),
            ("seq", number(seq)),
            ("writes", JsonValue::Array(Arc::new(main_writes))),
        ]);
        EncodedCommit {
            marker: json_line(&marker),
            sidecars,
        }
    }

    fn plan_reclamations(
        &self,
        writes: &[JsonValue],
        encoded: &EncodedCommit,
    ) -> Vec<(String, String)> {
        let mut created_current_only = Vec::new();
        let mut retired = Vec::new();
        let mut bases = Vec::new();
        let mut final_tasks: Vec<(i64, bool)> = Vec::new();
        for write in writes {
            match type_of(write) {
                Some("document.create") => {
                    let record = get(write, "record").unwrap_or(&JsonValue::Null);
                    if is_current_only(record) {
                        if let Some(id) = safe_integer(get(record, "id")) {
                            add_ordered(&mut created_current_only, id);
                        }
                    }
                }
                Some("document.change") => {
                    let kind = get(write, "content")
                        .and_then(|content| get(content, "kind"))
                        .and_then(JsonValue::as_str);
                    if let (Some("base"), Some(id)) = (kind, safe_integer(get(write, "id"))) {
                        add_ordered(&mut bases, id);
                    }
                }
                Some("document.retire") => {
                    if let Some(id) = safe_integer(get(write, "id")) {
                        add_ordered(&mut retired, id);
                    }
                }
                Some("task") => {
                    let task = get(write, "value").unwrap_or(&JsonValue::Null);
                    if let Some(id) = safe_integer(get(task, "id")) {
                        set_ordered(&mut final_tasks, id, is_terminal(task));
                    }
                }
                _ => {}
            }
        }

        let state = self.lock();
        let is_current_only_document = |id: i64| {
            state.current_only_documents.contains(&id) || created_current_only.contains(&id)
        };
        let mut replacements: Vec<(String, String)> = Vec::new();
        for &id in &retired {
            if is_current_only_document(id) {
                set_ordered(
                    &mut replacements,
                    sidecar_file_name("doc", id),
                    String::new(),
                );
            }
        }
        for &id in &bases {
            if !is_current_only_document(id) || retired.contains(&id) {
                continue;
            }
            let file = sidecar_file_name("doc", id);
            if let Some(content) = encoded.sidecar(&file) {
                let content = content.to_owned();
                set_ordered(&mut replacements, file, content);
            }
        }
        for &(id, terminal) in &final_tasks {
            let file = sidecar_file_name("task", id);
            if terminal
                && (state.live_task_sidecars.contains(&id) || encoded.sidecar(&file).is_some())
            {
                set_ordered(&mut replacements, file, String::new());
            }
        }
        replacements
    }

    fn adopt_sidecar_state(&self, writes: &[JsonValue]) {
        let mut state = self.lock();
        for write in writes {
            match type_of(write) {
                Some("document.create") => {
                    let record = get(write, "record").unwrap_or(&JsonValue::Null);
                    if is_current_only(record) {
                        if let Some(id) = safe_integer(get(record, "id")) {
                            state.current_only_documents.insert(id);
                        }
                    }
                }
                Some("task") => {
                    let task = get(write, "value").unwrap_or(&JsonValue::Null);
                    if let Some(id) = safe_integer(get(task, "id")) {
                        if is_terminal(task) {
                            state.live_task_sidecars.remove(&id);
                        } else {
                            state.live_task_sidecars.insert(id);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// The marker already published this state, so reclamation is retryable
    /// best-effort maintenance: every failure stops or skips it silently.
    async fn reclaim_sidecars(&self, replacements: &[(String, String)], cx: &Context) {
        if replacements.is_empty() {
            return;
        }
        if self.fsync && self.fs.flush_file(&self.main_path, cx).await.is_err() {
            return;
        }
        for (file, content) in replacements {
            self.replace_sidecar(file, content, cx).await;
        }
    }

    async fn replace_sidecar(&self, file: &str, content: &str, cx: &Context) {
        let Ok(path) = self
            .fs
            .join_path(&[self.directory.as_str(), file], cx)
            .await
        else {
            return;
        };
        if content.is_empty() {
            // Best-effort: a sidecar left behind is reclaimed on the next open.
            let _ = self
                .fs
                .remove(
                    &path,
                    RemoveOptions {
                        recursive: false,
                        force: true,
                    },
                    cx,
                )
                .await;
            return;
        }
        let temporary_name = format!("{file}{RECLAIM_SUFFIX}");
        let Ok(temporary_path) = self
            .fs
            .join_path(&[self.directory.as_str(), temporary_name.as_str()], cx)
            .await
        else {
            return;
        };
        if self
            .fs
            .write_file(&temporary_path, content.as_bytes(), cx)
            .await
            .is_err()
        {
            return;
        }
        if self.fsync && self.fs.flush_file(&temporary_path, cx).await.is_err() {
            return;
        }
        // Best-effort: a leftover temporary file is removed on the next open.
        let _ = self.fs.rename_file(&temporary_path, &path, cx).await;
    }

    #[allow(clippy::too_many_lines)] // One recovery pass, kept in TS order.
    async fn recover(&self, cx: &Context) -> Result<(), StorageError> {
        let fs = &*self.fs;
        let directory = self.directory.as_str();
        let main = read_lines(fs, &self.main_path, MAIN_FILE, cx, parse_main_marker).await?;
        let mut previous_seq = 0;
        for marker in &main.lines {
            if marker.value.seq <= previous_seq {
                return Err(corruption(format!(
                    "Commit sequence does not strictly increase in {MAIN_FILE}"
                )));
            }
            previous_seq = marker.value.seq;
        }

        let listed = fs
            .list_dir(directory, cx)
            .await
            .map_err(|error| failed(error_from_file("directory listing", error)))?;
        for info in &listed {
            if info.kind == FileKind::File && is_reclaim_file_name(&info.name) {
                // Best-effort, like the TS `await fs.remove(...)` whose result is unused.
                let _ = fs
                    .remove(
                        &info.path,
                        RemoveOptions {
                            recursive: false,
                            force: true,
                        },
                        cx,
                    )
                    .await;
            }
        }
        let mut sidecar_files: Vec<&str> = listed
            .iter()
            .filter(|info| info.kind == FileKind::File && is_sidecar_file_name(&info.name))
            .map(|info| info.name.as_str())
            .collect();
        sidecar_files.sort_unstable();

        let mut parsed_files: Vec<(String, ParsedFile<SidecarRecord>)> = Vec::new();
        let mut record_by_key: HashMap<SidecarKey, SidecarRecord> = HashMap::new();
        for file in sidecar_files {
            let path = fs
                .join_path(&[directory, file], cx)
                .await
                .map_err(|error| failed(error_from_file("path join", error)))?;
            let parsed = read_lines(fs, &path, file, cx, |text, line| {
                parse_sidecar_record(text, file, line)
            })
            .await?;
            let mut previous: Option<&SidecarRecord> = None;
            for line in &parsed.lines {
                if let Some(previous) = previous {
                    if line.value.seq < previous.seq
                        || (line.value.seq == previous.seq
                            && line.value.ordinal <= previous.ordinal)
                    {
                        return Err(corruption(format!(
                            "Sidecar records are out of order in {file}"
                        )));
                    }
                }
                previous = Some(&line.value);
                record_by_key.insert(
                    sidecar_key(file, line.value.seq, line.value.ordinal),
                    line.value.clone(),
                );
            }
            parsed_files.push((file.to_owned(), parsed));
        }

        let mut current_only_documents: Vec<i64> = Vec::new();
        let mut retired_documents: Vec<i64> = Vec::new();
        let mut final_task_is_live: Vec<(i64, bool)> = Vec::new();
        for marker in &main.lines {
            for operation in &marker.value.writes {
                match operation {
                    MainOperation::DocumentCreate { id, record, .. } => {
                        if is_current_only(record) {
                            add_ordered(&mut current_only_documents, *id);
                        }
                    }
                    MainOperation::DocumentRetire { id, .. } => {
                        add_ordered(&mut retired_documents, *id);
                    }
                    MainOperation::Task { id, .. } => {
                        set_ordered(&mut final_task_is_live, *id, false);
                    }
                    MainOperation::TaskSidecar { id, .. } => {
                        set_ordered(&mut final_task_is_live, *id, true);
                    }
                    MainOperation::Record(_) | MainOperation::DocumentChange { .. } => {}
                }
            }
        }
        let retired_current_only: HashSet<i64> = retired_documents
            .iter()
            .copied()
            .filter(|id| current_only_documents.contains(id))
            .collect();

        let mut latest_bases: HashMap<i64, (i64, i64)> = HashMap::new();
        for marker in &main.lines {
            for operation in &marker.value.writes {
                let (id, ordinal) = match operation {
                    MainOperation::DocumentCreate { id, ordinal, .. }
                    | MainOperation::DocumentChange { id, ordinal } => (*id, *ordinal),
                    MainOperation::Record(_)
                    | MainOperation::Task { .. }
                    | MainOperation::TaskSidecar { .. }
                    | MainOperation::DocumentRetire { .. } => continue,
                };
                if !current_only_documents.contains(&id) {
                    continue;
                }
                let key = sidecar_key(&sidecar_file_name("doc", id), marker.value.seq, ordinal);
                let Some(record) = record_by_key.get(&key) else {
                    continue;
                };
                if !record.is_base_of(id) {
                    continue;
                }
                let replace = match latest_bases.get(&id) {
                    None => true,
                    Some(&(seq, ordinal)) => {
                        record.seq > seq || (record.seq == seq && record.ordinal > ordinal)
                    }
                };
                if replace {
                    latest_bases.insert(id, (record.seq, record.ordinal));
                }
            }
        }

        let is_before_latest_base = |id: i64, seq: i64, ordinal: i64| {
            latest_bases
                .get(&id)
                .is_some_and(|&(base_seq, base_ordinal)| {
                    seq < base_seq || (seq == base_seq && ordinal < base_ordinal)
                })
        };
        let terminal_tasks: HashSet<i64> = final_task_is_live
            .iter()
            .filter(|(_, live)| !live)
            .map(|(id, _)| *id)
            .collect();
        let mut confirmed: HashSet<SidecarKey> = HashSet::new();
        for line in &main.lines {
            let marker = &line.value;
            let mut writes: Vec<JsonValue> = Vec::new();
            for operation in &marker.writes {
                match operation {
                    MainOperation::Record(write)
                    | MainOperation::Task { write, .. }
                    | MainOperation::DocumentRetire { write, .. } => writes.push(write.clone()),
                    MainOperation::TaskSidecar { id, ordinal } => {
                        let optional = terminal_tasks.contains(id);
                        let record = confirm_record(
                            marker,
                            *ordinal,
                            &sidecar_file_name("task", *id),
                            &record_by_key,
                            &mut confirmed,
                            optional,
                        )?;
                        if let Some(record) = record {
                            let SidecarPayload::Task { id: task_id, value } = &record.payload
                            else {
                                return Err(corruption(format!(
                                    "Confirmed task sidecar data does not match commit {}",
                                    marker.seq
                                )));
                            };
                            if task_id != id {
                                return Err(corruption(format!(
                                    "Confirmed task sidecar data does not match commit {}",
                                    marker.seq
                                )));
                            }
                            if !optional {
                                writes.push(object([
                                    ("type", "task".into()),
                                    ("value", value.clone()),
                                ]));
                            }
                        }
                    }
                    MainOperation::DocumentCreate { id, ordinal, .. }
                    | MainOperation::DocumentChange { id, ordinal } => {
                        let reclaimed = retired_current_only.contains(id)
                            || is_before_latest_base(*id, marker.seq, *ordinal);
                        let record = confirm_record(
                            marker,
                            *ordinal,
                            &sidecar_file_name("doc", *id),
                            &record_by_key,
                            &mut confirmed,
                            reclaimed,
                        )?;
                        let mut content: Option<JsonValue> = None;
                        if let Some(record) = record {
                            match &record.payload {
                                SidecarPayload::Document {
                                    id: document_id,
                                    content: record_content,
                                } if document_id == id => content = Some(record_content.clone()),
                                SidecarPayload::Document { .. } | SidecarPayload::Task { .. } => {
                                    return Err(corruption(format!(
                                        "Confirmed document sidecar data does not match commit {}",
                                        marker.seq
                                    )));
                                }
                            }
                        }
                        if let MainOperation::DocumentCreate { record, .. } = operation {
                            if let Some(content) = &content {
                                if get(content, "kind").and_then(JsonValue::as_str) != Some("base")
                                {
                                    return Err(corruption(format!(
                                        "Document creation lacks a confirmed base in commit {}",
                                        marker.seq
                                    )));
                                }
                            }
                            let content = match content {
                                Some(content) if !reclaimed => content,
                                _ => object([
                                    ("kind", "base".into()),
                                    ("version", number(1)),
                                    ("value", JsonValue::object()),
                                ]),
                            };
                            writes.push(object([
                                ("type", "document.create".into()),
                                ("record", record.clone()),
                                ("content", content),
                            ]));
                        } else if let (false, Some(content)) = (reclaimed, content) {
                            writes.push(object([
                                ("type", "document.change".into()),
                                ("id", number(*id)),
                                ("content", content),
                            ]));
                        }
                    }
                }
            }
            self.replay(marker.seq, &writes)?;
        }

        let mut reclamations: Vec<(String, String)> = Vec::new();
        for (file, parsed) in &parsed_files {
            let mut unconfirmed_at: Option<usize> = None;
            for line in &parsed.lines {
                let key = sidecar_key(file, line.value.seq, line.value.ordinal);
                if confirmed.contains(&key) {
                    if unconfirmed_at.is_some() {
                        return Err(corruption(format!(
                            "Confirmed record follows an unconfirmed tail in {file}"
                        )));
                    }
                } else if unconfirmed_at.is_none() {
                    unconfirmed_at = Some(line.start);
                }
            }
            if let Some(size) = unconfirmed_at {
                fs.truncate_file(&parsed.path, byte_size(size), cx)
                    .await
                    .map_err(|error| {
                        failed(error_from_file(format!("tail truncation of {file}"), error))
                    })?;
            }

            let numeric_id = file_numeric_id(file);
            let confirmed_lines: Vec<&ParsedLine<SidecarRecord>> = parsed
                .lines
                .iter()
                .filter(|line| {
                    confirmed.contains(&sidecar_key(file, line.value.seq, line.value.ordinal))
                })
                .collect();
            let mut retained: Option<Vec<&ParsedLine<SidecarRecord>>> = None;
            if file.starts_with("task-")
                && numeric_id.is_some_and(|id| terminal_tasks.contains(&id))
            {
                retained = Some(Vec::new());
            } else if file.starts_with("doc-") {
                if let Some(document_id) = numeric_id {
                    if retired_current_only.contains(&document_id) {
                        retained = Some(Vec::new());
                    } else if latest_bases.contains_key(&document_id) {
                        retained = Some(
                            confirmed_lines
                                .iter()
                                .copied()
                                .filter(|line| {
                                    !is_before_latest_base(
                                        document_id,
                                        line.value.seq,
                                        line.value.ordinal,
                                    )
                                })
                                .collect(),
                        );
                    }
                }
            }
            if let Some(retained) = retained {
                if retained.len() < confirmed_lines.len() || retained.is_empty() {
                    let content = retained
                        .iter()
                        .map(|line| json_line(&line.value.raw))
                        .collect();
                    set_ordered(&mut reclamations, file.clone(), content);
                }
            }
        }
        self.reclaim_sidecars(&reclamations, cx).await;

        let mut state = self.lock();
        state.current_only_documents.extend(current_only_documents);
        state.live_task_sidecars.extend(
            final_task_is_live
                .into_iter()
                .filter(|(_, live)| *live)
                .map(|(id, _)| id),
        );
        Ok(())
    }

    /// Apply one recovered commit at its persisted sequence.
    fn replay(&self, seq: i64, writes: &[JsonValue]) -> Result<(), StorageError> {
        let invalid = |cause: Cause| {
            failed(JsonlCorruptionError::caused(
                format!("Invalid committed state at sequence {seq}"),
                cause,
            ))
        };
        let typed = writes
            .iter()
            .map(from_json::<StorageWrite>)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| invalid(Arc::new(error)))?;
        let sequence = u64::try_from(seq).map_err(|error| invalid(Arc::new(error)))?;
        let prepared: PreparedMemoryCommit = self
            .memory
            .prepare_commit(&typed, Some(Seq::from_number(sequence)))
            .map_err(|error| invalid(Arc::new(error)))?;
        prepared.apply();
        Ok(())
    }

    async fn resolve_file(&self, file: &str, cx: &Context) -> Result<String, StorageError> {
        self.fs
            .join_path(&[self.directory.as_str(), file], cx)
            .await
            .map_err(|error| failed(error_from_file("path join", error)))
    }

    fn store(&self) -> Result<&MemoryStorage, StorageError> {
        self.assert_usable()?;
        Ok(&self.memory)
    }

    fn poison(&self, cause: JsonlFileError) -> StorageError {
        let mut state = self.lock();
        let poison = state
            .poison
            .get_or_insert_with(|| {
                Arc::new(JsonlStoragePoisonedError {
                    cause: Arc::new(cause),
                })
            })
            .clone();
        StorageError::Failed(poison)
    }

    fn assert_usable(&self) -> Result<(), StorageError> {
        let state = self.lock();
        if state.closed {
            return Err(failed(ClosedError));
        }
        if let Some(poison) = &state.poison {
            return Err(StorageError::Failed(poison.clone()));
        }
        Ok(())
    }
}

fn confirm_record<'a>(
    marker: &MainMarker,
    ordinal: i64,
    file: &str,
    record_by_key: &'a HashMap<SidecarKey, SidecarRecord>,
    confirmed: &mut HashSet<SidecarKey>,
    optional: bool,
) -> Result<Option<&'a SidecarRecord>, StorageError> {
    let key = sidecar_key(file, marker.seq, ordinal);
    if confirmed.contains(&key) {
        return Err(corruption("Sidecar record is confirmed more than once"));
    }
    let Some(record) = record_by_key.get(&key) else {
        if optional {
            return Ok(None);
        }
        return Err(corruption(format!(
            "Missing confirmed sidecar record {file} at sequence {}",
            marker.seq
        )));
    };
    confirmed.insert(key);
    Ok(Some(record))
}

/// `Number(file.slice(file.indexOf("-") + 1, -".jsonl".length))`; `None` when
/// the number is not a safe integer and so names no record.
fn file_numeric_id(file: &str) -> Option<i64> {
    let stem = file.strip_suffix(JSONL_SUFFIX)?;
    let digits = &stem[stem.find('-')? + 1..];
    let number: f64 = digits.parse().ok()?;
    safe_integer(Some(&JsonValue::try_from(number).ok()?))
}

/// A byte offset as the JS number `truncateFile` takes.
fn byte_size(size: usize) -> f64 {
    // File sizes stay far below 2^53.
    #[allow(clippy::cast_precision_loss)]
    let size = size as f64;
    size
}

/// UTF-8 decoding of one complete line like `new TextDecoder("utf-8",
/// { fatal: true })`: invalid bytes fail and a leading BOM is dropped.
fn decode_line(bytes: &[u8]) -> Result<&str, std::str::Utf8Error> {
    let text = std::str::from_utf8(bytes)?;
    Ok(text.strip_prefix('\u{FEFF}').unwrap_or(text))
}

async fn read_lines<T>(
    fs: &dyn FileSystem,
    path: &str,
    name: &str,
    cx: &Context,
    mut parse: impl FnMut(&str, usize) -> Result<T, StorageError>,
) -> Result<ParsedFile<T>, StorageError> {
    let bytes = match fs.read_binary_file(path, cx).await {
        Ok(bytes) => bytes,
        Err(error) if error.code == FileErrorCode::NotFound => {
            return Ok(ParsedFile {
                path: path.to_owned(),
                lines: Vec::new(),
            })
        }
        Err(error) => return Err(failed(error_from_file(format!("read of {name}"), error))),
    };
    let mut complete_size = bytes.len();
    if complete_size > 0 && bytes[complete_size - 1] != b'\n' {
        complete_size = bytes
            .iter()
            .rposition(|&byte| byte == b'\n')
            .map_or(0, |index| index + 1);
        fs.truncate_file(path, byte_size(complete_size), cx)
            .await
            .map_err(|error| {
                failed(error_from_file(
                    format!("torn-line truncation of {name}"),
                    error,
                ))
            })?;
    }
    let mut lines = Vec::new();
    let mut start = 0;
    let mut line_number = 1;
    for end in 0..complete_size {
        if bytes[end] != b'\n' {
            continue;
        }
        let text = decode_line(&bytes[start..end]).map_err(|error| {
            failed(JsonlCorruptionError::caused(
                format!("Invalid UTF-8 in complete {name} line {line_number}"),
                Arc::new(error),
            ))
        })?;
        lines.push(ParsedLine {
            value: parse(text, line_number)?,
            start,
        });
        start = end + 1;
        line_number += 1;
    }
    Ok(ParsedFile {
        path: path.to_owned(),
        lines,
    })
}

impl Storage for JsonlStorage {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        Box::pin(self.commit_writes(writes, cx))
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        Box::pin(async move { self.store()?.mint_id().await })
    }

    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>> {
        Box::pin(async move { self.store()?.conversation(id, cx).await })
    }

    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>> {
        Box::pin(async move {
            self.store()?
                .scan_conversations(query, limit, cursor, cx)
                .await
        })
    }

    fn entry<'a>(
        &'a self,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        Box::pin(async move { self.store()?.entry(id, cx).await })
    }

    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        Box::pin(async move { self.store()?.entry_in(conversation_id, id, cx).await })
    }

    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>> {
        Box::pin(async move {
            self.store()?
                .find_latest_head_marker(conversation_id, at_or_before_entry_id, cx)
                .await
        })
    }

    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>> {
        Box::pin(async move { self.store()?.scan_entries(query, limit, cursor, cx).await })
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        Box::pin(async move { self.store()?.task(id, cx).await })
    }

    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>> {
        Box::pin(async move { self.store()?.scan_tasks(query, limit, cursor, cx).await })
    }

    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        Box::pin(async move { self.store()?.submission(id, cx).await })
    }

    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>> {
        Box::pin(async move {
            self.store()?
                .scan_submissions(query, limit, cursor, cx)
                .await
        })
    }

    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        Box::pin(async move {
            self.store()?
                .submission_by_request(conversation_id, request_id, cx)
                .await
        })
    }

    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>> {
        Box::pin(async move { self.store()?.find_document(address, at, cx).await })
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
        Box::pin(async move { self.store()?.document(id, at, cx).await })
    }

    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>> {
        Box::pin(async move { self.store()?.scan_documents(query, limit, cursor, cx).await })
    }

    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        Box::pin(async move {
            {
                let mut state = self.lock();
                if state.closed {
                    return Ok(());
                }
                state.closed = true;
            }
            self.memory.close(cx).await
        })
    }
}
