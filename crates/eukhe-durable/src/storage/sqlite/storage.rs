//! Portable SQLite implementation of the durable storage contract. Port of
//! `storage/sqlite/storage.ts`.
//!
//! Records persist as `JSON.stringify` text; document deltas are applied in Rust with
//! [`eukhe_chord::delta::apply`]. Indexed strings (task kinds, request IDs, document kinds and
//! keys) are stored JSON-encoded so identities stay lossless across SQLite bindings.
//!
//! Like the TS methods, each method does its synchronous part (open check, cursor decoding,
//! admission, and its first database call) when called; the returned future finishes it.

use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::delta::{apply, DeltaError, Op};
use eukhe_chord::json::{from_json, to_json, JsonNumber, JsonValue};
use futures::channel::oneshot;
use futures::future::{self, BoxFuture, FutureExt, Shared};
use serde::de::DeserializeOwned;
use serde::Serialize;

use super::database::{
    SqliteDatabase, SqliteDatabaseExt, SqliteError, SqliteExecutor, SqliteRow, SqliteTransaction,
    SqliteValue,
};
use super::migrations::{apply_sqlite_migrations, SQLITE_MIGRATIONS};
use crate::errors::{StorageError, StorageRejected};
use crate::storage::common::{cursor_id, failure, is_alive_at, is_current_only, page, rejected};
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationQuery, ConversationRecord, Cursor, DocumentAddress,
    DocumentBase, DocumentContent, DocumentCopySource, DocumentCreate, DocumentId,
    DocumentIdentity, DocumentPoint, DocumentQuery, DocumentRecord, DocumentScope, EntryId,
    EntryQuery, EntryRecord, Page, Seq, Storage, StorageWrite, StoredDocument, StoredEntry,
    SubmissionId, SubmissionQuery, SubmissionRecord, SubmissionStatus, TaskId, TaskQuery,
    TaskStatus,
};

/// `Number.MAX_SAFE_INTEGER` as a JS number.
const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

const SELECT_METADATA: &str = "SELECT next_id, next_seq FROM durable_metadata WHERE singleton = 1";
const UPDATE_METADATA: &str =
    "UPDATE durable_metadata SET next_id = ?, next_seq = ? WHERE singleton = 1";
const SELECT_CONVERSATION: &str = "SELECT record FROM conversations WHERE id = ?";
const SELECT_ENTRY: &str = "SELECT record, commit_seq FROM entries WHERE id = ?";
const SELECT_LATEST_HEAD: &str = "SELECT record FROM entries WHERE conversation_id = ? AND head IS NOT NULL ORDER BY id DESC LIMIT 1";
const SELECT_LATEST_HEAD_UPTO: &str = "SELECT record FROM entries WHERE conversation_id = ? AND head IS NOT NULL AND id <= ? ORDER BY id DESC LIMIT 1";
const SELECT_TASK: &str = "SELECT record FROM tasks WHERE id = ?";
const SELECT_SUBMISSION: &str = "SELECT record FROM submissions WHERE id = ?";
const SELECT_SUBMISSION_BY_REQUEST: &str =
    "SELECT record FROM submissions WHERE conversation_id = ? AND request_id = ?";
const FIND_CURRENT_DOCUMENT: &str = "SELECT record FROM documents\n\t\t\t\t\tWHERE kind = ? AND scope_kind = ? AND owner_id = ? AND family = ? AND key_value = ?\n\t\t\t\t\tAND retired_at IS NULL ORDER BY created_at DESC LIMIT 1";
const FIND_DOCUMENT_AT: &str = "SELECT record FROM documents\n\t\t\t\t\tWHERE kind = ? AND scope_kind = ? AND owner_id = ? AND family = ? AND key_value = ?\n\t\t\t\t\tAND created_at <= ? AND (retired_at IS NULL OR retired_at > ?)\n\t\t\t\t\tORDER BY created_at DESC LIMIT 1";
const SELECT_DOCUMENT: &str = "SELECT record FROM documents WHERE id = ?";
const SELECT_BASE: &str = "SELECT seq, kind, version, content FROM document_revisions\n\t\t\t\tWHERE document_id = ? AND kind = 'base' AND seq <= ? ORDER BY seq DESC LIMIT 1";
const SELECT_TAIL: &str = "SELECT seq, kind, version, content FROM document_revisions\n\t\t\t\tWHERE document_id = ? AND seq > ? AND seq <= ? ORDER BY seq";
const SELECT_RECORD_TYPE: &str = "SELECT record_type FROM record_ids WHERE id = ?";
const SELECT_LAST_VERSION: &str =
    "SELECT version FROM document_revisions WHERE document_id = ? ORDER BY seq DESC LIMIT 1";
const SELECT_CURRENT_DOCUMENT_ID: &str = "SELECT id FROM documents\n\t\t\t\tWHERE kind = ? AND scope_kind = ? AND owner_id = ? AND family = ? AND key_value = ? AND retired_at IS NULL\n\t\t\t\tLIMIT 1";
const INSERT_CONVERSATION: &str = "INSERT INTO conversations (id, owner_conversation_id, owner_task_id, record) VALUES (?, ?, ?, ?)";
const INSERT_ENTRY: &str =
    "INSERT INTO entries (id, conversation_id, head, commit_seq, record) VALUES (?, ?, ?, ?, ?)";
const UPSERT_TASK: &str = "INSERT INTO tasks (id, conversation_id, kind, status, abort_requested, background, record)\n\t\t\t\t\t\tVALUES (?, ?, ?, ?, ?, ?, ?)\n\t\t\t\t\t\tON CONFLICT(id) DO UPDATE SET conversation_id = excluded.conversation_id, kind = excluded.kind,\n\t\t\t\t\t\tstatus = excluded.status, abort_requested = excluded.abort_requested,\n\t\t\t\t\t\tbackground = excluded.background, record = excluded.record";
const UPSERT_SUBMISSION: &str = "INSERT INTO submissions (id, conversation_id, request_id, status, record) VALUES (?, ?, ?, ?, ?)\n\t\t\t\t\t\tON CONFLICT(id) DO UPDATE SET conversation_id = excluded.conversation_id,\n\t\t\t\t\t\trequest_id = excluded.request_id, status = excluded.status, record = excluded.record";
const CLAIM_ID: &str = "INSERT OR IGNORE INTO record_ids (id, record_type) VALUES (?, ?)";
const INSERT_DOCUMENT: &str = "INSERT INTO documents\n\t\t\t\t\t\t(id, kind, family, key_value, scope_kind, owner_id, created_at, retired_at, record)\n\t\t\t\t\t\tVALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)";
const DELETE_REVISIONS: &str = "DELETE FROM document_revisions WHERE document_id = ?";
const INSERT_REVISION: &str = "INSERT INTO document_revisions (document_id, seq, kind, version, content) VALUES (?, ?, ?, ?, ?)";
const RETIRE_DOCUMENT: &str = "UPDATE documents SET retired_at = ?, record = ? WHERE id = ?";

impl From<SqliteError> for StorageError {
    fn from(error: SqliteError) -> Self {
        Self::failed(error)
    }
}

fn parse_json<T: DeserializeOwned>(text: &str) -> Result<T, StorageError> {
    let value = JsonValue::parse(text).map_err(StorageError::failed)?;
    from_json(&value).map_err(StorageError::failed)
}

fn encode_json<T: Serialize + ?Sized>(value: &T) -> Result<String, StorageError> {
    Ok(to_json(value).map_err(StorageError::failed)?.to_string())
}

// Some SQLite bindings replace lone UTF-16 surrogates. JSON encoding keeps indexed identities lossless.
fn encode_indexed_string(value: &str) -> String {
    JsonValue::from(value).to_string()
}

/// Parse the `record` column of a row.
fn row_record<T: DeserializeOwned>(row: &SqliteRow) -> Result<T, StorageError> {
    parse_json(row.text("record")?)
}

fn optional_record<T: DeserializeOwned>(row: Option<SqliteRow>) -> Result<Option<T>, StorageError> {
    row.map(|row| row_record(&row)).transpose()
}

fn records<T: DeserializeOwned>(rows: &[SqliteRow]) -> Result<Vec<T>, StorageError> {
    rows.iter().map(row_record).collect()
}

/// A stored record number (ID, sequence, or version) of an INTEGER column.
fn stored_number(row: &SqliteRow, column: &str) -> Result<u64, StorageError> {
    let value = row.integer(column)?;
    u64::try_from(value).map_err(|_| {
        failure(format!(
            "Durable SQLite column {column} holds a negative number: {value}"
        ))
    })
}

fn stored_entry(row: Option<SqliteRow>) -> Result<Option<StoredEntry>, StorageError> {
    let Some(row) = row else {
        return Ok(None);
    };
    Ok(Some(StoredEntry {
        entry: row_record(&row)?,
        commit_seq: Seq::from_number(stored_number(&row, "commit_seq")?),
    }))
}

/// A JS number for an integral record number.
#[expect(clippy::cast_precision_loss, reason = "JS numbers are doubles")]
fn js_number(value: u64) -> f64 {
    value as f64
}

/// A JS number for a page size.
#[expect(clippy::cast_precision_loss, reason = "JS numbers are doubles")]
fn js_limit(value: usize) -> f64 {
    value as f64
}

/// A JS number for a decoded cursor ID (a safe integer).
#[expect(clippy::cast_precision_loss, reason = "JS numbers are doubles")]
fn js_signed_number(value: i64) -> f64 {
    value as f64
}

/// `Math.max(left, right)`: NaN when either is NaN.
fn js_max(left: f64, right: f64) -> f64 {
    if left.is_nan() || right.is_nan() {
        f64::NAN
    } else {
        left.max(right)
    }
}

/// `Number.isSafeInteger(value)`.
fn is_safe_integer(value: f64) -> bool {
    value.fract() == 0.0 && value.abs() <= MAX_SAFE_INTEGER
}

/// `String(value)` for a JS number.
fn number_text(value: f64) -> String {
    match JsonNumber::new(value) {
        Some(number) => number.to_string(),
        None if value.is_nan() => "NaN".to_owned(),
        None if value > 0.0 => "Infinity".to_owned(),
        None => "-Infinity".to_owned(),
    }
}

/// `Number(text)` (JS `StringToNumber`).
fn text_number(text: &str) -> f64 {
    let text = text.trim_matches(|c: char| c.is_whitespace() || c == '\u{feff}');
    if text.is_empty() {
        return 0.0;
    }
    for (prefix, radix) in [
        ("0x", 16),
        ("0X", 16),
        ("0o", 8),
        ("0O", 8),
        ("0b", 2),
        ("0B", 2),
    ] {
        if let Some(digits) = text.strip_prefix(prefix) {
            if digits.is_empty() {
                return f64::NAN;
            }
            return digits
                .chars()
                .try_fold(0.0, |value: f64, digit| {
                    digit
                        .to_digit(radix)
                        .map(|digit| value * f64::from(radix) + f64::from(digit))
                })
                .unwrap_or(f64::NAN);
        }
    }
    match text {
        "Infinity" | "+Infinity" => return f64::INFINITY,
        "-Infinity" => return f64::NEG_INFINITY,
        _ => {}
    }
    // Rust also accepts `inf`, `infinity`, and `nan`; JS accepts only the decimal grammar.
    if !text
        .chars()
        .all(|c| c.is_ascii_digit() || matches!(c, '+' | '-' | '.' | 'e' | 'E'))
    {
        return f64::NAN;
    }
    text.parse().unwrap_or(f64::NAN)
}

fn task_status_name(status: TaskStatus) -> &'static str {
    match status {
        TaskStatus::Pending => "pending",
        TaskStatus::Running => "running",
        TaskStatus::Waiting => "waiting",
        TaskStatus::Completing => "completing",
        TaskStatus::Terminal => "terminal",
    }
}

fn submission_status_name(status: SubmissionStatus) -> &'static str {
    match status {
        SubmissionStatus::Queued => "queued",
        SubmissionStatus::Placed => "placed",
        SubmissionStatus::Done => "done",
        SubmissionStatus::Unanswered => "unanswered",
    }
}

fn flag(value: bool) -> SqliteValue {
    SqliteValue::Integer(i64::from(value))
}

/// TS `cursorId(cursor) ?? -1`.
fn cursor_param(cursor: Option<&Cursor>) -> Result<SqliteValue, StorageError> {
    Ok(SqliteValue::Integer(cursor_id(cursor)?.unwrap_or(-1)))
}

/// TS `scopeColumns`.
fn scope_columns(scope: DocumentScope) -> (&'static str, u64) {
    match scope {
        DocumentScope::Session => ("session", 0),
        DocumentScope::Conversation { conversation_id } => ("conversation", conversation_id.get()),
        DocumentScope::Task { task_id } => ("task", task_id.get()),
    }
}

/// Indexed columns of a document address (TS `addressParts`).
struct AddressParts {
    kind: String,
    scope_kind: &'static str,
    owner_id: u64,
    family: i64,
    key_value: String,
}

/// Map key of one exact address (TS `addressKey`).
type AddressKey = (String, &'static str, u64, i64, String);

impl AddressParts {
    fn new(kind: &str, scope: DocumentScope, key: Option<&str>) -> Self {
        let (scope_kind, owner_id) = scope_columns(scope);
        Self {
            kind: encode_indexed_string(kind),
            scope_kind,
            owner_id,
            family: i64::from(key.is_some()),
            key_value: encode_indexed_string(key.unwrap_or_default()),
        }
    }

    fn of_address(address: &DocumentAddress) -> Self {
        Self::new(&address.kind, address.scope, address.key.as_deref())
    }

    fn of_identity(identity: &impl DocumentIdentity) -> Self {
        Self::new(
            identity.kind(),
            identity.record_scope().scope(),
            identity.key(),
        )
    }

    fn key(&self) -> AddressKey {
        (
            self.kind.clone(),
            self.scope_kind,
            self.owner_id,
            self.family,
            self.key_value.clone(),
        )
    }

    /// `kind, scope_kind, owner_id, family, key_value` bindings.
    fn params(&self) -> Vec<SqliteValue> {
        vec![
            self.kind.as_str().into(),
            self.scope_kind.into(),
            self.owner_id.into(),
            self.family.into(),
            self.key_value.as_str().into(),
        ]
    }
}

/// Table of a record ID claim (TS `TableName`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TableName {
    Conversation,
    Entry,
    Task,
    Submission,
    Document,
}

impl TableName {
    fn name(self) -> &'static str {
        match self {
            Self::Conversation => "conversation",
            Self::Entry => "entry",
            Self::Task => "task",
            Self::Submission => "submission",
            Self::Document => "document",
        }
    }
}

/// TS `writeId`.
fn write_id(write: &StorageWrite) -> Option<u64> {
    match write {
        StorageWrite::Conversation { value } => Some(value.id.get()),
        StorageWrite::Entry { value } => Some(value.id.get()),
        StorageWrite::Task { value } => Some(value.id.get()),
        StorageWrite::Submission { value } => Some(value.id.get()),
        StorageWrite::DocumentCreate { record, .. } | StorageWrite::DocumentCopy { record, .. } => {
            Some(record.id.get())
        }
        StorageWrite::DocumentChange { .. } | StorageWrite::DocumentRetire { .. } => None,
    }
}

/// How a batch creates an incarnation: from its own base, or as a copy of committed source
/// state (TS `DocumentAction.create` plus `DocumentAction.copy`).
#[derive(Clone, Copy)]
enum Creation<'w> {
    Create(&'w DocumentCreate),
    Copy(&'w DocumentCreate, DocumentCopySource),
}

impl<'w> Creation<'w> {
    fn record(self) -> &'w DocumentCreate {
        match self {
            Self::Create(record) | Self::Copy(record, _) => record,
        }
    }
}

/// The content commands of one incarnation in a batch (TS `DocumentAction`).
#[derive(Default)]
struct DocumentAction<'w> {
    create: Option<Creation<'w>>,
    content: Option<DocumentContent>,
    retire: bool,
}

impl DocumentAction<'_> {
    fn copy(&self) -> Option<DocumentCopySource> {
        match self.create {
            Some(Creation::Copy(_, source)) => Some(source),
            Some(Creation::Create(_)) | None => None,
        }
    }
}

/// Document actions in first-write order (TS `Map<DocumentId, DocumentAction>`).
#[derive(Default)]
struct DocumentActions<'w> {
    actions: Vec<(DocumentId, DocumentAction<'w>)>,
    index: HashMap<DocumentId, usize>,
}

impl<'w> DocumentActions<'w> {
    fn has(&self, id: DocumentId) -> bool {
        self.index.contains_key(&id)
    }

    fn action(&mut self, id: DocumentId) -> &mut DocumentAction<'w> {
        let index = *self.index.entry(id).or_insert_with(|| {
            self.actions.push((id, DocumentAction::default()));
            self.actions.len() - 1
        });
        &mut self.actions[index].1
    }

    fn iter(&self) -> impl Iterator<Item = (DocumentId, &DocumentAction<'w>)> {
        self.actions.iter().map(|(id, action)| (*id, action))
    }
}

fn more_than_one_content(id: DocumentId) -> StorageError {
    failure(format!("Document {id} has more than one content command"))
}

/// TS `prepareDocumentActions`.
fn prepare_document_actions(writes: &[StorageWrite]) -> Result<DocumentActions<'_>, StorageError> {
    let mut actions = DocumentActions::default();
    for write in writes {
        match write {
            StorageWrite::DocumentCreate { record, content } => {
                let action = actions.action(record.id);
                if action.create.is_some() || action.content.is_some() {
                    return Err(more_than_one_content(record.id));
                }
                action.create = Some(Creation::Create(record));
                action.content = Some(DocumentContent::Base(content.clone()));
            }
            StorageWrite::DocumentCopy { record, source } => {
                let action = actions.action(record.id);
                if action.create.is_some() || action.content.is_some() {
                    return Err(more_than_one_content(record.id));
                }
                action.create = Some(Creation::Copy(record, *source));
            }
            StorageWrite::DocumentChange { id, content } => {
                let action = actions.action(*id);
                if action.content.is_some() || action.copy().is_some() {
                    return Err(more_than_one_content(*id));
                }
                action.content = Some(content.clone());
            }
            StorageWrite::DocumentRetire { id } => {
                let action = actions.action(*id);
                if action.retire {
                    return Err(failure(format!("Document {id} is retired more than once")));
                }
                action.retire = true;
            }
            StorageWrite::Conversation { .. }
            | StorageWrite::Entry { .. }
            | StorageWrite::Task { .. }
            | StorageWrite::Submission { .. } => {}
        }
    }
    Ok(actions)
}

/// TS `checkGlobalIds`.
async fn check_global_ids(
    executor: &dyn SqliteExecutor,
    writes: &[StorageWrite],
) -> Result<(), StorageError> {
    let mut claimed: HashMap<u64, TableName> = HashMap::new();
    for write in writes {
        let (table, id) = match write {
            StorageWrite::Conversation { value } => (TableName::Conversation, value.id.get()),
            StorageWrite::Entry { value } => (TableName::Entry, value.id.get()),
            StorageWrite::Task { value } => (TableName::Task, value.id.get()),
            StorageWrite::Submission { value } => (TableName::Submission, value.id.get()),
            StorageWrite::DocumentCreate { record, .. }
            | StorageWrite::DocumentCopy { record, .. } => (TableName::Document, record.id.get()),
            StorageWrite::DocumentChange { .. } | StorageWrite::DocumentRetire { .. } => continue,
        };
        let existing = executor
            .get(SELECT_RECORD_TYPE.into(), vec![id.into()])
            .await?
            .map(|row| row.text("record_type").map(str::to_owned))
            .transpose()?;
        let earlier = claimed.get(&id).copied();
        match table {
            TableName::Conversation | TableName::Entry | TableName::Document => {
                if let Some(existing) = existing {
                    return Err(failure(format!("ID {id} already belongs to {existing}")));
                }
                if earlier.is_some() {
                    return Err(failure(format!("ID {id} is written more than once")));
                }
            }
            TableName::Task | TableName::Submission => {
                if let Some(existing) = existing.filter(|existing| existing != table.name()) {
                    return Err(failure(format!("ID {id} already belongs to {existing}")));
                }
                if earlier.is_some_and(|earlier| earlier != table) {
                    return Err(failure(format!("ID {id} is written as two record types")));
                }
            }
        }
        claimed.insert(id, table);
    }
    Ok(())
}

async fn read_document(
    executor: &dyn SqliteExecutor,
    id: DocumentId,
) -> Result<Option<DocumentRecord>, StorageError> {
    optional_record(
        executor
            .get(SELECT_DOCUMENT.into(), vec![id.get().into()])
            .await?,
    )
}

/// TS `currentDocumentId`.
async fn current_document_id(
    executor: &dyn SqliteExecutor,
    parts: &AddressParts,
) -> Result<Option<DocumentId>, StorageError> {
    executor
        .get(SELECT_CURRENT_DOCUMENT_ID.into(), parts.params())
        .await?
        .map(|row| stored_number(&row, "id").map(DocumentId::from_number))
        .transpose()
}

/// TS `checkDocumentActions`.
async fn check_document_actions(
    executor: &dyn SqliteExecutor,
    actions: &DocumentActions<'_>,
) -> Result<(), StorageError> {
    let mut live_counts: HashMap<AddressKey, i64> = HashMap::new();
    for (id, action) in actions.iter() {
        if action.copy().is_some_and(|copy| actions.has(copy.id)) {
            return Err(StorageRejected::new(format!(
                "Document copy {id} source is changed in the copy batch"
            ))
            .into());
        }
        let existing = read_document(executor, id).await?;
        let create = action.create.map(Creation::record);
        if create.is_none() && existing.is_none() {
            return Err(failure(format!("Unknown document: {id}")));
        }
        if create.is_some() && existing.is_some() {
            return Err(failure(format!("Document {id} already exists")));
        }
        if existing
            .as_ref()
            .is_some_and(|existing| existing.retired_at.is_some())
        {
            return Err(failure(format!("Document {id} is retired")));
        }
        if let Some(DocumentContent::Delta(delta)) = &action.content {
            let Some(previous) = executor
                .get(SELECT_LAST_VERSION.into(), vec![id.get().into()])
                .await?
            else {
                return Err(failure(format!("Document {id} delta has no base")));
            };
            if stored_number(&previous, "version")? != delta.version {
                return Err(failure(format!(
                    "Document {id} version transition requires a base"
                )));
            }
        }
        let parts = match (create, &existing) {
            (Some(create), _) => AddressParts::of_identity(create),
            (None, Some(existing)) => AddressParts::of_identity(existing),
            (None, None) => return Err(failure(format!("Unknown document: {id}"))),
        };
        let key = parts.key();
        let mut live = match live_counts.get(&key) {
            Some(live) => *live,
            None => i64::from(current_document_id(executor, &parts).await?.is_some()),
        };
        if action.retire && existing.is_some() {
            live -= 1;
        }
        if create.is_some() && !action.retire {
            live += 1;
        }
        live_counts.insert(key, live);
    }
    if live_counts.values().any(|live| *live > 1) {
        return Err(failure(
            "Document address already has a current incarnation",
        ));
    }
    Ok(())
}

async fn claim_id(
    executor: &dyn SqliteExecutor,
    id: u64,
    table: TableName,
) -> Result<(), StorageError> {
    executor
        .run(CLAIM_ID.into(), vec![id.into(), table.name().into()])
        .await?;
    Ok(())
}

/// TS `applyTableWrite`.
async fn apply_table_write(
    executor: &dyn SqliteExecutor,
    write: &StorageWrite,
    seq: Seq,
) -> Result<(), StorageError> {
    match write {
        StorageWrite::Conversation { value } => {
            claim_id(executor, value.id.get(), TableName::Conversation).await?;
            let params = vec![
                value.id.get().into(),
                value.owner.map(|owner| owner.conversation_id.get()).into(),
                value.owner.map(|owner| owner.task_id.get()).into(),
                encode_json(value)?.into(),
            ];
            executor.run(INSERT_CONVERSATION.into(), params).await?;
        }
        StorageWrite::Entry { value } => {
            claim_id(executor, value.id.get(), TableName::Entry).await?;
            let params = vec![
                value.id.get().into(),
                value.conversation_id.get().into(),
                value.head.map(EntryId::get).into(),
                seq.get().into(),
                encode_json(value)?.into(),
            ];
            executor.run(INSERT_ENTRY.into(), params).await?;
        }
        StorageWrite::Task { value } => {
            claim_id(executor, value.id.get(), TableName::Task).await?;
            let params = vec![
                value.id.get().into(),
                value.conversation_id.get().into(),
                encode_indexed_string(&value.kind).into(),
                task_status_name(value.state.status()).into(),
                flag(value.abort_requested),
                flag(value.background),
                encode_json(value)?.into(),
            ];
            executor.run(UPSERT_TASK.into(), params).await?;
        }
        StorageWrite::Submission { value } => {
            claim_id(executor, value.id.get(), TableName::Submission).await?;
            let params = vec![
                value.id.get().into(),
                value.conversation_id.get().into(),
                value
                    .request_id
                    .as_deref()
                    .map(encode_indexed_string)
                    .into(),
                submission_status_name(value.state.status()).into(),
                encode_json(value)?.into(),
            ];
            executor.run(UPSERT_SUBMISSION.into(), params).await?;
        }
        StorageWrite::DocumentCreate { .. }
        | StorageWrite::DocumentCopy { .. }
        | StorageWrite::DocumentChange { .. }
        | StorageWrite::DocumentRetire { .. } => {}
    }
    Ok(())
}

/// TS `materializeDocument`.
async fn materialize_document(
    executor: &dyn SqliteExecutor,
    id: DocumentId,
    at: DocumentPoint,
) -> Result<Option<StoredDocument>, StorageError> {
    let Some(record) = read_document(executor, id).await? else {
        return Ok(None);
    };
    if at != DocumentPoint::Current && is_current_only(record.scope) {
        return Err(failure(format!(
            "Document {id} does not retain historical content"
        )));
    }
    if !is_alive_at(&record, at) {
        return Ok(None);
    }
    let upper = match at {
        DocumentPoint::Current => SqliteValue::Real(MAX_SAFE_INTEGER),
        DocumentPoint::At(seq) => seq.get().into(),
    };
    let Some(base) = executor
        .get(SELECT_BASE.into(), vec![id.get().into(), upper.clone()])
        .await?
    else {
        return Err(failure(format!("Document {id} is missing a required base")));
    };
    let base_version = stored_number(&base, "version")?;
    let mut value = JsonValue::parse(base.text("content")?).map_err(StorageError::failed)?;
    let tail = executor
        .all(
            SELECT_TAIL.into(),
            vec![id.get().into(), stored_number(&base, "seq")?.into(), upper],
        )
        .await?;
    for revision in &tail {
        if revision.text("kind")? != "delta" || stored_number(revision, "version")? != base_version
        {
            return Err(failure(format!(
                "Document {id} crosses a stored version boundary without a base"
            )));
        }
        let ops = stored_ops(revision.text("content")?)?;
        value = apply(value, &ops).map_err(StorageError::failed)?;
    }
    let JsonValue::Object(value) = value else {
        return Err(failure(format!(
            "Document {id} materialized to a value that is not an object"
        )));
    };
    Ok(Some(StoredDocument {
        record,
        version: base_version,
        value,
        deltas_since_base: tail.len() as u64,
    }))
}

/// Decode a stored delta batch the way TS `apply` iterates and validates it.
fn stored_ops(content: &str) -> Result<Vec<Op>, StorageError> {
    let ops = JsonValue::parse(content).map_err(StorageError::failed)?;
    match &ops {
        JsonValue::Array(items) => items
            .iter()
            .map(|op| Op::from_json(op).map_err(StorageError::failed))
            .collect(),
        // A string iterates its characters, none of which is an op tuple.
        JsonValue::String(text) if text.is_empty() => Ok(Vec::new()),
        JsonValue::String(_) => Err(StorageError::failed(DeltaError::Type("op is not a tuple"))),
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::Object(_) => Err(
            StorageError::failed(DeltaError::Type("ops is not iterable")),
        ),
    }
}

/// Read a document-copy source and build the child's base (the `try` block of TS
/// `applyDocumentActions`).
async fn copied_content(
    executor: &dyn SqliteExecutor,
    create: &DocumentCreate,
    source: DocumentCopySource,
) -> Result<DocumentContent, StorageError> {
    let Some(stored) = materialize_document(executor, source.id, source.at).await? else {
        return Err(failure(format!(
            "Fork source document {} cannot be read",
            source.id
        )));
    };
    let matches = matches!(
        stored.record.scope.scope(),
        DocumentScope::Conversation { .. }
    ) && matches!(create.scope.scope(), DocumentScope::Conversation { .. })
        && stored.record.kind == create.kind
        && stored.record.key == create.key
        && stored.record.scope.history() == create.scope.history()
        && stored.record.scope.fork() == create.scope.fork();
    if !matches {
        return Err(failure(format!(
            "Fork source document {} does not match the copied record",
            source.id
        )));
    }
    Ok(DocumentContent::Base(DocumentBase {
        version: stored.version,
        value: stored.value,
    }))
}

/// TS `applyDocumentActions`.
async fn apply_document_actions(
    executor: &dyn SqliteExecutor,
    actions: &DocumentActions<'_>,
    seq: Seq,
) -> Result<(), StorageError> {
    for (id, action) in actions.iter() {
        let mut content = action.content.clone();
        if let Some(Creation::Copy(create, source)) = action.create {
            content = Some(
                copied_content(executor, create, source)
                    .await
                    .map_err(|error| rejected(format!("Document copy {id} was rejected"), error))?,
            );
        }
        let mut record = if let Some(creation) = action.create {
            let record = DocumentRecord {
                retired_at: action.retire.then_some(seq),
                ..DocumentRecord::from_create(creation.record().clone(), seq)
            };
            let parts = AddressParts::of_identity(&record);
            claim_id(executor, id.get(), TableName::Document).await?;
            let params = vec![
                id.get().into(),
                parts.kind.into(),
                parts.family.into(),
                parts.key_value.into(),
                parts.scope_kind.into(),
                parts.owner_id.into(),
                seq.get().into(),
                action.retire.then(|| seq.get()).into(),
                encode_json(&record)?.into(),
            ];
            executor.run(INSERT_DOCUMENT.into(), params).await?;
            record
        } else {
            read_document(executor, id)
                .await?
                .ok_or_else(|| failure(format!("Unknown document: {id}")))?
        };

        if let Some(content) = content {
            if matches!(content, DocumentContent::Base(_)) && is_current_only(record.scope) {
                executor
                    .run(DELETE_REVISIONS.into(), vec![id.get().into()])
                    .await?;
            }
            let (kind, encoded) = match &content {
                DocumentContent::Base(base) => (
                    "base",
                    JsonValue::Object(Arc::clone(&base.value)).to_string(),
                ),
                DocumentContent::Delta(delta) => ("delta", encode_json(&*delta.ops)?),
            };
            executor
                .run(
                    INSERT_REVISION.into(),
                    vec![
                        id.get().into(),
                        seq.get().into(),
                        kind.into(),
                        content.version().into(),
                        encoded.into(),
                    ],
                )
                .await?;
        }

        if action.retire {
            if action.create.is_none() {
                record = DocumentRecord {
                    retired_at: Some(seq),
                    ..record
                };
                executor
                    .run(
                        RETIRE_DOCUMENT.into(),
                        vec![
                            seq.get().into(),
                            encode_json(&record)?.into(),
                            id.get().into(),
                        ],
                    )
                    .await?;
            }
            if is_current_only(record.scope) {
                executor
                    .run(DELETE_REVISIONS.into(), vec![id.get().into()])
                    .await?;
            }
        }
    }
    Ok(())
}

type DatabaseClose = BoxFuture<'static, Result<(), SqliteError>>;
type Closing = Shared<BoxFuture<'static, Result<(), StorageError>>>;

struct State {
    /// TS `nextId`: a JS number, so exhaustion past `Number.MAX_SAFE_INTEGER` is observable.
    next_id: f64,
    closed: bool,
    closing: Option<Closing>,
    admitted_reads: usize,
    /// Resolved by the last admitted read with the database close it started.
    reads_drained: Option<oneshot::Sender<DatabaseClose>>,
}

/// Portable SQLite implementation of the durable storage contract.
pub struct SqliteStorage {
    db: Arc<dyn SqliteDatabase>,
    state: Mutex<State>,
}

impl std::fmt::Debug for SqliteStorage {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("SqliteStorage")
            .finish_non_exhaustive()
    }
}

/// An admitted multi-query read; close waits until every one is dropped.
struct ReadGuard<'a> {
    storage: &'a SqliteStorage,
}

impl Drop for ReadGuard<'_> {
    fn drop(&mut self) {
        let mut state = self.storage.lock();
        state.admitted_reads -= 1;
        if state.admitted_reads == 0 {
            if let Some(drained) = state.reads_drained.take() {
                // The close future only goes unreceived when the storage is being dropped.
                drop(drained.send(self.storage.db.close()));
            }
        }
    }
}

fn failed_now<'a, T: Send + 'a>(error: StorageError) -> BoxFuture<'a, Result<T, StorageError>> {
    Box::pin(future::ready(Err(error)))
}

impl SqliteStorage {
    /// Initialize storage over an owned SQLite database facade. On failure the database is
    /// closed (its close failure is dropped to preserve the initialization failure).
    ///
    /// # Errors
    /// A migration fails or the durable metadata is missing.
    pub async fn open(db: impl SqliteDatabase + 'static) -> Result<Self, StorageError> {
        let db: Arc<dyn SqliteDatabase> = Arc::new(db);
        let initialized = async {
            apply_sqlite_migrations(&*db, SQLITE_MIGRATIONS)
                .await
                .map_err(StorageError::failed)?;
            let metadata = db
                .get(SELECT_METADATA.into(), Vec::new())
                .await?
                .ok_or_else(|| failure("Durable SQLite metadata is missing"))?;
            Ok::<_, StorageError>(text_number(metadata.text("next_id")?))
        }
        .await;
        match initialized {
            Ok(next_id) => Ok(Self {
                db,
                state: Mutex::new(State {
                    next_id,
                    closed: false,
                    closing: None,
                    admitted_reads: 0,
                    reads_drained: None,
                }),
            }),
            Err(error) => {
                // Preserve the initialization failure.
                drop(db.close().await);
                Err(error)
            }
        }
    }

    fn lock(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn assert_open(&self) -> Result<(), StorageError> {
        if self.lock().closed {
            return Err(failure("SqliteStorage is closed"));
        }
        Ok(())
    }

    /// Admit a read that issues several queries. Close waits for admitted reads, so their
    /// later queries never reach a closed database. Single-query reads and transactions are
    /// already ordered before close by the database.
    fn admit_read(&self) -> Result<ReadGuard<'_>, StorageError> {
        let mut state = self.lock();
        if state.closed {
            return Err(failure("SqliteStorage is closed"));
        }
        state.admitted_reads += 1;
        Ok(ReadGuard { storage: self })
    }

    fn candidate_next_id(&self, writes: &[StorageWrite]) -> f64 {
        writes
            .iter()
            .filter_map(write_id)
            .fold(self.lock().next_id, |next_id, id| {
                js_max(next_id, js_number(id) + 1.0)
            })
    }

    /// Start reading a conversation; the query is queued now.
    fn read_conversation(
        &self,
        id: ConversationId,
    ) -> BoxFuture<'static, Result<Option<ConversationRecord>, StorageError>> {
        let row = self
            .db
            .get(SELECT_CONVERSATION.into(), vec![id.get().into()]);
        Box::pin(async move { optional_record(row.await?) })
    }

    /// Read a conversation an existing record references (TS non-null `readConversation`).
    async fn read_ancestor(&self, id: ConversationId) -> Result<ConversationRecord, StorageError> {
        self.read_conversation(id)
            .await?
            .ok_or_else(|| unknown_conversation(id))
    }

    async fn read_entry_in(
        &self,
        conversation: BoxFuture<'static, Result<Option<ConversationRecord>, StorageError>>,
        conversation_id: ConversationId,
        id: EntryId,
    ) -> Result<Option<StoredEntry>, StorageError> {
        let mut conversation = conversation
            .await?
            .ok_or_else(|| unknown_conversation(conversation_id))?;
        let row = self
            .db
            .get(SELECT_ENTRY.into(), vec![id.get().into()])
            .await?;
        let Some(stored) = stored_entry(row)? else {
            return Ok(None);
        };
        let mut upper_entry_id = f64::INFINITY;
        while conversation.id != stored.entry.conversation_id {
            let Some(parent) = conversation.parent else {
                return Ok(None);
            };
            upper_entry_id = upper_entry_id.min(js_number(parent.at.get()));
            conversation = self.read_ancestor(parent.conversation_id).await?;
        }
        if js_number(stored.entry.id.get()) > upper_entry_id {
            return Ok(None);
        }
        Ok(Some(stored))
    }

    async fn read_latest_head_marker(
        &self,
        conversation: BoxFuture<'static, Result<Option<ConversationRecord>, StorageError>>,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
    ) -> Result<Option<EntryRecord>, StorageError> {
        let mut conversation = conversation
            .await?
            .ok_or_else(|| unknown_conversation(conversation_id))?;
        let mut upper = at_or_before_entry_id.map(|id| js_number(id.get()));
        loop {
            let row = match upper {
                None => {
                    self.db
                        .get(
                            SELECT_LATEST_HEAD.into(),
                            vec![conversation.id.get().into()],
                        )
                        .await?
                }
                Some(upper) => {
                    self.db
                        .get(
                            SELECT_LATEST_HEAD_UPTO.into(),
                            vec![conversation.id.get().into(), upper.into()],
                        )
                        .await?
                }
            };
            if let Some(row) = row {
                return row_record(&row).map(Some);
            }
            let Some(parent) = conversation.parent else {
                return Ok(None);
            };
            let at = js_number(parent.at.get());
            upper = Some(upper.map_or(at, |upper| upper.min(at)));
            conversation = self.read_ancestor(parent.conversation_id).await?;
        }
    }

    async fn read_entries(
        &self,
        conversation: BoxFuture<'static, Result<Option<ConversationRecord>, StorageError>>,
        query: &EntryQuery,
        limit: usize,
        cursor: Option<&Cursor>,
    ) -> Result<Page<EntryRecord>, StorageError> {
        let mut conversation = conversation
            .await?
            .ok_or_else(|| unknown_conversation(query.conversation_id))?;
        let after = cursor_id(cursor)?;
        let mut upper = query.max_entry_id.map(|id| js_number(id.get()));
        if let Some(after) = after {
            upper = Some(
                upper
                    .unwrap_or(MAX_SAFE_INTEGER)
                    .min(js_signed_number(after) - 1.0),
            );
        }
        let min_entry_id = query.min_entry_id.map(|id| js_number(id.get()));
        let mut values: Vec<EntryRecord> = Vec::new();
        loop {
            let mut clauses = vec!["conversation_id = ?"];
            let mut params: Vec<SqliteValue> = vec![conversation.id.get().into()];
            if let Some(min_entry_id) = min_entry_id {
                clauses.push("id >= ?");
                params.push(min_entry_id.into());
            }
            if let Some(upper) = upper {
                clauses.push("id <= ?");
                params.push(upper.into());
            }
            params.push((js_limit(limit) + 1.0 - js_limit(values.len())).into());
            let rows = self
                .db
                .all(
                    format!(
                        "SELECT record FROM entries WHERE {} ORDER BY id DESC LIMIT ?",
                        clauses.join(" AND ")
                    )
                    .into(),
                    params,
                )
                .await?;
            values.extend(records::<EntryRecord>(&rows)?);
            let Some(parent) = conversation.parent.filter(|_| values.len() <= limit) else {
                break;
            };
            let at = js_number(parent.at.get());
            let next_upper = upper.map_or(at, |upper| upper.min(at));
            upper = Some(next_upper);
            if min_entry_id.is_some_and(|min_entry_id| next_upper < min_entry_id) {
                break;
            }
            conversation = self.read_ancestor(parent.conversation_id).await?;
        }
        Ok(page(values, limit))
    }

    /// Queue a scan of `table` over `clauses` (TS `SELECT record FROM … ORDER BY id LIMIT ?`).
    fn scan<'a, T: DeserializeOwned + Send + 'a>(
        &self,
        table: &str,
        clauses: &[&str],
        mut params: Vec<SqliteValue>,
        limit: usize,
    ) -> BoxFuture<'a, Result<Vec<T>, StorageError>> {
        params.push((js_limit(limit) + 1.0).into());
        let rows = self.db.all(
            Cow::Owned(format!(
                "SELECT record FROM {table} WHERE {} ORDER BY id LIMIT ?",
                clauses.join(" AND ")
            )),
            params,
        );
        Box::pin(async move { records(&rows.await?) })
    }
}

fn unknown_conversation(id: ConversationId) -> StorageError {
    failure(format!("Unknown conversation: {id}"))
}

impl Storage for SqliteStorage {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        let actions = match prepare_document_actions(writes) {
            Ok(actions) => actions,
            Err(error) => return failed_now(error),
        };
        let candidate_next_id = self.candidate_next_id(writes);
        let committed = self
            .db
            .transaction(move |transaction: SqliteTransaction| async move {
                let metadata = transaction
                    .get(SELECT_METADATA.into(), Vec::new())
                    .await?
                    .ok_or_else(|| failure("Durable SQLite metadata is missing"))?;
                let committed_seq = Seq::from_number(stored_number(&metadata, "next_seq")?);
                check_global_ids(&*transaction, writes).await?;
                check_document_actions(&*transaction, &actions).await?;
                for write in writes {
                    apply_table_write(&*transaction, write, committed_seq).await?;
                }
                apply_document_actions(&*transaction, &actions, committed_seq).await?;
                let next_id = js_max(text_number(metadata.text("next_id")?), candidate_next_id);
                transaction
                    .run(
                        UPDATE_METADATA.into(),
                        vec![
                            number_text(next_id).into(),
                            (committed_seq.get() + 1).into(),
                        ],
                    )
                    .await?;
                Ok::<_, StorageError>(committed_seq)
            });
        Box::pin(async move {
            let seq = committed.await?;
            let mut state = self.lock();
            state.next_id = js_max(state.next_id, candidate_next_id);
            Ok(seq)
        })
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        let minted = (|| {
            let mut state = self.lock();
            if state.closed {
                return Err(failure("SqliteStorage is closed"));
            }
            if !is_safe_integer(state.next_id) {
                return Err(failure("ID space is exhausted"));
            }
            // A safe integer, checked above.
            #[expect(
                clippy::cast_possible_truncation,
                clippy::cast_sign_loss,
                reason = "checked safe integer"
            )]
            let id = state.next_id as u64;
            state.next_id += 1.0;
            Ok(id)
        })();
        Box::pin(future::ready(minted))
    }

    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        self.read_conversation(id)
    }

    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        let mut clauses = vec!["id > ?"];
        let mut params = match cursor_param(cursor) {
            Ok(after) => vec![after],
            Err(error) => return failed_now(error),
        };
        if let Some(owner) = query.owner_conversation_id {
            clauses.push("owner_conversation_id = ?");
            params.push(owner.get().into());
        }
        if let Some(owner) = query.owner_task_id {
            clauses.push("owner_task_id = ?");
            params.push(owner.get().into());
        }
        let scanned = self.scan("conversations", &clauses, params, limit);
        Box::pin(async move { Ok(page(scanned.await?, limit)) })
    }

    fn entry<'a>(
        &'a self,
        id: EntryId,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        let guard = match self.admit_read() {
            Ok(guard) => guard,
            Err(error) => return failed_now(error),
        };
        let row = self.db.get(SELECT_ENTRY.into(), vec![id.get().into()]);
        Box::pin(async move {
            let _guard = guard;
            stored_entry(row.await?)
        })
    }

    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        let guard = match self.admit_read() {
            Ok(guard) => guard,
            Err(error) => return failed_now(error),
        };
        let conversation = self.read_conversation(conversation_id);
        Box::pin(async move {
            let _guard = guard;
            self.read_entry_in(conversation, conversation_id, id).await
        })
    }

    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>> {
        let guard = match self.admit_read() {
            Ok(guard) => guard,
            Err(error) => return failed_now(error),
        };
        let conversation = self.read_conversation(conversation_id);
        Box::pin(async move {
            let _guard = guard;
            self.read_latest_head_marker(conversation, conversation_id, at_or_before_entry_id)
                .await
        })
    }

    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>> {
        let guard = match self.admit_read() {
            Ok(guard) => guard,
            Err(error) => return failed_now(error),
        };
        let conversation = self.read_conversation(query.conversation_id);
        Box::pin(async move {
            let _guard = guard;
            self.read_entries(conversation, query, limit, cursor).await
        })
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        let row = self.db.get(SELECT_TASK.into(), vec![id.get().into()]);
        Box::pin(async move { optional_record(row.await?) })
    }

    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        let mut clauses = vec!["id > ?"];
        let mut params = match cursor_param(cursor) {
            Ok(after) => vec![after],
            Err(error) => return failed_now(error),
        };
        if let Some(conversation_id) = query.conversation_id {
            clauses.push("conversation_id = ?");
            params.push(conversation_id.get().into());
        }
        if let Some(kind) = &query.kind {
            clauses.push("kind = ?");
            params.push(encode_indexed_string(kind).into());
        }
        if let Some(status) = query.status {
            clauses.push("status = ?");
            params.push(task_status_name(status).into());
        }
        if let Some(abort_requested) = query.abort_requested {
            clauses.push("abort_requested = ?");
            params.push(flag(abort_requested));
        }
        if let Some(background) = query.background {
            clauses.push("background = ?");
            params.push(flag(background));
        }
        let scanned = self.scan("tasks", &clauses, params, limit);
        Box::pin(async move { Ok(page(scanned.await?, limit)) })
    }

    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        let row = self.db.get(SELECT_SUBMISSION.into(), vec![id.get().into()]);
        Box::pin(async move { optional_record(row.await?) })
    }

    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        let mut clauses = vec!["id > ?"];
        let mut params = match cursor_param(cursor) {
            Ok(after) => vec![after],
            Err(error) => return failed_now(error),
        };
        if let Some(conversation_id) = query.conversation_id {
            clauses.push("conversation_id = ?");
            params.push(conversation_id.get().into());
        }
        if let Some(status) = query.status {
            clauses.push("status = ?");
            params.push(submission_status_name(status).into());
        }
        let scanned = self.scan("submissions", &clauses, params, limit);
        Box::pin(async move { Ok(page(scanned.await?, limit)) })
    }

    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        let row = self.db.get(
            SELECT_SUBMISSION_BY_REQUEST.into(),
            vec![
                conversation_id.get().into(),
                encode_indexed_string(request_id).into(),
            ],
        );
        Box::pin(async move { optional_record(row.await?) })
    }

    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        let mut params = AddressParts::of_address(address).params();
        let sql = match at {
            DocumentPoint::Current => FIND_CURRENT_DOCUMENT,
            DocumentPoint::At(seq) => {
                params.push(seq.get().into());
                params.push(seq.get().into());
                FIND_DOCUMENT_AT
            }
        };
        let row = self.db.get(sql.into(), params);
        Box::pin(async move { optional_record(row.await?) })
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        // The record and revision queries must observe one committed state; a commit between
        // them can replace the base.
        self.db
            .transaction(move |transaction: SqliteTransaction| async move {
                materialize_document(&*transaction, id, at).await
            })
    }

    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>> {
        if let Err(error) = self.assert_open() {
            return failed_now(error);
        }
        let (scope_kind, owner_id) = scope_columns(query.scope);
        let mut clauses = vec!["scope_kind = ?", "owner_id = ?", "id > ?"];
        let mut params = match cursor_param(cursor) {
            Ok(after) => vec![scope_kind.into(), owner_id.into(), after],
            Err(error) => return failed_now(error),
        };
        if let Some(kind) = &query.kind {
            clauses.push("kind = ?");
            params.push(encode_indexed_string(kind).into());
        }
        match query.at {
            DocumentPoint::Current => clauses.push("retired_at IS NULL"),
            DocumentPoint::At(at) => {
                clauses.push("created_at <= ?");
                clauses.push("(retired_at IS NULL OR retired_at > ?)");
                params.push(at.get().into());
                params.push(at.get().into());
            }
        }
        let scanned = self.scan("documents", &clauses, params, limit);
        Box::pin(async move { Ok(page(scanned.await?, limit)) })
    }

    fn close<'a>(&'a self, _cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        let mut state = self.lock();
        let closing = if let Some(closing) = &state.closing {
            closing.clone()
        } else {
            state.closed = true;
            let closing: BoxFuture<'static, Result<(), StorageError>> = if state.admitted_reads > 0
            {
                let (drained, close) = oneshot::channel::<DatabaseClose>();
                state.reads_drained = Some(drained);
                let db = Arc::clone(&self.db);
                Box::pin(async move {
                    let close = close.await.unwrap_or_else(|oneshot::Canceled| db.close());
                    Ok(close.await?)
                })
            } else {
                let close = self.db.close();
                Box::pin(async move { Ok(close.await?) })
            };
            let closing = closing.shared();
            state.closing = Some(closing.clone());
            closing
        };
        drop(state);
        Box::pin(closing)
    }
}
