//! Detached in-memory reference implementation of [`Storage`] (`storage/memory.ts`).

use std::collections::{BTreeSet, HashMap};
use std::ops::Bound;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::delta::{try_apply_immutable_batches, BatchError, Op};
use eukhe_chord::json::{JsonValue, MAX_SAFE_INTEGER};
use futures::future::BoxFuture;

use super::common::{cursor_id, failure, failure_with_cause, is_alive_at, is_current_only, page};
use super::scan::{scan_start, ScanStart};
use crate::errors::StorageError;
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationQuery, ConversationRecord, Cursor, DocumentAddress,
    DocumentBase, DocumentContent, DocumentCreate, DocumentId, DocumentPoint, DocumentQuery,
    DocumentRecord, DocumentScope, EntryId, EntryQuery, EntryRecord, Page, ScanOrder, Seq, Storage,
    StorageWrite, StoredDocument, StoredEntry, SubmissionId, SubmissionQuery, SubmissionRecord,
    SubmissionStatus, TaskId, TaskQuery, TaskStatus,
};

/// Record table an ID belongs to; the name is part of error messages.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TableName {
    Conversation,
    Entry,
    Task,
    Submission,
    Document,
}

impl TableName {
    fn as_str(self) -> &'static str {
        match self {
            Self::Conversation => "conversation",
            Self::Entry => "entry",
            Self::Task => "task",
            Self::Submission => "submission",
            Self::Document => "document",
        }
    }
}

/// One stored content revision and the commit that wrote it.
#[derive(Clone, Debug)]
struct DocumentRevision {
    content: DocumentContent,
    seq: Seq,
}

#[derive(Clone, Debug)]
struct StoredDocumentState {
    record: DocumentRecord,
    revisions: Vec<DocumentRevision>,
}

/// The commands one batch issues for one document.
#[derive(Clone, Debug)]
struct DocumentAction {
    create: Option<DocumentCreate>,
    content: Option<DocumentContent>,
    retire: bool,
}

/// Exact scope identity (TS `scopeKey`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ScopeKey {
    Session,
    Conversation(u64),
    Task(u64),
}

impl ScopeKey {
    fn of(scope: DocumentScope) -> Self {
        match scope {
            DocumentScope::Session => Self::Session,
            DocumentScope::Conversation { conversation_id } => {
                Self::Conversation(conversation_id.get())
            }
            DocumentScope::Task { task_id } => Self::Task(task_id.get()),
        }
    }
}

/// Exact logical address identity (TS `addressKey`): kind, scope, and
/// singleton (`None`) or family member key.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct AddressKey {
    kind: String,
    scope: ScopeKey,
    key: Option<String>,
}

impl AddressKey {
    fn of(address: &DocumentAddress) -> Self {
        Self {
            kind: address.kind.clone(),
            scope: ScopeKey::of(address.scope),
            key: address.key.clone(),
        }
    }

    fn of_create(record: &DocumentCreate) -> Self {
        Self {
            kind: record.kind.clone(),
            scope: ScopeKey::of(record.scope.scope()),
            key: record.key.clone(),
        }
    }

    fn of_record(record: &DocumentRecord) -> Self {
        Self {
            kind: record.kind.clone(),
            scope: ScopeKey::of(record.scope.scope()),
            key: record.key.clone(),
        }
    }
}

#[derive(Clone, Debug, Default)]
struct DocumentAddressIndex {
    ids: BTreeSet<u64>,
    current_id: Option<u64>,
}

const TASK_STATUSES: usize = 5;
const SUBMISSION_STATUSES: usize = 4;

fn task_status_index(status: TaskStatus) -> usize {
    match status {
        TaskStatus::Pending => 0,
        TaskStatus::Running => 1,
        TaskStatus::Waiting => 2,
        TaskStatus::Completing => 3,
        TaskStatus::Terminal => 4,
    }
}

fn submission_status_index(status: SubmissionStatus) -> usize {
    match status {
        SubmissionStatus::Queued => 0,
        SubmissionStatus::Placed => 1,
        SubmissionStatus::Done => 2,
        SubmissionStatus::Unanswered => 3,
    }
}

/// Sorted ID sets stand in for the TS sorted arrays with binary search.
#[derive(Debug, Default)]
struct State {
    record_types: HashMap<u64, TableName>,
    conversations: HashMap<u64, ConversationRecord>,
    conversation_ids: BTreeSet<u64>,
    conversation_ids_by_owner_conversation: HashMap<u64, BTreeSet<u64>>,
    conversation_ids_by_owner_task: HashMap<u64, BTreeSet<u64>>,
    entries: HashMap<u64, EntryRecord>,
    entry_ids: HashMap<u64, BTreeSet<u64>>,
    head_entry_ids: HashMap<u64, BTreeSet<u64>>,
    entry_commit_seqs: HashMap<u64, Seq>,
    tasks: HashMap<u64, AnyTaskRecord>,
    task_ids: BTreeSet<u64>,
    task_ids_by_status: [BTreeSet<u64>; TASK_STATUSES],
    submissions: HashMap<u64, SubmissionRecord>,
    submission_ids: BTreeSet<u64>,
    submission_ids_by_status: [BTreeSet<u64>; SUBMISSION_STATUSES],
    submission_ids_by_request: HashMap<u64, HashMap<String, u64>>,
    documents: HashMap<u64, StoredDocumentState>,
    document_addresses: HashMap<AddressKey, DocumentAddressIndex>,
    document_ids_by_scope: HashMap<ScopeKey, BTreeSet<u64>>,
    next_id: u64,
    next_seq: u64,
    closed: bool,
}

/// IDs of `ids` after the cursor position `after` (TS `upperBound(ids, after)`).
fn ids_after(ids: &BTreeSet<u64>, after: Option<i64>) -> impl Iterator<Item = u64> + '_ {
    let start = match after {
        None => Bound::Unbounded,
        Some(after) if after < 0 => Bound::Unbounded,
        Some(after) => Bound::Excluded(after.unsigned_abs()),
    };
    ids.range((start, Bound::Unbounded)).copied()
}

/// Sorted `ids` in scan order, after the cursor's ID when there is one (TS
/// `scanIndexes`).
fn scan_ids(ids: &BTreeSet<u64>, start: ScanStart) -> Box<dyn Iterator<Item = u64> + '_> {
    match start.order {
        ScanOrder::Ascending => Box::new(ids_after(ids, start.after)),
        ScanOrder::Descending => {
            let end = match start.after {
                None => Bound::Unbounded,
                Some(after) => Bound::Excluded(u64::try_from(after).unwrap_or(0)),
            };
            Box::new(ids.range((Bound::Unbounded, end)).rev().copied())
        }
    }
}

/// IDs of `ids` at or below `upper`, newest first. `upper` is a JS number:
/// an ID, a cursor minus one, or infinity.
fn ids_at_or_below(ids: &BTreeSet<u64>, upper: f64) -> impl Iterator<Item = u64> + '_ {
    let end = if upper < 0.0 {
        None
    } else if upper >= MAX_SAFE_INTEGER {
        Some(Bound::Unbounded)
    } else {
        #[expect(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "a non-negative safe integer"
        )]
        Some(Bound::Included(upper.floor() as u64))
    };
    end.into_iter()
        .flat_map(move |end| ids.range((Bound::Unbounded, end)).rev().copied())
}

#[expect(
    clippy::cast_precision_loss,
    reason = "IDs are safe integers, exact as JS numbers"
)]
fn id_number(id: u64) -> f64 {
    id as f64
}

/// The document content after the latest base at or before `at`.
fn materialize(
    state: &State,
    id: DocumentId,
    at: DocumentPoint,
) -> Result<Option<StoredDocument>, StorageError> {
    let Some(stored) = state.documents.get(&id.get()) else {
        return Ok(None);
    };
    if at != DocumentPoint::Current && is_current_only(stored.record.scope) {
        return Err(StorageError::request(format!(
            "Document {id} does not retain historical content"
        )));
    }
    if !is_alive_at(&stored.record, at) {
        return Ok(None);
    }
    let revisions: Vec<&DocumentRevision> = match at {
        DocumentPoint::Current => stored.revisions.iter().collect(),
        DocumentPoint::At(at) => stored
            .revisions
            .iter()
            .filter(|revision| revision.seq <= at)
            .collect(),
    };
    let Some(base_index) = revisions
        .iter()
        .rposition(|revision| matches!(revision.content, DocumentContent::Base(_)))
    else {
        return Err(failure(format!("Document {id} is missing a required base")));
    };
    let DocumentContent::Base(base) = &revisions[base_index].content else {
        return Err(failure(format!("Document {id} is missing a required base")));
    };
    let tail = &revisions[base_index + 1..];
    let batches = tail.iter().map(|revision| match &revision.content {
        DocumentContent::Delta(delta) if delta.version == base.version => Ok(&delta.ops[..]),
        DocumentContent::Base(_) | DocumentContent::Delta(_) => Err(failure(format!(
            "Document {id} crosses a stored version boundary without a base"
        ))),
    });
    let value = try_apply_immutable_batches::<_, &[Op], StorageError>(
        &JsonValue::Object(base.value.clone()),
        batches,
    )
    .map_err(|error| match error {
        BatchError::Delta(error) => StorageError::failed(error),
        BatchError::Source(error) => error,
    })?;
    let JsonValue::Object(value) = value else {
        return Err(failure(format!(
            "Document {id} materialized to a non-object value"
        )));
    };
    Ok(Some(StoredDocument {
        record: stored.record.clone(),
        version: base.version,
        value,
        deltas_since_base: tail.len() as u64,
    }))
}

/// Visit the entries visible through `conversation_id`'s ancestry between
/// the inclusive bounds, newest first, until `visit` returns false.
fn visible_entries(
    state: &State,
    conversation_id: ConversationId,
    min_entry_id: f64,
    max_entry_id: f64,
    mut visit: impl FnMut(&EntryRecord) -> bool,
) -> Result<(), StorageError> {
    if !state.conversations.contains_key(&conversation_id.get()) {
        return Err(StorageError::request(format!(
            "Unknown conversation: {conversation_id}"
        )));
    }
    let empty = BTreeSet::new();
    let mut current_id = conversation_id.get();
    let mut upper_entry_id = max_entry_id;
    loop {
        let ids = state.entry_ids.get(&current_id).unwrap_or(&empty);
        for id in ids_at_or_below(ids, upper_entry_id) {
            if id_number(id) < min_entry_id {
                break;
            }
            if !visit(&state.entries[&id]) {
                return Ok(());
            }
        }
        let conversation = &state.conversations[&current_id];
        let Some(parent) = conversation.parent else {
            break;
        };
        upper_entry_id = upper_entry_id.min(id_number(parent.at.get()));
        if upper_entry_id < min_entry_id {
            break;
        }
        current_id = parent.conversation_id.get();
    }
    Ok(())
}

/// Visit the entries visible through `conversation_id`'s ancestry between
/// the inclusive bounds oldest first, until `visit` returns false: the fork
/// chain's segments from the root conversation forward.
fn visible_entries_ascending(
    state: &State,
    conversation_id: ConversationId,
    min_entry_id: f64,
    max_entry_id: f64,
    mut visit: impl FnMut(&EntryRecord) -> bool,
) -> Result<(), StorageError> {
    if !state.conversations.contains_key(&conversation_id.get()) {
        return Err(StorageError::request(format!(
            "Unknown conversation: {conversation_id}"
        )));
    }
    let mut segments: Vec<(u64, f64)> = Vec::new();
    let mut current_id = conversation_id.get();
    let mut upper_entry_id = max_entry_id;
    loop {
        segments.push((current_id, upper_entry_id));
        let Some(parent) = state.conversations[&current_id].parent else {
            break;
        };
        upper_entry_id = upper_entry_id.min(id_number(parent.at.get()));
        if upper_entry_id < min_entry_id {
            break;
        }
        current_id = parent.conversation_id.get();
    }
    let empty = BTreeSet::new();
    let lower = if min_entry_id <= 0.0 {
        0
    } else {
        #[expect(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "a positive bound; above every ID it selects nothing"
        )]
        let lower = min_entry_id.ceil() as u64;
        lower
    };
    for (segment, upper) in segments.into_iter().rev() {
        let ids = state.entry_ids.get(&segment).unwrap_or(&empty);
        for id in ids.range(lower..) {
            if id_number(*id) > upper {
                break;
            }
            if !visit(&state.entries[id]) {
                return Ok(());
            }
        }
    }
    Ok(())
}

impl State {
    fn new() -> Self {
        Self {
            next_id: 2,
            next_seq: 1,
            ..Self::default()
        }
    }

    fn assert_open(&self) -> Result<(), StorageError> {
        if self.closed {
            return Err(failure("MemoryStorage is closed"));
        }
        Ok(())
    }

    fn resolve_document_copies(
        &self,
        writes: &[StorageWrite],
    ) -> Result<Vec<StorageWrite>, StorageError> {
        if !writes
            .iter()
            .any(|write| matches!(write, StorageWrite::DocumentCopy { .. }))
        {
            return Ok(writes.to_vec());
        }
        let mut changed_document_ids = BTreeSet::new();
        for write in writes {
            match write {
                StorageWrite::DocumentCreate { record, .. }
                | StorageWrite::DocumentCopy { record, .. } => {
                    changed_document_ids.insert(record.id);
                }
                StorageWrite::DocumentChange { id, .. } | StorageWrite::DocumentRetire { id } => {
                    changed_document_ids.insert(*id);
                }
                StorageWrite::Conversation { .. }
                | StorageWrite::Entry { .. }
                | StorageWrite::Task { .. }
                | StorageWrite::Submission { .. } => {}
            }
        }
        writes
            .iter()
            .map(|write| {
                let StorageWrite::DocumentCopy { record, source } = write else {
                    return Ok(write.clone());
                };
                let resolve = || -> Result<StorageWrite, StorageError> {
                    if changed_document_ids.contains(&source.id) {
                        return Err(failure(format!(
                            "Fork source document {} is changed in the copy batch",
                            source.id
                        )));
                    }
                    let Some(stored) = materialize(self, source.id, source.at)? else {
                        return Err(failure(format!(
                            "Fork source document {} cannot be read",
                            source.id
                        )));
                    };
                    let both_conversation =
                        matches!(
                            stored.record.scope.scope(),
                            DocumentScope::Conversation { .. }
                        ) && matches!(record.scope.scope(), DocumentScope::Conversation { .. });
                    if !both_conversation
                        || stored.record.kind != record.kind
                        || stored.record.key != record.key
                        || stored.record.scope.history() != record.scope.history()
                        || stored.record.scope.fork() != record.scope.fork()
                    {
                        return Err(failure(format!(
                            "Fork source document {} does not match the copied record",
                            source.id
                        )));
                    }
                    Ok(StorageWrite::DocumentCreate {
                        record: record.clone(),
                        content: DocumentBase {
                            version: stored.version,
                            value: stored.value,
                        },
                    })
                };
                resolve().map_err(|error| {
                    failure_with_cause(format!("Document copy {} was rejected", record.id), error)
                })
            })
            .collect()
    }

    fn check_global_ids(&self, writes: &[StorageWrite]) -> Result<(), StorageError> {
        let mut claimed: HashMap<u64, TableName> = HashMap::new();
        for write in writes {
            let (table, id) = match write {
                StorageWrite::DocumentChange { .. } | StorageWrite::DocumentRetire { .. } => {
                    continue
                }
                StorageWrite::Conversation { value } => (TableName::Conversation, value.id.get()),
                StorageWrite::Entry { value } => (TableName::Entry, value.id.get()),
                StorageWrite::Task { value } => (TableName::Task, value.id.get()),
                StorageWrite::Submission { value } => (TableName::Submission, value.id.get()),
                StorageWrite::DocumentCreate { record, .. }
                | StorageWrite::DocumentCopy { record, .. } => {
                    (TableName::Document, record.id.get())
                }
            };
            let existing = self.record_types.get(&id).copied();
            let earlier = claimed.get(&id).copied();
            match table {
                TableName::Conversation | TableName::Entry | TableName::Document => {
                    if let Some(existing) = existing {
                        return Err(failure(format!(
                            "ID {id} already belongs to {}",
                            existing.as_str()
                        )));
                    }
                    if earlier.is_some() {
                        return Err(failure(format!("ID {id} is written more than once")));
                    }
                }
                TableName::Task | TableName::Submission => {
                    if let Some(existing) = existing.filter(|existing| *existing != table) {
                        return Err(failure(format!(
                            "ID {id} already belongs to {}",
                            existing.as_str()
                        )));
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

    fn check_document_actions(
        &self,
        actions: &[(DocumentId, DocumentAction)],
    ) -> Result<(), StorageError> {
        let mut live_counts: HashMap<AddressKey, i64> = HashMap::new();
        for (id, action) in actions {
            let existing = self.documents.get(&id.get());
            if action.create.is_none() && existing.is_none() {
                return Err(failure(format!("Unknown document: {id}")));
            }
            if action.create.is_some() && existing.is_some() {
                return Err(failure(format!("Document {id} already exists")));
            }
            if existing.is_some_and(|existing| existing.record.retired_at.is_some()) {
                return Err(failure(format!("Document {id} is retired")));
            }
            if let Some(DocumentContent::Delta(delta)) = &action.content {
                let Some(previous) = existing.and_then(|existing| existing.revisions.last()) else {
                    return Err(failure(format!("Document {id} delta has no base")));
                };
                if previous.content.version() != delta.version {
                    return Err(failure(format!(
                        "Document {id} version transition requires a base"
                    )));
                }
            }

            let key = match (&action.create, existing) {
                (Some(create), _) => AddressKey::of_create(create),
                (None, Some(existing)) => AddressKey::of_record(&existing.record),
                (None, None) => return Err(failure(format!("Unknown document: {id}"))),
            };
            let current_id = self
                .document_addresses
                .get(&key)
                .and_then(|address| address.current_id);
            let live = live_counts
                .entry(key)
                .or_insert_with(|| i64::from(current_id.is_some()));
            if action.retire && current_id == Some(id.get()) {
                *live -= 1;
            }
            if action.create.is_some() && !action.retire {
                *live += 1;
            }
        }
        if live_counts.values().any(|live| *live > 1) {
            return Err(failure(
                "Document address already has a current incarnation",
            ));
        }
        Ok(())
    }

    fn apply_prepared_commit(
        &mut self,
        prepared: &[StorageWrite],
        document_actions: &[(DocumentId, DocumentAction)],
        seq: Seq,
    ) {
        for write in prepared {
            match write {
                StorageWrite::Conversation { value } => {
                    let id = value.id.get();
                    self.record_types.insert(id, TableName::Conversation);
                    self.conversations.insert(id, *value);
                    self.conversation_ids.insert(id);
                    if let Some(owner) = value.owner {
                        self.conversation_ids_by_owner_conversation
                            .entry(owner.conversation_id.get())
                            .or_default()
                            .insert(id);
                        self.conversation_ids_by_owner_task
                            .entry(owner.task_id.get())
                            .or_default()
                            .insert(id);
                    }
                    self.next_id = self.next_id.max(id + 1);
                }
                StorageWrite::Entry { value } => {
                    let id = value.id.get();
                    self.record_types.insert(id, TableName::Entry);
                    self.entries.insert(id, value.clone());
                    self.entry_commit_seqs.insert(id, seq);
                    self.entry_ids
                        .entry(value.conversation_id.get())
                        .or_default()
                        .insert(id);
                    if value.head.is_some() {
                        self.head_entry_ids
                            .entry(value.conversation_id.get())
                            .or_default()
                            .insert(id);
                    }
                    self.next_id = self.next_id.max(id + 1);
                }
                StorageWrite::Task { value } => {
                    let id = value.id.get();
                    self.record_types.insert(id, TableName::Task);
                    let status = task_status_index(value.state.status());
                    match self.tasks.get(&id) {
                        None => {
                            self.task_ids.insert(id);
                            self.task_ids_by_status[status].insert(id);
                        }
                        Some(previous) => {
                            let previous = task_status_index(previous.state.status());
                            if previous != status {
                                self.task_ids_by_status[previous].remove(&id);
                                self.task_ids_by_status[status].insert(id);
                            }
                        }
                    }
                    self.tasks.insert(id, value.clone());
                    self.next_id = self.next_id.max(id + 1);
                }
                StorageWrite::Submission { value } => self.apply_submission(value),
                StorageWrite::DocumentCopy { .. } => {
                    unreachable!("prepare_commit resolves every document copy into a creation")
                }
                StorageWrite::DocumentCreate { .. }
                | StorageWrite::DocumentChange { .. }
                | StorageWrite::DocumentRetire { .. } => {}
            }
        }
        self.apply_document_actions(document_actions, seq);
        self.next_seq = seq.get() + 1;
    }

    fn apply_submission(&mut self, value: &SubmissionRecord) {
        let id = value.id.get();
        self.record_types.insert(id, TableName::Submission);
        let status = submission_status_index(value.state.status());
        let previous = self.submissions.get(&id);
        match previous {
            None => {
                self.submission_ids.insert(id);
                self.submission_ids_by_status[status].insert(id);
            }
            Some(previous) => {
                let previous = submission_status_index(previous.state.status());
                if previous != status {
                    self.submission_ids_by_status[previous].remove(&id);
                    self.submission_ids_by_status[status].insert(id);
                }
            }
        }
        if let Some(previous) = previous {
            if let Some(request_id) = &previous.request_id {
                let conversation_id = previous.conversation_id.get();
                if let Some(requests) = self.submission_ids_by_request.get_mut(&conversation_id) {
                    if requests.get(request_id) == Some(&id) {
                        requests.remove(request_id);
                        if requests.is_empty() {
                            self.submission_ids_by_request.remove(&conversation_id);
                        }
                    }
                }
            }
        }
        self.submissions.insert(id, value.clone());
        if let Some(request_id) = &value.request_id {
            self.submission_ids_by_request
                .entry(value.conversation_id.get())
                .or_default()
                .insert(request_id.clone(), id);
        }
        self.next_id = self.next_id.max(id + 1);
    }

    fn apply_document_actions(&mut self, actions: &[(DocumentId, DocumentAction)], seq: Seq) {
        for (id, action) in actions {
            let id = id.get();
            if let Some(create) = &action.create {
                let mut record = DocumentRecord::from_create(create.clone(), seq);
                if action.retire {
                    record.retired_at = Some(seq);
                }
                let content = action.content.clone().expect("a creation carries its base");
                let scope = ScopeKey::of(record.scope.scope());
                let key = AddressKey::of_record(&record);
                self.record_types.insert(id, TableName::Document);
                self.documents.insert(
                    id,
                    StoredDocumentState {
                        record,
                        revisions: vec![DocumentRevision { content, seq }],
                    },
                );
                self.document_addresses
                    .entry(key)
                    .or_default()
                    .ids
                    .insert(id);
                self.document_ids_by_scope
                    .entry(scope)
                    .or_default()
                    .insert(id);
                self.next_id = self.next_id.max(id + 1);
            } else if let Some(content) = &action.content {
                let stored = self.documents.get_mut(&id).expect("checked document");
                let revision = DocumentRevision {
                    content: content.clone(),
                    seq,
                };
                if matches!(content, DocumentContent::Base(_))
                    && is_current_only(stored.record.scope)
                {
                    stored.revisions = vec![revision];
                } else {
                    stored.revisions.push(revision);
                }
            }

            let stored = self.documents.get_mut(&id).expect("checked document");
            if action.retire && action.create.is_none() {
                stored.record.retired_at = Some(seq);
            }
            if action.retire && is_current_only(stored.record.scope) {
                stored.revisions.clear();
            }
            if action.create.is_some() || action.retire {
                let key = AddressKey::of_record(&stored.record);
                let address = self
                    .document_addresses
                    .get_mut(&key)
                    .expect("indexed address");
                if action.retire && address.current_id == Some(id) {
                    address.current_id = None;
                }
                if action.create.is_some() && !action.retire {
                    address.current_id = Some(id);
                }
            }
        }
    }
}

fn prepare_document_actions(
    writes: &[StorageWrite],
) -> Result<Vec<(DocumentId, DocumentAction)>, StorageError> {
    let mut actions: Vec<(DocumentId, DocumentAction)> = Vec::new();
    let mut positions: HashMap<DocumentId, usize> = HashMap::new();
    for write in writes {
        let id = match write {
            StorageWrite::DocumentCreate { record, .. } => record.id,
            StorageWrite::DocumentChange { id, .. } | StorageWrite::DocumentRetire { id } => *id,
            StorageWrite::Conversation { .. }
            | StorageWrite::Entry { .. }
            | StorageWrite::Task { .. }
            | StorageWrite::Submission { .. }
            | StorageWrite::DocumentCopy { .. } => continue,
        };
        let position = *positions.entry(id).or_insert_with(|| {
            actions.push((
                id,
                DocumentAction {
                    create: None,
                    content: None,
                    retire: false,
                },
            ));
            actions.len() - 1
        });
        let action = &mut actions[position].1;
        match write {
            StorageWrite::DocumentCreate { record, content } => {
                if action.create.is_some() || action.content.is_some() {
                    return Err(failure(format!(
                        "Document {id} has more than one content command"
                    )));
                }
                action.create = Some(record.clone());
                action.content = Some(DocumentContent::Base(content.clone()));
            }
            StorageWrite::DocumentChange { content, .. } => {
                if action.content.is_some() {
                    return Err(failure(format!(
                        "Document {id} has more than one content command"
                    )));
                }
                action.content = Some(content.clone());
            }
            StorageWrite::DocumentRetire { .. } => {
                if action.retire {
                    return Err(failure(format!("Document {id} is retired more than once")));
                }
                action.retire = true;
            }
            StorageWrite::Conversation { .. }
            | StorageWrite::Entry { .. }
            | StorageWrite::Task { .. }
            | StorageWrite::Submission { .. }
            | StorageWrite::DocumentCopy { .. } => {}
        }
    }
    Ok(actions)
}

/// A fully validated, detached state mutation whose application performs no
/// fallible preparation.
#[derive(Debug)]
pub struct PreparedMemoryCommit {
    state: Arc<Mutex<State>>,
    seq: Seq,
    writes: Vec<StorageWrite>,
    resolved_copies: Vec<bool>,
    document_actions: Vec<(DocumentId, DocumentAction)>,
    applied: AtomicBool,
}

impl PreparedMemoryCommit {
    /// The sequence the commit takes.
    #[must_use]
    pub fn seq(&self) -> Seq {
        self.seq
    }

    /// The detached writes for persistence, with every `document.copy`
    /// resolved into a `document.create` of the copied base.
    #[must_use]
    pub fn writes(&self) -> &[StorageWrite] {
        &self.writes
    }

    /// Whether `writes()[index]` is a `document.copy` resolved into a
    /// creation. TS builds that base content as `{ kind, version, value }`,
    /// so its JSON key order differs from a caller-supplied base.
    #[must_use]
    pub fn is_resolved_copy(&self, index: usize) -> bool {
        self.resolved_copies.get(index).copied().unwrap_or(false)
    }

    /// Apply the commit once; later calls only return its sequence.
    pub fn apply(&self) -> Seq {
        if !self.applied.swap(true, Ordering::AcqRel) {
            let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
            state.apply_prepared_commit(&self.writes, &self.document_actions, self.seq);
        }
        self.seq
    }
}

/// Detached in-memory reference implementation of [`Storage`].
///
/// Reads and retained writes are owned copies, matching the ownership
/// boundary of serialization-backed stores. This is backend conformance, not
/// validation. Clones share one store.
#[derive(Clone, Debug)]
pub struct MemoryStorage {
    state: Arc<Mutex<State>>,
}

impl Default for MemoryStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryStorage {
    /// An empty store.
    #[must_use]
    pub fn new() -> Self {
        Self {
            state: Arc::new(Mutex::new(State::new())),
        }
    }

    fn read<T>(
        &self,
        read: impl FnOnce(&State) -> Result<T, StorageError>,
    ) -> Result<T, StorageError> {
        let state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        state.assert_open()?;
        read(&state)
    }

    /// Validate and detach one commit without changing observable state.
    /// `seq` defaults to the next sequence.
    ///
    /// # Errors
    ///
    /// The storage is closed, `seq` does not strictly increase, or the batch
    /// is invalid (rejected document copies are [`StorageError::Rejected`]).
    pub fn prepare_commit(
        &self,
        writes: &[StorageWrite],
        seq: Option<Seq>,
    ) -> Result<PreparedMemoryCommit, StorageError> {
        let state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        state.assert_open()?;
        let seq = seq.unwrap_or_else(|| Seq::from_number(state.next_seq));
        if id_number(seq.get()) > MAX_SAFE_INTEGER || seq.get() < state.next_seq {
            return Err(failure(format!(
                "Commit sequence {seq} does not strictly increase"
            )));
        }
        let resolved_copies = writes
            .iter()
            .map(|write| matches!(write, StorageWrite::DocumentCopy { .. }))
            .collect();
        let writes = state.resolve_document_copies(writes)?;
        state.check_global_ids(&writes)?;
        let document_actions = prepare_document_actions(&writes)?;
        state.check_document_actions(&document_actions)?;
        Ok(PreparedMemoryCommit {
            state: Arc::clone(&self.state),
            seq,
            writes,
            resolved_copies,
            document_actions,
            applied: AtomicBool::new(false),
        })
    }

    fn scan_conversations_now(
        &self,
        query: &ConversationQuery,
        limit: usize,
        cursor: Option<&Cursor>,
    ) -> Result<Page<ConversationRecord>, StorageError> {
        self.read(|state| {
            let empty = BTreeSet::new();
            let ids = if let Some(task_id) = query.owner_task_id {
                state
                    .conversation_ids_by_owner_task
                    .get(&task_id.get())
                    .unwrap_or(&empty)
            } else if let Some(conversation_id) = query.owner_conversation_id {
                state
                    .conversation_ids_by_owner_conversation
                    .get(&conversation_id.get())
                    .unwrap_or(&empty)
            } else {
                &state.conversation_ids
            };
            let start = scan_start(query.order, cursor, ScanOrder::Ascending)?;
            let mut values = Vec::new();
            for id in scan_ids(ids, start) {
                if values.len() > limit {
                    break;
                }
                let value = state.conversations[&id];
                if let Some(owner_conversation_id) = query.owner_conversation_id {
                    if value.owner.map(|owner| owner.conversation_id) != Some(owner_conversation_id)
                    {
                        continue;
                    }
                }
                values.push(value);
            }
            Ok(page(values, limit, start.order))
        })
    }

    fn entry_in_now(
        &self,
        conversation_id: ConversationId,
        id: EntryId,
    ) -> Result<Option<StoredEntry>, StorageError> {
        self.read(|state| {
            let mut found = None;
            visible_entries(
                state,
                conversation_id,
                id_number(id.get()),
                id_number(id.get()),
                |entry| {
                    found = Some(entry.clone());
                    false
                },
            )?;
            Ok(found.map(|entry| StoredEntry {
                entry,
                commit_seq: state.entry_commit_seqs[&id.get()],
            }))
        })
    }

    fn find_latest_head_marker_now(
        &self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
    ) -> Result<Option<EntryRecord>, StorageError> {
        self.read(|state| {
            if !state.conversations.contains_key(&conversation_id.get()) {
                return Err(StorageError::request(format!(
                    "Unknown conversation: {conversation_id}"
                )));
            }
            let empty = BTreeSet::new();
            let mut current_id = conversation_id.get();
            let mut upper_entry_id =
                at_or_before_entry_id.map_or(f64::INFINITY, |id| id_number(id.get()));
            loop {
                let ids = state.head_entry_ids.get(&current_id).unwrap_or(&empty);
                if let Some(id) = ids_at_or_below(ids, upper_entry_id).next() {
                    return Ok(Some(state.entries[&id].clone()));
                }
                let Some(parent) = state.conversations[&current_id].parent else {
                    return Ok(None);
                };
                upper_entry_id = upper_entry_id.min(id_number(parent.at.get()));
                current_id = parent.conversation_id.get();
            }
        })
    }

    fn scan_entries_now(
        &self,
        query: &EntryQuery,
        limit: usize,
        cursor: Option<&Cursor>,
    ) -> Result<Page<EntryRecord>, StorageError> {
        self.read(|state| {
            let ScanStart { order, after } =
                scan_start(query.order, cursor, ScanOrder::Descending)?;
            // The cursor narrows the bound on the side the scan moves away from.
            let mut max_entry_id = query
                .max_entry_id
                .map_or(f64::INFINITY, |id| id_number(id.get()));
            let mut min_entry_id = query
                .min_entry_id
                .map_or(f64::NEG_INFINITY, |id| id_number(id.get()));
            #[expect(clippy::cast_precision_loss, reason = "cursor IDs are safe integers")]
            let after = after.map(|after| after as f64);
            if let Some(after) = after {
                match order {
                    ScanOrder::Descending => max_entry_id = max_entry_id.min(after - 1.0),
                    ScanOrder::Ascending => min_entry_id = min_entry_id.max(after + 1.0),
                }
            }
            let mut visible = Vec::new();
            let visit = |entry: &EntryRecord| {
                visible.push(entry.clone());
                visible.len() <= limit
            };
            match order {
                ScanOrder::Descending => visible_entries(
                    state,
                    query.conversation_id,
                    min_entry_id,
                    max_entry_id,
                    visit,
                )?,
                ScanOrder::Ascending => visible_entries_ascending(
                    state,
                    query.conversation_id,
                    min_entry_id,
                    max_entry_id,
                    visit,
                )?,
            }
            Ok(page(visible, limit, order))
        })
    }

    fn scan_tasks_now(
        &self,
        query: &TaskQuery,
        limit: usize,
        cursor: Option<&Cursor>,
    ) -> Result<Page<AnyTaskRecord>, StorageError> {
        self.read(|state| {
            let start = scan_start(query.order, cursor, ScanOrder::Ascending)?;
            let ids = match query.status {
                None => &state.task_ids,
                Some(status) => &state.task_ids_by_status[task_status_index(status)],
            };
            let mut values = Vec::new();
            for id in scan_ids(ids, start) {
                if values.len() > limit {
                    break;
                }
                let value = &state.tasks[&id];
                if query
                    .conversation_id
                    .is_some_and(|conversation_id| value.conversation_id != conversation_id)
                    || query.kind.as_ref().is_some_and(|kind| value.kind != *kind)
                    || query
                        .abort_requested
                        .is_some_and(|requested| value.abort_requested != requested)
                    || query
                        .background
                        .is_some_and(|background| value.background != background)
                {
                    continue;
                }
                values.push(value.clone());
            }
            Ok(page(values, limit, start.order))
        })
    }

    fn scan_submissions_now(
        &self,
        query: &SubmissionQuery,
        limit: usize,
        cursor: Option<&Cursor>,
    ) -> Result<Page<SubmissionRecord>, StorageError> {
        self.read(|state| {
            let start = scan_start(query.order, cursor, ScanOrder::Ascending)?;
            let ids = match query.status {
                None => &state.submission_ids,
                Some(status) => &state.submission_ids_by_status[submission_status_index(status)],
            };
            let mut values = Vec::new();
            for id in scan_ids(ids, start) {
                if values.len() > limit {
                    break;
                }
                let value = &state.submissions[&id];
                if query
                    .conversation_id
                    .is_some_and(|conversation_id| value.conversation_id != conversation_id)
                {
                    continue;
                }
                values.push(value.clone());
            }
            Ok(page(values, limit, start.order))
        })
    }

    fn find_document_now(
        &self,
        address: &DocumentAddress,
        at: DocumentPoint,
    ) -> Result<Option<DocumentRecord>, StorageError> {
        self.read(|state| {
            let index = state.document_addresses.get(&AddressKey::of(address));
            if at == DocumentPoint::Current {
                return Ok(index
                    .and_then(|index| index.current_id)
                    .map(|id| state.documents[&id].record.clone()));
            }
            Ok(index.and_then(|index| {
                index
                    .ids
                    .iter()
                    .map(|id| &state.documents[id].record)
                    .find(|record| is_alive_at(record, at))
                    .cloned()
            }))
        })
    }

    fn scan_documents_now(
        &self,
        query: &DocumentQuery,
        limit: usize,
        cursor: Option<&Cursor>,
    ) -> Result<Page<DocumentRecord>, StorageError> {
        self.read(|state| {
            let empty = BTreeSet::new();
            let ids = state
                .document_ids_by_scope
                .get(&ScopeKey::of(query.scope))
                .unwrap_or(&empty);
            let after = cursor_id(cursor)?;
            let mut values = Vec::new();
            for id in ids_after(ids, after) {
                if values.len() > limit {
                    break;
                }
                let record = &state.documents[&id].record;
                if query.kind.as_ref().is_some_and(|kind| record.kind != *kind) {
                    continue;
                }
                if is_alive_at(record, query.at) {
                    values.push(record.clone());
                }
            }
            Ok(page(values, limit, ScanOrder::Ascending))
        })
    }
}

fn ready<'a, T: Send + 'a>(
    result: Result<T, StorageError>,
) -> BoxFuture<'a, Result<T, StorageError>> {
    Box::pin(std::future::ready(result))
}

impl Storage for MemoryStorage {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        ready(
            self.prepare_commit(writes, None)
                .map(|prepared| prepared.apply()),
        )
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        let result = state.assert_open().and_then(|()| {
            if id_number(state.next_id) > MAX_SAFE_INTEGER {
                return Err(failure("ID space is exhausted"));
            }
            let id = state.next_id;
            state.next_id += 1;
            Ok(id)
        });
        drop(state);
        ready(result)
    }

    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>> {
        ready(self.read(|state| Ok(state.conversations.get(&id.get()).copied())))
    }

    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>> {
        ready(self.scan_conversations_now(query, limit, cursor))
    }

    fn entry<'a>(
        &'a self,
        id: EntryId,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        ready(self.read(|state| {
            Ok(state.entries.get(&id.get()).map(|entry| StoredEntry {
                entry: entry.clone(),
                commit_seq: state.entry_commit_seqs[&id.get()],
            }))
        }))
    }

    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        ready(self.entry_in_now(conversation_id, id))
    }

    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>> {
        ready(self.find_latest_head_marker_now(conversation_id, at_or_before_entry_id))
    }

    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>> {
        ready(self.scan_entries_now(query, limit, cursor))
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        ready(self.read(|state| Ok(state.tasks.get(&id.get()).cloned())))
    }

    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>> {
        ready(self.scan_tasks_now(query, limit, cursor))
    }

    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        ready(self.read(|state| Ok(state.submissions.get(&id.get()).cloned())))
    }

    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>> {
        ready(self.scan_submissions_now(query, limit, cursor))
    }

    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        ready(self.read(|state| {
            Ok(state
                .submission_ids_by_request
                .get(&conversation_id.get())
                .and_then(|requests| requests.get(request_id))
                .map(|id| state.submissions[id].clone()))
        }))
    }

    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>> {
        ready(self.find_document_now(address, at))
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
        ready(self.read(|state| materialize(state, id, at)))
    }

    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        _cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>> {
        ready(self.scan_documents_now(query, limit, cursor))
    }

    fn close<'a>(&'a self, _cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        self.state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .closed = true;
        ready(Ok(()))
    }
}

#[cfg(test)]
impl MemoryStorage {
    /// Reopen after `close()`, as a fresh process would reopen the same
    /// database, keeping every committed record (TS test `reopen()`).
    pub(crate) fn reopen(&self) {
        self.state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .closed = false;
    }
}
