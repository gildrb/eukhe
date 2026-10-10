//! Helpers every storage backend shares. The TS backends each carry their own
//! copy of these (`cursorId`, `page`, `isAliveAt`, `isCurrentOnly`); the Rust
//! port keeps one.

use crate::errors::StorageError;
use crate::types::{
    AnyTaskRecord, ConversationRecord, ConversationSemantics, Cursor, DocumentPoint,
    DocumentRecord, DocumentRecordScope, EntryRecord, ScanOrder, SubmissionRecord,
};

/// A failure TS raises with `throw new Error(message)` or `new TypeError(message)`.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub(crate) struct StorageFailure(pub(crate) String);

/// `throw new Error(message)`: a failure that fails the Session.
pub(crate) fn failure(message: impl Into<String>) -> StorageError {
    StorageError::failed(StorageFailure(message.into()))
}

/// `new Error(message, { cause })`.
#[derive(Debug, Clone, thiserror::Error)]
#[error("{message}")]
pub(crate) struct CausedFailure {
    message: String,
    #[source]
    cause: StorageError,
}

/// `throw new Error(message, { cause })`.
pub(crate) fn failure_with_cause(message: impl Into<String>, cause: StorageError) -> StorageError {
    StorageError::failed(CausedFailure {
        message: message.into(),
        cause,
    })
}

/// Records a scan pages by ID.
pub(crate) trait PageItem {
    fn page_id(&self) -> u64;
}

impl PageItem for ConversationRecord {
    fn page_id(&self) -> u64 {
        self.id.get()
    }
}

impl PageItem for EntryRecord {
    fn page_id(&self) -> u64 {
        self.id.get()
    }
}

impl PageItem for AnyTaskRecord {
    fn page_id(&self) -> u64 {
        self.id.get()
    }
}

impl PageItem for SubmissionRecord {
    fn page_id(&self) -> u64 {
        self.id.get()
    }
}

impl PageItem for DocumentRecord {
    fn page_id(&self) -> u64 {
        self.id.get()
    }
}

/// The `after` ID of a backend cursor (TS `cursorId`): absent without a
/// cursor or `after`; `Invalid storage cursor` unless a safe integer.
pub(crate) fn cursor_id(cursor: Option<&Cursor>) -> Result<Option<i64>, StorageError> {
    let Some(after) = cursor.and_then(|cursor| cursor.get("after")) else {
        return Ok(None);
    };
    match after.as_number() {
        Some(number)
            if number.is_integer() && number.get().abs() <= eukhe_chord::json::MAX_SAFE_INTEGER =>
        {
            #[expect(
                clippy::cast_possible_truncation,
                reason = "a safe integer fits i64 exactly"
            )]
            Ok(Some(number.get() as i64))
        }
        _ => Err(StorageError::request("Invalid storage cursor")),
    }
}

/// One page of at most `limit` of `values`, which holds up to `limit + 1`
/// items; the extra item only signals a continuation after the last returned.
/// The cursor carries the scan's `order`.
pub(crate) fn page<T: PageItem>(
    mut values: Vec<T>,
    limit: usize,
    order: ScanOrder,
) -> crate::types::Page<T> {
    if values.len() <= limit {
        return crate::types::Page {
            items: values,
            next: None,
        };
    }
    values.truncate(limit);
    let next = values
        .last()
        .map(|last| super::scan::next_cursor(last.page_id(), order));
    crate::types::Page {
        items: values,
        next,
    }
}

/// Whether the incarnation is alive at `at`: `createdAt <= at < retiredAt`.
pub(crate) fn is_alive_at(record: &DocumentRecord, at: DocumentPoint) -> bool {
    match at {
        DocumentPoint::Current => record.retired_at.is_none(),
        DocumentPoint::At(at) => {
            record.created_at <= at && record.retired_at.is_none_or(|retired| at < retired)
        }
    }
}

/// Whether the scope keeps only current content: every scope but a
/// rewindable conversation document.
pub(crate) fn is_current_only(scope: DocumentRecordScope) -> bool {
    !matches!(
        scope,
        DocumentRecordScope::Conversation {
            semantics: ConversationSemantics::Rewindable(_),
            ..
        }
    )
}
