//! Errors of the Session kernel, its transactions, and its observers.

use std::sync::Arc;

use eukhe_chord::context::AbortReason;
use eukhe_chord::delta::TrackerError;
use eukhe_chord::json::JsonError;

use crate::documents::DocumentError;
use crate::errors::{ReadAfterWrite, SessionFailed, StorageError};

/// A Session, transaction, or observer failure. Messages are the TS messages.
///
/// TS throws plain `Error`s and `TypeError`s with literal messages; they are
/// [`SessionError::Error`] and [`SessionError::Type`]. Errors raised by
/// collaborators keep their own types.
#[derive(Clone, Debug, thiserror::Error)]
pub enum SessionError {
    /// A TS `Error` with this message.
    #[error("{0}")]
    Error(Arc<str>),
    /// A TS `TypeError` with this message.
    #[error("{0}")]
    Type(Arc<str>),
    /// A table read after the transaction's first table write.
    #[error(transparent)]
    ReadAfterWrite(ReadAfterWrite),
    /// A Storage failure; only a read's `StorageRequestError` leaves the Session usable.
    #[error(transparent)]
    Storage(StorageError),
    /// A document definition check, initializer, or migration failure.
    #[error(transparent)]
    Document(DocumentError),
    /// A value that is not strict JSON.
    #[error(transparent)]
    Json(Arc<JsonError>),
    /// A tracker, change, or draft failure.
    #[error(transparent)]
    Tracker(TrackerError),
    /// Every Session operation after the Session failed (TS `SessionFailed`).
    #[error(transparent)]
    Failed(SessionFailed),
    /// The caller's context was cancelled: its abort reason.
    #[error("{0}")]
    Aborted(AbortReason),
    /// An application failure raised inside a commit callback or listener.
    #[error(transparent)]
    Other(Arc<dyn std::error::Error + Send + Sync>),
}

impl SessionError {
    /// A TS `Error` with `message`.
    #[must_use]
    pub fn error(message: impl Into<Arc<str>>) -> Self {
        Self::Error(message.into())
    }

    /// A TS `TypeError` with `message`.
    #[must_use]
    pub fn type_error(message: impl Into<Arc<str>>) -> Self {
        Self::Type(message.into())
    }

    /// Wrap an application error.
    #[must_use]
    pub fn other(error: impl std::error::Error + Send + Sync + 'static) -> Self {
        Self::Other(Arc::new(error))
    }
}

impl SessionError {
    /// TS `new SessionFailed(cause)`.
    #[must_use]
    pub fn session_failed(cause: Arc<SessionError>) -> Self {
        Self::Failed(SessionFailed::new(cause))
    }
}

impl From<TrackerError> for SessionError {
    fn from(error: TrackerError) -> Self {
        Self::Tracker(error)
    }
}

/// A guarded Storage call reports a failed Session as `SessionFailed` and a
/// closing one as `Session is closed`, both through [`StorageError::Failed`];
/// they convert back to the Session's own errors.
impl From<StorageError> for SessionError {
    fn from(error: StorageError) -> Self {
        if let StorageError::Failed(cause) = &error {
            if let Some(failed) = cause.downcast_ref::<SessionFailed>() {
                return Self::Failed(failed.clone());
            }
            if cause
                .downcast_ref::<super::guarded::StorageClosing>()
                .is_some()
            {
                return Self::error("Session is closed");
            }
        }
        Self::Storage(error)
    }
}

impl From<ReadAfterWrite> for SessionError {
    fn from(error: ReadAfterWrite) -> Self {
        Self::ReadAfterWrite(error)
    }
}

impl From<DocumentError> for SessionError {
    fn from(error: DocumentError) -> Self {
        Self::Document(error)
    }
}

impl From<JsonError> for SessionError {
    fn from(error: JsonError) -> Self {
        Self::Json(Arc::new(error))
    }
}

/// Result of a Session operation.
pub type SessionResult<T> = Result<T, SessionError>;
