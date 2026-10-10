//! Public error types (`errors.ts`) and the storage error model (spec §10).

use std::error::Error;
use std::sync::Arc;

use crate::session::SessionError;
use crate::types::ConversationId;

/// A transaction read a table after its first table write. Read every
/// required row before writing.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("Tx.{method}() cannot read tables after the first table write")]
pub struct ReadAfterWrite {
    /// The `Tx` method, as TS names it (`"entry"`, `"scanEntries"`, ...).
    pub method: &'static str,
}

impl ReadAfterWrite {
    /// The error for `Tx.{method}()`.
    #[must_use]
    pub fn new(method: &'static str) -> Self {
        Self { method }
    }
}

/// A Storage read rejected an invalid request, such as an unknown
/// conversation or a cursor from another scan, with no durable effect. Unlike
/// any other error a Storage returns, it fails only that read, not the
/// Session; from `commit()` it is fatal like any other.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{message}")]
pub struct StorageRequestError {
    message: String,
}

impl StorageRequestError {
    /// The JS `error.name`.
    pub const NAME: &'static str = "StorageRequestError";

    /// An invalid-request error with `message`.
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    /// The message.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// The Session failed, so nothing runs or commits any more. It fails when a
/// Storage method fails, a commit cannot be adopted, or the Harness's own
/// bookkeeping fails (a scheduler commit, an internal commit listener).
/// `cause` is that first error. Reopen the Session; reopening recovers from
/// what was committed.
#[derive(Debug, Clone, thiserror::Error)]
#[error("Session failed after a storage error; close and reopen it")]
pub struct SessionFailed {
    cause: Arc<SessionError>,
}

impl SessionFailed {
    /// The JS `error.name`.
    pub const NAME: &'static str = "SessionFailed";

    /// The failure caused by `cause`.
    #[must_use]
    pub fn new(cause: Arc<SessionError>) -> Self {
        Self { cause }
    }

    /// The error that failed the Session (TS `error.cause`).
    #[must_use]
    pub fn cause(&self) -> &Arc<SessionError> {
        &self.cause
    }
}

/// A submission reached a busy conversation and was not admitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Conversation {conversation_id} is busy")]
pub struct ConversationBusy {
    /// The busy conversation.
    pub conversation_id: ConversationId,
}

impl ConversationBusy {
    /// The error for `conversation_id`.
    #[must_use]
    pub fn new(conversation_id: ConversationId) -> Self {
        Self { conversation_id }
    }
}

/// Failure of a [`Storage`](crate::types::Storage) operation.
///
/// Any failure is final: it fails the owning Session, which nothing retries.
/// Only a [`StorageError::Request`] from a read, or a read whose caller's
/// context was cancelled, fails just that read.
#[derive(Debug, Clone, thiserror::Error)]
pub enum StorageError {
    /// A read rejected an invalid request with no durable effect.
    #[error(transparent)]
    Request(#[from] StorageRequestError),
    /// Any other failure, including cancellation through the operation's context.
    #[error(transparent)]
    Failed(Arc<dyn Error + Send + Sync + 'static>),
}

impl StorageError {
    /// Wrap any other failure.
    #[must_use]
    pub fn failed(error: impl Error + Send + Sync + 'static) -> Self {
        Self::Failed(Arc::new(error))
    }

    /// A [`StorageRequestError`] with `message`.
    #[must_use]
    pub fn request(message: impl Into<String>) -> Self {
        Self::Request(StorageRequestError::new(message))
    }

    /// Whether this is a [`StorageRequestError`].
    #[must_use]
    pub fn is_request(&self) -> bool {
        matches!(self, Self::Request(_))
    }
}
