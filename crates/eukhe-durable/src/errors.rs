//! Public error types (`errors.ts`) and the storage error model (spec §10).

use std::error::Error;
use std::fmt;
use std::sync::Arc;

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

/// Storage rejected a batch before any durable effect; the owning Session may
/// continue safely.
#[derive(Clone)]
pub struct StorageRejected {
    message: String,
    cause: Option<Arc<dyn Error + Send + Sync + 'static>>,
}

impl StorageRejected {
    /// A rejection with `message`.
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            cause: None,
        }
    }

    /// A rejection with `message` caused by `cause` (TS `ErrorOptions.cause`).
    #[must_use]
    pub fn with_cause(
        message: impl Into<String>,
        cause: Arc<dyn Error + Send + Sync + 'static>,
    ) -> Self {
        Self {
            message: message.into(),
            cause: Some(cause),
        }
    }

    /// The message.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }

    /// The cause, if any.
    #[must_use]
    pub fn cause(&self) -> Option<&Arc<dyn Error + Send + Sync + 'static>> {
        self.cause.as_ref()
    }
}

impl fmt::Debug for StorageRejected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StorageRejected")
            .field("message", &self.message)
            .field("cause", &self.cause)
            .finish()
    }
}

impl fmt::Display for StorageRejected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl Error for StorageRejected {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.cause
            .as_deref()
            .map(|cause| cause as &(dyn Error + 'static))
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
/// A [`StorageError::Rejected`] commit had no durable effect. Any other
/// failure of an admitted commit leaves its state uncertain, which is fatal to
/// the owning Session (TS: any error other than `StorageRejected`).
#[derive(Debug, Clone, thiserror::Error)]
pub enum StorageError {
    /// The batch was rejected before any durable effect.
    #[error(transparent)]
    Rejected(#[from] StorageRejected),
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

    /// Whether this is a [`StorageRejected`] rejection.
    #[must_use]
    pub fn is_rejected(&self) -> bool {
        matches!(self, Self::Rejected(_))
    }
}
