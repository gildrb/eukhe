//! The Session's Storage behind its failure guard (TS `GuardedStorage` in
//! `session/session.ts`).

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Weak};

use eukhe_chord::context::Context;
use futures::future::BoxFuture;
use futures::FutureExt;
use tokio::sync::watch;

use super::error::SessionError;
use crate::errors::{SessionFailed, StorageError};
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationQuery, ConversationRecord, Cursor, DocumentAddress,
    DocumentId, DocumentPoint, DocumentQuery, DocumentRecord, EntryId, EntryQuery, EntryRecord,
    Page, Seq, Storage, StorageWrite, StoredDocument, StoredEntry, SubmissionId, SubmissionQuery,
    SubmissionRecord, TaskId, TaskQuery,
};

/// What the guard needs of its Session: the failure so far, and how to fail it.
pub(super) trait FailureLatch: Send + Sync {
    fn failure(&self) -> Option<Arc<SessionError>>;
    fn fail(&self, error: SessionError);
}

/// `new Error("Session is closed")` from a Storage call that starts while
/// the backend closes.
#[derive(Debug, Clone, Copy, thiserror::Error)]
#[error("Session is closed")]
pub(super) struct StorageClosing;

/// The Session's Storage behind its failure guard; every component of the
/// Session reads and writes through it. Before a call, a failed Session gets
/// `SessionFailed` without reaching the backend. A call that fails fails the
/// Session and returns the backend's error, unless it is a
/// [`StorageError::Request`] or a read whose caller's context was cancelled:
/// neither says the Storage is broken. `close()` always reaches the backend,
/// so a failed Session still closes it.
pub(super) struct GuardedStorage {
    storage: Arc<dyn Storage>,
    latch: Weak<dyn FailureLatch>,
    /// Backend calls underway, also those off the Session line, which close
    /// waits for before it closes the backend.
    underway: watch::Sender<usize>,
    closing: AtomicBool,
}

/// Decrements the underway count when a call settles or is dropped.
struct Underway<'a>(&'a watch::Sender<usize>);

impl Drop for Underway<'_> {
    fn drop(&mut self) {
        self.0.send_modify(|count| *count -= 1);
    }
}

impl GuardedStorage {
    pub(super) fn new(storage: Arc<dyn Storage>, latch: Weak<dyn FailureLatch>) -> Self {
        Self {
            storage,
            latch,
            underway: watch::channel(0).0,
            closing: AtomicBool::new(false),
        }
    }

    fn failure(&self) -> Option<Arc<SessionError>> {
        self.latch.upgrade().and_then(|latch| latch.failure())
    }

    fn assert_healthy(&self) -> Result<(), StorageError> {
        match self.failure() {
            Some(cause) => Err(StorageError::failed(SessionFailed::new(cause))),
            None => Ok(()),
        }
    }

    /// Run one backend call under the guard. `read` is a read's context;
    /// `commit()` and `mint_id()` pass none, so nothing exempts their errors:
    /// once a batch is admitted, whether it committed is unknown. A call still
    /// underway when another fails the Session ends with `SessionFailed` too,
    /// whatever it returns: nothing it read or wrote is used.
    fn call<'a, T: Send + 'a>(
        &'a self,
        read: Option<&'a Context>,
        run: impl FnOnce() -> BoxFuture<'a, Result<T, StorageError>> + Send + 'a,
    ) -> BoxFuture<'a, Result<T, StorageError>> {
        async move {
            self.assert_healthy()?;
            if self.closing.load(Ordering::SeqCst) {
                return Err(StorageError::failed(StorageClosing));
            }
            self.underway.send_modify(|count| *count += 1);
            let underway = Underway(&self.underway);
            let result = run().await;
            drop(underway);
            match result {
                Ok(value) => {
                    self.assert_healthy()?;
                    Ok(value)
                }
                Err(error) => {
                    self.assert_healthy()?;
                    // An invalid read, or one its caller cancelled, says nothing
                    // about the Storage; it fails that call only.
                    let exempt = read.is_some_and(|cx| error.is_request() || cx.aborted());
                    if !exempt {
                        if let Some(latch) = self.latch.upgrade() {
                            latch.fail(SessionError::from(error.clone()));
                        }
                    }
                    Err(error)
                }
            }
        }
        .boxed()
    }
}

impl Storage for GuardedStorage {
    /// Never exempt, whatever it returns: once admitted, whether a failed batch
    /// committed is unknown.
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        self.call(None, move || self.storage.commit(writes, cx))
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        self.call(None, move || self.storage.mint_id())
    }

    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>> {
        self.call(Some(cx), move || self.storage.conversation(id, cx))
    }

    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>> {
        self.call(Some(cx), move || {
            self.storage.scan_conversations(query, limit, cursor, cx)
        })
    }

    fn entry<'a>(
        &'a self,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.call(Some(cx), move || self.storage.entry(id, cx))
    }

    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.call(Some(cx), move || {
            self.storage.entry_in(conversation_id, id, cx)
        })
    }

    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>> {
        self.call(Some(cx), move || {
            self.storage
                .find_latest_head_marker(conversation_id, at_or_before_entry_id, cx)
        })
    }

    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>> {
        self.call(Some(cx), move || {
            self.storage.scan_entries(query, limit, cursor, cx)
        })
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        self.call(Some(cx), move || self.storage.task(id, cx))
    }

    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>> {
        self.call(Some(cx), move || {
            self.storage.scan_tasks(query, limit, cursor, cx)
        })
    }

    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.call(Some(cx), move || self.storage.submission(id, cx))
    }

    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>> {
        self.call(Some(cx), move || {
            self.storage.scan_submissions(query, limit, cursor, cx)
        })
    }

    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.call(Some(cx), move || {
            self.storage
                .submission_by_request(conversation_id, request_id, cx)
        })
    }

    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>> {
        self.call(Some(cx), move || {
            self.storage.find_document(address, at, cx)
        })
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
        self.call(Some(cx), move || self.storage.document(id, at, cx))
    }

    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>> {
        self.call(Some(cx), move || {
            self.storage.scan_documents(query, limit, cursor, cx)
        })
    }

    /// Close the backend once every call underway has settled, so none
    /// outlives it or fails after `closed` settles. New calls are refused from
    /// here on: a paged read must not start its next page while the backend
    /// closes.
    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        async move {
            self.closing.store(true, Ordering::SeqCst);
            let mut underway = self.underway.subscribe();
            // The sender lives in `self`, so the wait only ends at zero.
            let _ = underway.wait_for(|count| *count == 0).await;
            self.storage.close(cx).await
        }
        .boxed()
    }
}
