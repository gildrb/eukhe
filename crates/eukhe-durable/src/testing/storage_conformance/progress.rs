//! The case watchdog's progress signal: a [`Storage`] that counts its
//! completed calls. [`super::run_storage_conformance`] fails a case only
//! when this count stops moving, so a slow disk (an fsync backend under
//! load) is not a failure, but a hung call still is.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use eukhe_chord::context::Context;
use futures::future::BoxFuture;

use crate::errors::StorageError;
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationQuery, ConversationRecord, Cursor, DocumentAddress,
    DocumentId, DocumentPoint, DocumentQuery, DocumentRecord, EntryId, EntryQuery, EntryRecord,
    Page, Seq, Storage, StorageWrite, StoredDocument, StoredEntry, SubmissionId, SubmissionQuery,
    SubmissionRecord, TaskId, TaskQuery,
};

/// Delegates every call to `inner` and adds 1 to `completed` when the call
/// returns, success or error.
pub(super) struct Progress {
    inner: Arc<dyn Storage>,
    completed: Arc<AtomicU64>,
}

impl Progress {
    pub(super) fn new(inner: Arc<dyn Storage>, completed: Arc<AtomicU64>) -> Self {
        Self { inner, completed }
    }

    fn counted<'a, T: Send + 'a>(&'a self, call: BoxFuture<'a, T>) -> BoxFuture<'a, T> {
        Box::pin(async move {
            let result = call.await;
            self.completed.fetch_add(1, Ordering::SeqCst);
            result
        })
    }
}

impl Storage for Progress {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        self.counted(self.inner.commit(writes, cx))
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        self.counted(self.inner.mint_id())
    }

    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>> {
        self.counted(self.inner.conversation(id, cx))
    }

    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>> {
        self.counted(self.inner.scan_conversations(query, limit, cursor, cx))
    }

    fn entry<'a>(
        &'a self,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.counted(self.inner.entry(id, cx))
    }

    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.counted(self.inner.entry_in(conversation_id, id, cx))
    }

    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>> {
        self.counted(
            self.inner
                .find_latest_head_marker(conversation_id, at_or_before_entry_id, cx),
        )
    }

    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>> {
        self.counted(self.inner.scan_entries(query, limit, cursor, cx))
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        self.counted(self.inner.task(id, cx))
    }

    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>> {
        self.counted(self.inner.scan_tasks(query, limit, cursor, cx))
    }

    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.counted(self.inner.submission(id, cx))
    }

    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>> {
        self.counted(self.inner.scan_submissions(query, limit, cursor, cx))
    }

    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.counted(
            self.inner
                .submission_by_request(conversation_id, request_id, cx),
        )
    }

    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>> {
        self.counted(self.inner.find_document(address, at, cx))
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
        self.counted(self.inner.document(id, at, cx))
    }

    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>> {
        self.counted(self.inner.scan_documents(query, limit, cursor, cx))
    }

    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        self.counted(self.inner.close(cx))
    }
}
