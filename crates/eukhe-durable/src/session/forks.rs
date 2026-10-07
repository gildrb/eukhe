//! Document copies selected by one conversation fork.

use std::collections::HashSet;

use eukhe_chord::context::Context;

use crate::documents::address_id;
use crate::types::{
    ConversationId, Cursor, DocumentCopySource, DocumentCreate, DocumentFork, DocumentId,
    DocumentPoint, DocumentQuery, DocumentRecordScope, DocumentScope, EntryId, Storage,
};

use super::transaction::record_address;

use super::error::{SessionError, SessionResult};

const SCAN_PAGE_SIZE: usize = 256;

/// One definition-free document copy to create with a forked conversation.
#[derive(Clone, Debug)]
pub(crate) struct ForkDocumentCopy {
    pub(crate) record: DocumentCreate,
    pub(crate) source: DocumentCopySource,
}

/// Select every persisted conversation document copied by one fork.
pub(crate) async fn prepare_fork_document_copies(
    storage: &dyn Storage,
    parent_conversation_id: ConversationId,
    at: EntryId,
    child_conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Vec<ForkDocumentCopy>> {
    let Some(entry) = storage.entry_in(parent_conversation_id, at, cx).await? else {
        return Err(SessionError::error(format!(
            "Entry {at} is not visible from conversation {parent_conversation_id}"
        )));
    };

    let mut copies = Vec::new();
    let mut copied_addresses = HashSet::new();
    collect_copies(
        storage,
        entry.entry.conversation_id,
        DocumentPoint::At(entry.commit_seq),
        DocumentFork::AsOf,
        child_conversation_id,
        &mut copies,
        &mut copied_addresses,
        cx,
    )
    .await?;
    collect_copies(
        storage,
        parent_conversation_id,
        DocumentPoint::Current,
        DocumentFork::Current,
        child_conversation_id,
        &mut copies,
        &mut copied_addresses,
        cx,
    )
    .await?;
    Ok(copies)
}

#[expect(
    clippy::too_many_arguments,
    reason = "one-to-one port of the TS helper's parameters"
)]
async fn collect_copies(
    storage: &dyn Storage,
    conversation_id: ConversationId,
    at: DocumentPoint,
    policy: DocumentFork,
    child_conversation_id: ConversationId,
    copies: &mut Vec<ForkDocumentCopy>,
    copied_addresses: &mut HashSet<String>,
    cx: &Context,
) -> SessionResult<()> {
    let mut cursor: Option<Cursor> = None;
    loop {
        let query = DocumentQuery {
            scope: DocumentScope::Conversation { conversation_id },
            at,
            kind: None,
        };
        let page = storage
            .scan_documents(&query, SCAN_PAGE_SIZE, cursor.as_ref(), cx)
            .await?;
        for source in &page.items {
            let DocumentRecordScope::Conversation { semantics, .. } = source.scope else {
                continue;
            };
            if semantics.fork() != policy {
                continue;
            }
            let id = DocumentId::from_number(storage.mint_id().await?);
            let record = DocumentCreate {
                id,
                kind: source.kind.clone(),
                key: source.key.clone(),
                scope: DocumentRecordScope::Conversation {
                    conversation_id: child_conversation_id,
                    semantics,
                },
            };
            let copy_address = address_id(&record_address(&record));
            if !copied_addresses.insert(copy_address) {
                let member = match &record.key {
                    None => record.kind.clone(),
                    Some(key) => format!("{}/{key}", record.kind),
                };
                return Err(SessionError::error(format!(
                    "Fork selects multiple source documents for {member}"
                )));
            }
            copies.push(ForkDocumentCopy {
                record,
                source: DocumentCopySource { id: source.id, at },
            });
        }
        cursor = page.next;
        if cursor.is_none() {
            return Ok(());
        }
    }
}
