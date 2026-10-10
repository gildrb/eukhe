//! Port of `test/session-forks.test.ts`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::{JsonObject, JsonValue};

use super::support::{
    assert_error, context, create_conversation, document_changes, document_copy_changes, fail,
    flush, json, object, open_test_session, work_task, TestSession,
};
use crate::documents::{
    ConversationDoc, ConversationDocFamily, DocDefinition, DocFamilyDefinition,
    RewindableConversationDoc, RewindableConversationDocFamily, SessionDoc, TaskDoc,
};
use crate::errors::StorageError;
use crate::session::{Session, SessionEnd, SessionError, SessionResult};
use crate::types::{
    ConversationId, ConversationOwnership, ConversationRecord, DocumentAddress, DocumentPoint,
    DocumentRecordScope, DocumentScope, EntryDraft, EntryId, EntryQuery, LatestFork,
    RewindableFork, Storage, StorageWrite, TaskOptions, TaskOwnership,
};

/// `defineDoc` with a JSON literal initial value.
macro_rules! doc {
    ($token:ident, $kind:literal, $init:literal $(, $fork:expr)?) => {
        match $token::define(
            DocDefinition {
                kind: $kind,
                version: 1,
                initial: || json($init),
                migrate: None,
                checkpoint_when: None,
            }
            $(, $fork)?
        ) {
            Ok(token) => token,
            Err(_) => panic!("valid definition"),
        }
    };
}

fn document_creates(writes: &[StorageWrite]) -> Vec<&StorageWrite> {
    writes
        .iter()
        .filter(|write| matches!(write, StorageWrite::DocumentCreate { .. }))
        .collect()
}

fn document_copies(writes: &[StorageWrite]) -> Vec<&StorageWrite> {
    writes
        .iter()
        .filter(|write| matches!(write, StorageWrite::DocumentCopy { .. }))
        .collect()
}

fn count(writes: &[StorageWrite], predicate: fn(&StorageWrite) -> bool) -> usize {
    writes.iter().filter(|write| predicate(write)).count()
}

async fn fork(
    session: &Session,
    parent: ConversationId,
    at: EntryId,
) -> SessionResult<ConversationRecord> {
    session
        .commit(
            move |tx| async move {
                tx.fork_conversation(parent, at, ConversationOwnership::Ownerless)
                    .await
            },
            context(),
        )
        .await
}

async fn create_ownerless(session: &Session) -> ConversationRecord {
    session
        .commit(
            |tx| async move {
                tx.create_conversation(ConversationOwnership::Ownerless)
                    .await
            },
            context(),
        )
        .await
        .unwrap()
}

fn conversation_address(kind: &str, conversation_id: ConversationId) -> DocumentAddress {
    DocumentAddress {
        kind: kind.to_owned(),
        scope: DocumentScope::Conversation { conversation_id },
        key: None,
    }
}

/// A present snapshot value (TS `toEqual({...})` against `snapshot`).
#[allow(clippy::unnecessary_wraps)]
fn value(text: &str) -> Option<Arc<JsonObject>> {
    Some(object(text))
}

#[tokio::test]
#[allow(clippy::too_many_lines)]
async fn copies_as_of_and_current_singleton_and_family_bases_while_leaving_initial_documents_absent(
) {
    const AS_OF: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.policies.as-of",
        r#"{"value":"as-initial"}"#,
        RewindableFork::AsOf
    );
    const CURRENT: ConversationDoc<JsonValue> = doc!(
        ConversationDoc,
        "fork.policies.current",
        r#"{"value":"current-initial"}"#,
        LatestFork::Current
    );
    const INITIAL: ConversationDoc<JsonValue> = doc!(
        ConversationDoc,
        "fork.policies.initial",
        r#"{"value":"fresh"}"#,
        LatestFork::Initial
    );
    const AS_OF_FAMILY: RewindableConversationDocFamily<JsonValue, String> =
        match RewindableConversationDocFamily::define(
            DocFamilyDefinition {
                kind: "fork.policies.as-of-family",
                version: 1,
                initial: |seed: String| json(&format!(r#"{{"value":{seed:?}}}"#)),
                migrate: None,
                checkpoint_when: None,
            },
            RewindableFork::AsOf,
        ) {
            Ok(token) => token,
            Err(_) => panic!("valid definition"),
        };
    const CURRENT_FAMILY: ConversationDocFamily<JsonValue, String> =
        match ConversationDocFamily::define(
            DocFamilyDefinition {
                kind: "fork.policies.current-family",
                version: 1,
                initial: |seed: String| json(&format!(r#"{{"value":{seed:?}}}"#)),
                migrate: None,
                checkpoint_when: None,
            },
            LatestFork::Current,
        ) {
            Ok(token) => token,
            Err(_) => panic!("valid definition"),
        };
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();
    let parent_id = create_conversation(&session).await;
    let unused = "unused".to_owned();
    let fork_at = session
        .commit(
            move |tx| async move {
                let id = tx
                    .append_entry(parent_id, EntryDraft::new("fork-point"))
                    .await?
                    .id;
                tx.doc(&AS_OF, parent_id)
                    .await?
                    .set("value", "as-at-fork")?;
                tx.doc(&CURRENT, parent_id)
                    .await?
                    .set("value", "current-at-fork")?;
                tx.doc(&INITIAL, parent_id)
                    .await?
                    .set("value", "parent-only")?;
                tx.doc_member(&AS_OF_FAMILY, (parent_id, "a"), &unused)
                    .await?
                    .set("value", "family-as-a")?;
                tx.doc_member(&AS_OF_FAMILY, (parent_id, "b"), &unused)
                    .await?
                    .set("value", "family-as-b")?;
                tx.doc_member(&CURRENT_FAMILY, (parent_id, "a"), &unused)
                    .await?
                    .set("value", "family-current-a")?;
                Ok(id)
            },
            context(),
        )
        .await
        .unwrap();
    let unused = "unused".to_owned();
    session
        .commit(
            move |tx| async move {
                tx.doc(&AS_OF, parent_id)
                    .await?
                    .set("value", "as-after-fork")?;
                tx.doc(&CURRENT, parent_id)
                    .await?
                    .set("value", "current-when-copied")?;
                tx.doc_member(&AS_OF_FAMILY, (parent_id, "a"), &unused)
                    .await?
                    .set("value", "family-as-after")?;
                tx.doc_member(&CURRENT_FAMILY, (parent_id, "a"), &unused)
                    .await?
                    .set("value", "family-current-when-copied")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    let document_reads = storage.document_read_count();

    let child = fork(&session, parent_id, fork_at).await.unwrap();
    flush().await;
    assert_eq!(storage.document_read_count(), document_reads);

    let cx = context();
    assert_eq!(
        session.snapshot(&AS_OF, child.id, cx).await.unwrap(),
        value(r#"{"value":"as-at-fork"}"#)
    );
    assert_eq!(
        session.snapshot(&CURRENT, child.id, cx).await.unwrap(),
        value(r#"{"value":"current-when-copied"}"#)
    );
    assert_eq!(
        session.snapshot(&INITIAL, child.id, cx).await.unwrap(),
        None
    );
    assert_eq!(
        session
            .snapshot(&AS_OF_FAMILY, (child.id, "a"), cx)
            .await
            .unwrap(),
        value(r#"{"value":"family-as-a"}"#)
    );
    assert_eq!(
        session
            .snapshot(&AS_OF_FAMILY, (child.id, "b"), cx)
            .await
            .unwrap(),
        value(r#"{"value":"family-as-b"}"#)
    );
    assert_eq!(
        session
            .snapshot(&CURRENT_FAMILY, (child.id, "a"), cx)
            .await
            .unwrap(),
        value(r#"{"value":"family-current-when-copied"}"#)
    );

    let admitted = storage.admitted_commits().pop().unwrap();
    let copies = document_copies(&admitted);
    assert_eq!(copies.len(), 5);
    assert!(copies.iter().all(|write| matches!(
        write,
        StorageWrite::DocumentCopy {
            record: crate::types::DocumentCreate {
                scope: DocumentRecordScope::Conversation { .. },
                ..
            },
            ..
        }
    )));
    assert!(copies.iter().all(|write| matches!(
        write,
        StorageWrite::DocumentCopy {
            record: crate::types::DocumentCreate {
                scope: DocumentRecordScope::Conversation { conversation_id, .. },
                ..
            },
            ..
        } if *conversation_id == child.id
    )));
    let publication = publications.last();
    let copy_changes = document_copy_changes(&publication);
    assert_eq!(copy_changes.len(), 5);
    for change in copy_changes {
        assert_eq!(change.record.created_at, publication.seq);
        assert_eq!(change.conversation_id, child.id);
        let source = copies
            .iter()
            .find_map(|candidate| match candidate {
                StorageWrite::DocumentCopy { record, source } if record.id == change.record.id => {
                    Some(*source)
                }
                _ => None,
            })
            .unwrap();
        assert_eq!(change.source, source);
    }

    let parent_address = conversation_address(AS_OF.definition().kind, parent_id);
    let parent_record = storage
        .find_document(&parent_address, DocumentPoint::Current, cx)
        .await
        .unwrap();
    let child_address = conversation_address(AS_OF.definition().kind, child.id);
    let child_record = storage
        .find_document(&child_address, DocumentPoint::Current, cx)
        .await
        .unwrap();
    assert_ne!(child_record.unwrap().id, parent_record.unwrap().id);

    let child_id = child.id;
    session
        .commit(
            move |tx| async move {
                tx.doc(&AS_OF, child_id)
                    .await?
                    .set("value", "child-independent")?;
                Ok(())
            },
            cx,
        )
        .await
        .unwrap();
    assert_eq!(
        session.snapshot(&AS_OF, parent_id, cx).await.unwrap(),
        value(r#"{"value":"as-after-fork"}"#)
    );
    assert_eq!(
        session.snapshot(&AS_OF, child_id, cx).await.unwrap(),
        value(r#"{"value":"child-independent"}"#)
    );
    session
        .commit(
            move |tx| async move {
                tx.doc(&INITIAL, child_id)
                    .await?
                    .set("value", "child-created")?;
                Ok(())
            },
            cx,
        )
        .await
        .unwrap();
    assert_eq!(
        session.snapshot(&INITIAL, child_id, cx).await.unwrap(),
        value(r#"{"value":"child-created"}"#)
    );
}

#[tokio::test]
async fn uses_final_document_state_from_the_fork_entry_commit_while_excluding_later_same_commit_entries(
) {
    const DOC: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.same-commit",
        r#"{"value":"initial"}"#,
        RewindableFork::AsOf
    );
    let TestSession { session, .. } = open_test_session();
    let parent_id = create_conversation(&session).await;
    let (fork_at, excluded) = session
        .commit(
            move |tx| async move {
                let fork_at = tx
                    .append_entry(parent_id, EntryDraft::new("included"))
                    .await?
                    .id;
                tx.doc(&DOC, parent_id)
                    .await?
                    .set("value", "final-state-of-commit")?;
                let excluded = tx
                    .append_entry(parent_id, EntryDraft::new("excluded"))
                    .await?
                    .id;
                Ok((fork_at, excluded))
            },
            context(),
        )
        .await
        .unwrap();
    let child = fork(&session, parent_id, fork_at).await.unwrap();
    assert_eq!(
        session.snapshot(&DOC, child.id, context()).await.unwrap(),
        value(r#"{"value":"final-state-of-commit"}"#)
    );
    let child_id = child.id;
    let visible = session
        .commit(
            move |tx| async move { tx.scan_entries(EntryQuery::new(child_id), 10, None).await },
            context(),
        )
        .await
        .unwrap();
    let ids: Vec<EntryId> = visible.items.iter().map(|entry| entry.id).collect();
    assert!(ids.contains(&fork_at));
    assert!(!ids.contains(&excluded));
}

#[tokio::test]
async fn selects_the_entry_owning_ancestor_for_as_of_copies_and_the_immediate_parent_for_current_copies(
) {
    const AS_OF: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.ancestry.as-of",
        r#"{"value":"initial"}"#,
        RewindableFork::AsOf
    );
    const CURRENT: ConversationDoc<JsonValue> = doc!(
        ConversationDoc,
        "fork.ancestry.current",
        r#"{"value":"initial"}"#,
        LatestFork::Current
    );
    let TestSession { session, .. } = open_test_session();
    let cx = context();
    let root_id = create_conversation(&session).await;
    let inherited = session
        .commit(
            move |tx| async move {
                let id = tx.append_entry(root_id, EntryDraft::new("root")).await?.id;
                tx.doc(&AS_OF, root_id)
                    .await?
                    .set("value", "root-at-entry")?;
                tx.doc(&CURRENT, root_id)
                    .await?
                    .set("value", "root-current")?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();
    let parent = fork(&session, root_id, inherited).await.unwrap();
    let parent_id = parent.id;
    let parent_entry = session
        .commit(
            move |tx| async move {
                let id = tx
                    .append_entry(parent_id, EntryDraft::new("parent"))
                    .await?
                    .id;
                tx.doc(&AS_OF, parent_id)
                    .await?
                    .set("value", "parent-at-own-entry")?;
                tx.doc(&CURRENT, parent_id)
                    .await?
                    .set("value", "parent-current")?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();

    let inherited_fork = fork(&session, parent_id, inherited).await.unwrap();
    assert_eq!(
        session
            .snapshot(&AS_OF, inherited_fork.id, cx)
            .await
            .unwrap(),
        value(r#"{"value":"root-at-entry"}"#)
    );
    assert_eq!(
        session
            .snapshot(&CURRENT, inherited_fork.id, cx)
            .await
            .unwrap(),
        value(r#"{"value":"parent-current"}"#)
    );

    let own_entry_fork = fork(&session, parent_id, parent_entry).await.unwrap();
    assert_eq!(
        session
            .snapshot(&AS_OF, own_entry_fork.id, cx)
            .await
            .unwrap(),
        value(r#"{"value":"parent-at-own-entry"}"#)
    );
    assert_eq!(
        session
            .snapshot(&CURRENT, own_entry_fork.id, cx)
            .await
            .unwrap(),
        value(r#"{"value":"parent-current"}"#)
    );
}

#[tokio::test]
async fn copies_the_stored_value_and_version_without_consulting_migration_definitions_or_migrated_caches(
) {
    static MIGRATIONS: AtomicUsize = AtomicUsize::new(0);
    const V1: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.stored-version",
        r#"{"count":1}"#,
        RewindableFork::AsOf
    );
    const V3: RewindableConversationDoc<JsonValue> = match RewindableConversationDoc::define(
        DocDefinition {
            kind: "fork.stored-version",
            version: 3,
            initial: || json(r#"{"count":0,"migrated":false}"#),
            migrate: Some(|value, from_version| {
                assert_eq!(from_version, 1);
                MIGRATIONS.fetch_add(1, Ordering::SeqCst);
                Ok(json(&format!(
                    r#"{{"count":{},"migrated":true}}"#,
                    value.get("count").cloned().unwrap_or(JsonValue::Null)
                )))
            }),
            checkpoint_when: None,
        },
        RewindableFork::AsOf,
    ) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let cx = context();
    let parent_id = create_conversation(&session).await;
    let fork_at = session
        .commit(
            move |tx| async move {
                let id = tx
                    .append_entry(parent_id, EntryDraft::new("point"))
                    .await?
                    .id;
                tx.doc(&V1, parent_id).await?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();
    session.unload_documents().await.unwrap();
    assert_eq!(
        session.snapshot(&V3, parent_id, cx).await.unwrap(),
        value(r#"{"count":1,"migrated":true}"#)
    );
    assert_eq!(MIGRATIONS.load(Ordering::SeqCst), 1);

    let child = fork(&session, parent_id, fork_at).await.unwrap();
    assert_eq!(MIGRATIONS.load(Ordering::SeqCst), 1);
    let address = conversation_address(V1.definition().kind, child.id);
    let child_record = storage
        .find_document(&address, DocumentPoint::Current, cx)
        .await
        .unwrap()
        .unwrap();
    let child_stored = storage
        .document(child_record.id, DocumentPoint::Current, cx)
        .await
        .unwrap()
        .unwrap();
    assert_eq!(child_stored.version, 1);
    assert_eq!(child_stored.value, object(r#"{"count":1}"#));
    assert_eq!(
        session.snapshot(&V3, child.id, cx).await.unwrap(),
        value(r#"{"count":1,"migrated":true}"#)
    );
    assert_eq!(MIGRATIONS.load(Ordering::SeqCst), 2);
}

#[tokio::test]
async fn coalesces_a_typed_migration_and_override_into_the_copied_creation_base() {
    static CHECKPOINTS: AtomicUsize = AtomicUsize::new(0);
    const V1: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.override",
        r#"{"count":2}"#,
        RewindableFork::AsOf
    );
    const V2: RewindableConversationDoc<JsonValue> = match RewindableConversationDoc::define(
        DocDefinition {
            kind: "fork.override",
            version: 2,
            initial: || json(r#"{"count":0,"migrated":false}"#),
            migrate: Some(|value, _from| {
                Ok(json(&format!(
                    r#"{{"count":{},"migrated":true}}"#,
                    value.get("count").cloned().unwrap_or(JsonValue::Null)
                )))
            }),
            checkpoint_when: Some(|_value, _ops, _info| {
                CHECKPOINTS.fetch_add(1, Ordering::SeqCst);
                false
            }),
        },
        RewindableFork::AsOf,
    ) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();
    let cx = context();
    let parent_id = create_conversation(&session).await;
    let fork_at = session
        .commit(
            move |tx| async move {
                let id = tx
                    .append_entry(parent_id, EntryDraft::new("point"))
                    .await?
                    .id;
                tx.doc(&V1, parent_id).await?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();

    let document_reads = storage.document_read_count();
    let child = session
        .commit(
            move |tx| async move {
                let created = tx
                    .fork_conversation(parent_id, fork_at, ConversationOwnership::Ownerless)
                    .await?;
                tx.doc(&V2, created.id).await?.set("count", 9)?;
                Ok(created)
            },
            cx,
        )
        .await
        .unwrap();
    flush().await;
    assert_eq!(storage.document_read_count(), document_reads + 1);
    let admitted = storage.admitted_commits().pop().unwrap();
    let creates = document_creates(&admitted);
    assert_eq!(creates.len(), 1);
    // TS `kind: "base"` is the `DocumentBase` content type itself.
    let StorageWrite::DocumentCreate { content, .. } = creates[0] else {
        unreachable!()
    };
    assert_eq!(content.version, 2);
    assert_eq!(content.value, object(r#"{"count":9,"migrated":true}"#));
    assert_eq!(CHECKPOINTS.load(Ordering::SeqCst), 0);
    let changes = document_changes(&publications.last());
    assert_eq!(changes.len(), 1);
    assert_eq!(changes[0].version, Some(2));
    assert_eq!(
        session.snapshot(&V2, child.id, cx).await.unwrap(),
        value(r#"{"count":9,"migrated":true}"#)
    );
    let address = conversation_address(V1.definition().kind, parent_id);
    let parent_record = storage
        .find_document(&address, DocumentPoint::Current, cx)
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        storage
            .document(parent_record.id, DocumentPoint::Current, cx)
            .await
            .unwrap()
            .unwrap()
            .version,
        1
    );
}

#[tokio::test]
async fn copies_the_incarnation_alive_at_the_fork_point_across_retirement_and_recreation() {
    const DOC: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.incarnations",
        r#"{"value":"initial"}"#,
        RewindableFork::AsOf
    );
    let TestSession { session, .. } = open_test_session();
    let cx = context();
    let parent_id = create_conversation(&session).await;
    let old_at = session
        .commit(
            move |tx| async move {
                let id = tx.append_entry(parent_id, EntryDraft::new("old")).await?.id;
                tx.doc(&DOC, parent_id).await?.set("value", "old")?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();
    let retired_at = session
        .commit(
            move |tx| async move {
                let id = tx
                    .append_entry(parent_id, EntryDraft::new("retired"))
                    .await?
                    .id;
                tx.retire_doc(&DOC, parent_id).await?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();
    let new_at = session
        .commit(
            move |tx| async move {
                let id = tx.append_entry(parent_id, EntryDraft::new("new")).await?.id;
                tx.doc(&DOC, parent_id).await?.set("value", "new")?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();

    let old_child = fork(&session, parent_id, old_at).await.unwrap();
    let empty_child = fork(&session, parent_id, retired_at).await.unwrap();
    let new_child = fork(&session, parent_id, new_at).await.unwrap();
    assert_eq!(
        session.snapshot(&DOC, old_child.id, cx).await.unwrap(),
        value(r#"{"value":"old"}"#)
    );
    assert_eq!(
        session.snapshot(&DOC, empty_child.id, cx).await.unwrap(),
        None
    );
    assert_eq!(
        session.snapshot(&DOC, new_child.id, cx).await.unwrap(),
        value(r#"{"value":"new"}"#)
    );
}

#[tokio::test]
async fn rejects_invisible_fork_points_before_admission_and_remains_usable() {
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();
    let root_id = create_conversation(&session).await;
    let (visible, hidden) = session
        .commit(
            move |tx| async move {
                let visible = tx
                    .append_entry(root_id, EntryDraft::new("visible"))
                    .await?
                    .id;
                let hidden = tx
                    .append_entry(root_id, EntryDraft::new("hidden"))
                    .await?
                    .id;
                Ok((visible, hidden))
            },
            context(),
        )
        .await
        .unwrap();
    let parent = fork(&session, root_id, visible).await.unwrap();
    flush().await;
    let commits = storage.commit_count();
    let published = publications.len();
    assert_error(
        fork(&session, parent.id, hidden).await,
        &format!("Entry {hidden} is not visible"),
    );
    flush().await;
    assert_eq!(storage.commit_count(), commits);
    assert_eq!(publications.len(), published);
    let independent = create_ownerless(&session).await;
    assert_eq!(
        storage
            .conversation(independent.id, context())
            .await
            .unwrap(),
        Some(independent)
    );
}

#[tokio::test]
async fn rejects_duplicate_as_of_and_current_selections_for_one_child_address_before_admission() {
    const AS_OF: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.duplicate-policy",
        r#"{"value":"as-of"}"#,
        RewindableFork::AsOf
    );
    const CURRENT: ConversationDoc<JsonValue> = doc!(
        ConversationDoc,
        "fork.duplicate-policy",
        r#"{"value":"current"}"#,
        LatestFork::Current
    );
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let cx = context();
    let parent_id = create_conversation(&session).await;
    let old_at = session
        .commit(
            move |tx| async move {
                let id = tx.append_entry(parent_id, EntryDraft::new("old")).await?.id;
                tx.doc(&AS_OF, parent_id).await?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();
    session
        .commit(
            move |tx| async move { tx.retire_doc(&AS_OF, parent_id).await },
            cx,
        )
        .await
        .unwrap();
    session
        .commit(
            move |tx| async move {
                tx.doc(&CURRENT, parent_id).await?;
                Ok(())
            },
            cx,
        )
        .await
        .unwrap();
    let commits = storage.commit_count();
    assert_error(
        fork(&session, parent_id, old_at).await,
        "Fork selects multiple source documents",
    );
    assert_eq!(storage.commit_count(), commits);
    let independent = create_ownerless(&session).await;
    assert_eq!(
        storage.conversation(independent.id, cx).await.unwrap(),
        Some(independent)
    );
}

#[tokio::test]
async fn rejects_current_and_as_of_source_writes_in_the_fork_transaction() {
    const CURRENT: ConversationDoc<JsonValue> = doc!(
        ConversationDoc,
        "fork.same-transaction-current",
        r#"{"value":"committed"}"#,
        LatestFork::Current
    );
    const AS_OF: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.same-transaction-as-of",
        r#"{"value":"committed"}"#,
        RewindableFork::AsOf
    );
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let cx = context();
    let parent_id = create_conversation(&session).await;
    let fork_at = session
        .commit(
            move |tx| async move {
                let id = tx
                    .append_entry(parent_id, EntryDraft::new("point"))
                    .await?
                    .id;
                tx.doc(&CURRENT, parent_id).await?;
                tx.doc(&AS_OF, parent_id).await?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();
    let commits = storage.commit_count();
    assert_error(
        session
            .commit(
                move |tx| async move {
                    tx.doc(&CURRENT, parent_id)
                        .await?
                        .set("value", "before-fork")?;
                    tx.fork_conversation(parent_id, fork_at, ConversationOwnership::Ownerless)
                        .await?;
                    Ok(())
                },
                cx,
            )
            .await,
        "Cannot change fork source document",
    );
    assert_error(
        session
            .commit(
                move |tx| async move {
                    tx.fork_conversation(parent_id, fork_at, ConversationOwnership::Ownerless)
                        .await?;
                    tx.doc(&CURRENT, parent_id)
                        .await?
                        .set("value", "after-fork")?;
                    Ok(())
                },
                cx,
            )
            .await,
        "Cannot change fork source document",
    );
    assert_error(
        session
            .commit(
                move |tx| async move {
                    tx.doc(&AS_OF, parent_id)
                        .await?
                        .set("value", "as-of-write")?;
                    tx.fork_conversation(parent_id, fork_at, ConversationOwnership::Ownerless)
                        .await?;
                    Ok(())
                },
                cx,
            )
            .await,
        "Cannot change fork source document",
    );
    assert_eq!(storage.commit_count(), commits);
    assert_eq!(
        session.snapshot(&CURRENT, parent_id, cx).await.unwrap(),
        value(r#"{"value":"committed"}"#)
    );
    let child = fork(&session, parent_id, fork_at).await.unwrap();
    assert_eq!(
        session.snapshot(&CURRENT, child.id, cx).await.unwrap(),
        value(r#"{"value":"committed"}"#)
    );
}

/// TS throws from `checkpointWhen` during pre-admission assembly; Rust's
/// `CheckpointWhenFn` returns `bool` and cannot fail, so the commit fails
/// with the same message after staging the copies and the `Failure` change.
#[tokio::test]
async fn rolls_every_copied_base_back_when_later_pre_admission_assembly_fails() {
    const COPIED: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.rollback.copied",
        r#"{"value":"copied"}"#,
        RewindableFork::AsOf
    );
    const FAILURE: SessionDoc<JsonValue> =
        doc!(SessionDoc, "fork.rollback.failure", r#"{"count":0}"#);
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();
    let cx = context();
    let parent_id = create_conversation(&session).await;
    let fork_at = session
        .commit(
            move |tx| async move {
                let id = tx
                    .append_entry(parent_id, EntryDraft::new("point"))
                    .await?
                    .id;
                tx.doc(&COPIED, parent_id).await?;
                tx.doc(&FAILURE, ()).await?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();
    flush().await;
    let commits = storage.commit_count();
    let published = publications.len();
    let child_id = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&child_id);
    assert_error(
        session
            .commit(
                move |tx| async move {
                    let created = tx
                        .fork_conversation(parent_id, fork_at, ConversationOwnership::Ownerless)
                        .await?;
                    *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(created.id);
                    tx.doc(&FAILURE, ()).await?.set("count", 1)?;
                    fail::<()>("checkpoint failed")
                },
                cx,
            )
            .await,
        "checkpoint failed",
    );
    flush().await;
    assert_eq!(storage.commit_count(), commits);
    assert_eq!(publications.len(), published);
    let child_id = child_id
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .unwrap();
    assert_eq!(storage.conversation(child_id, cx).await.unwrap(), None);
    session
        .commit(
            |tx| async move {
                tx.doc(&FAILURE, ()).await?.set("count", 2)?;
                Ok(())
            },
            cx,
        )
        .await
        .unwrap();
    assert_eq!(
        session.snapshot(&FAILURE, (), cx).await.unwrap(),
        value(r#"{"count":2}"#)
    );
    assert_eq!(
        session.snapshot(&COPIED, parent_id, cx).await.unwrap(),
        value(r#"{"value":"copied"}"#)
    );
}

#[tokio::test]
async fn fails_the_session_on_a_rejected_fork_commit_which_leaves_no_effect() {
    const DOC: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.storage-rejected",
        r#"{"value":"source"}"#,
        RewindableFork::AsOf
    );
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let cx = context();
    let parent_id = create_conversation(&session).await;
    let fork_at = session
        .commit(
            move |tx| async move {
                let id = tx
                    .append_entry(parent_id, EntryDraft::new("point"))
                    .await?
                    .id;
                tx.doc(&DOC, parent_id).await?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();
    let rejected_child_id = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&rejected_child_id);
    storage.fail_next_commit(StorageError::failed(TestFailure("copy rejected")));
    assert_error(
        session
            .commit(
                move |tx| async move {
                    let created = tx
                        .fork_conversation(parent_id, fork_at, ConversationOwnership::Ownerless)
                        .await?;
                    *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(created.id);
                    Ok(())
                },
                cx,
            )
            .await,
        "copy rejected",
    );
    let rejected_child_id = rejected_child_id
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .unwrap();
    let created = session
        .commit(
            |tx| async move {
                tx.create_conversation(ConversationOwnership::Ownerless)
                    .await
            },
            cx,
        )
        .await;
    match created {
        Err(SessionError::Failed(failed)) => {
            assert_eq!(failed.cause().to_string(), "copy rejected");
        }
        other => panic!("expected SessionFailed, got {other:?}"),
    }
    // The failed Session closed its Storage; reopened, it holds nothing of the batch.
    assert!(matches!(
        session.closed().await,
        SessionEnd::Failed { error } if error.to_string() == "copy rejected"
    ));
    assert_eq!(
        storage
            .reopen()
            .conversation(rejected_child_id, cx)
            .await
            .unwrap(),
        None
    );
}

/// A test failure with a fixed message.
#[derive(Debug, thiserror::Error)]
#[error("{0}")]
struct TestFailure(&'static str);

#[tokio::test]
async fn retires_a_copied_document_and_can_recreate_the_address_in_the_fork_transaction() {
    const DOC: RewindableConversationDoc<JsonValue> = doc!(
        RewindableConversationDoc,
        "fork.retire-recreate",
        r#"{"value":"fresh"}"#,
        RewindableFork::AsOf
    );
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let cx = context();
    let parent_id = create_conversation(&session).await;
    let fork_at = session
        .commit(
            move |tx| async move {
                let id = tx
                    .append_entry(parent_id, EntryDraft::new("point"))
                    .await?
                    .id;
                tx.doc(&DOC, parent_id).await?.set("value", "copied")?;
                Ok(id)
            },
            cx,
        )
        .await
        .unwrap();
    let child = session
        .commit(
            move |tx| async move {
                let created = tx
                    .fork_conversation(parent_id, fork_at, ConversationOwnership::Ownerless)
                    .await?;
                tx.retire_doc(&DOC, created.id).await?;
                tx.doc(&DOC, created.id)
                    .await?
                    .set("value", "replacement")?;
                Ok(created)
            },
            cx,
        )
        .await
        .unwrap();
    let writes = storage.last_commit();
    assert_eq!(
        count(&writes, |write| matches!(
            write,
            StorageWrite::DocumentCopy { .. }
        )),
        1
    );
    assert_eq!(
        count(&writes, |write| matches!(
            write,
            StorageWrite::DocumentCreate { .. }
        )),
        1
    );
    assert_eq!(
        count(&writes, |write| matches!(
            write,
            StorageWrite::DocumentRetire { .. }
        )),
        1
    );
    assert_eq!(
        session.snapshot(&DOC, child.id, cx).await.unwrap(),
        value(r#"{"value":"replacement"}"#)
    );
}

/// TS defines a dedicated `fork.scope.work` task; the shared `test.work`
/// definition is equivalent here (the task only owns a document).
#[tokio::test]
async fn copies_only_conversation_documents_leaving_session_and_task_documents_in_their_original_scopes(
) {
    const COPIED: ConversationDoc<JsonValue> = doc!(
        ConversationDoc,
        "fork.scope.conversation",
        r#"{"value":"conversation"}"#,
        LatestFork::Current
    );
    const SESSION_ONLY: SessionDoc<JsonValue> =
        doc!(SessionDoc, "fork.scope.session", r#"{"value":"session"}"#);
    const TASK_ONLY: TaskDoc<JsonValue> = doc!(TaskDoc, "fork.scope.task", r#"{"value":"task"}"#);
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();
    let cx = context();
    let parent_id = create_conversation(&session).await;
    let (fork_at, task_id) = session
        .commit(
            move |tx| async move {
                let fork_at = tx
                    .append_entry(parent_id, EntryDraft::new("point"))
                    .await?
                    .id;
                let task_id = tx
                    .create_task(
                        work_task(),
                        JsonValue::Null,
                        TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: Some(parent_id),
                            background: None,
                            abandon_on_restart: None,
                        },
                    )
                    .await?;
                tx.doc(&COPIED, parent_id).await?;
                tx.doc(&SESSION_ONLY, ()).await?;
                tx.doc(&TASK_ONLY, task_id).await?;
                Ok((fork_at, task_id))
            },
            cx,
        )
        .await
        .unwrap();
    let child = fork(&session, parent_id, fork_at).await.unwrap();
    flush().await;
    let last = storage.last_commit();
    let kinds: Vec<&str> = document_copies(&last)
        .into_iter()
        .filter_map(|write| match write {
            StorageWrite::DocumentCopy { record, .. } => Some(record.kind.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(kinds, [COPIED.definition().kind]);
    let published: Vec<String> = document_copy_changes(&publications.last())
        .into_iter()
        .map(|change| change.record.kind)
        .collect();
    assert_eq!(published, [COPIED.definition().kind]);
    assert_eq!(
        session.snapshot(&COPIED, child.id, cx).await.unwrap(),
        value(r#"{"value":"conversation"}"#)
    );
    assert_eq!(
        session.snapshot(&SESSION_ONLY, (), cx).await.unwrap(),
        value(r#"{"value":"session"}"#)
    );
    assert_eq!(
        session.snapshot(&TASK_ONLY, task_id, cx).await.unwrap(),
        value(r#"{"value":"task"}"#)
    );
}

#[tokio::test]
async fn copies_every_family_member_across_storage_scan_pages() {
    const FAMILY: ConversationDocFamily<JsonValue, u64> = match ConversationDocFamily::define(
        DocFamilyDefinition {
            kind: "fork.pagination",
            version: 1,
            initial: |seed: u64| json(&format!(r#"{{"value":{seed}}}"#)),
            migrate: None,
            checkpoint_when: None,
        },
        LatestFork::Current,
    ) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let cx = context();
    let parent_id = create_conversation(&session).await;
    let fork_at = session
        .commit(
            move |tx| async move {
                Ok(tx
                    .append_entry(parent_id, EntryDraft::new("point"))
                    .await?
                    .id)
            },
            cx,
        )
        .await
        .unwrap();
    session
        .commit(
            move |tx| async move {
                futures::future::try_join_all((0..260_u64).map(|index| {
                    let key = format!("member-{index}");
                    tx.doc_member(&FAMILY, (parent_id, key.as_str()), &index)
                }))
                .await?;
                Ok(())
            },
            cx,
        )
        .await
        .unwrap();
    let child = fork(&session, parent_id, fork_at).await.unwrap();
    assert_eq!(document_copies(&storage.last_commit()).len(), 260);
    assert_eq!(
        session
            .snapshot(&FAMILY, (child.id, "member-0"), cx)
            .await
            .unwrap(),
        value(r#"{"value":0}"#)
    );
    assert_eq!(
        session
            .snapshot(&FAMILY, (child.id, "member-259"), cx)
            .await
            .unwrap(),
        value(r#"{"value":259}"#)
    );
}
