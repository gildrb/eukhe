//! Port of `test/session-tables.test.ts`.

use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::JsonValue;

use super::support::{
    assert_error, child, context, create_conversation, document_changes, flush, json,
    open_test_session, work_task, TestSession,
};
use crate::documents::{
    DocDefinition, DocFamilyDefinition, RewindableConversationDoc, TaskDoc, TaskDocFamily,
};
use crate::entries::Entry;
use crate::session::{Session, SessionError, SessionResult, TransactionScope, Tx};
use crate::types::{
    AnyTaskRecord, CommitChange, ConversationId, ConversationOwner, ConversationOwnership,
    ConversationQuery, ConversationRecord, DocumentPoint, DocumentQuery, DocumentScope, EntryDraft,
    EntryHead, EntryId, EntryQuery, Page, RewindableFork, Storage, StorageWrite, TaskId,
    TaskOptions, TaskOutcome, TaskOwnership, TaskQuery, TaskState, TypedEntryDraft,
};

const PROGRESS_DOC: TaskDoc<JsonValue> = match TaskDoc::define(DocDefinition {
    kind: "test.progress",
    version: 1,
    initial: || json(r#"{"lines":[]}"#),
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

const STEP_DOC: TaskDocFamily<JsonValue, JsonValue> =
    match TaskDocFamily::define(DocFamilyDefinition {
        kind: "test.step",
        version: 1,
        initial: |_seed: JsonValue| json(r#"{"lines":[]}"#),
        migrate: None,
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };

const NOTES_DOC: RewindableConversationDoc<JsonValue> = match RewindableConversationDoc::define(
    DocDefinition {
        kind: "test.notes",
        version: 1,
        initial: || json(r#"{"text":""}"#),
        migrate: None,
        checkpoint_when: None,
    },
    RewindableFork::AsOf,
) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

/// Entry kind whose data is a double, so NaN data reaches strict-JSON validation.
const INVALID: Entry<f64> = match Entry::define("invalid") {
    Ok(token) => token,
    Err(_) => panic!("valid entry kind"),
};

/// The TS `null` family seed.
const NULL: JsonValue = JsonValue::Null;

fn terminal(task: &AnyTaskRecord) -> AnyTaskRecord {
    AnyTaskRecord {
        id: task.id,
        conversation_id: task.conversation_id,
        kind: task.kind.clone(),
        version: task.version,
        input: task.input.clone(),
        owner: None,
        background: task.background,
        abort_requested: task.abort_requested,
        state: TaskState::Terminal {
            outcome: TaskOutcome::Completed {
                result: json(r#"{"ok":true}"#),
            },
        },
        memos: None,
    }
}

fn conversation_options(conversation_id: ConversationId) -> TaskOptions {
    TaskOptions {
        ownership: TaskOwnership::Conversation,
        conversation_id: Some(conversation_id),
        background: None,
    }
}

/// `session.commitWith(fn, context)` without a bound scope.
fn commit_with<T, F, Fut>(
    session: &Session,
    change: F,
) -> impl Future<Output = SessionResult<T>> + Send + 'static
where
    T: Send + 'static,
    F: FnOnce(Tx) -> Fut + Send + 'static,
    Fut: Future<Output = SessionResult<T>> + Send + 'static,
{
    session.commit_with(change, context(), TransactionScope::default())
}

async fn create_task(
    session: &Session,
    conversation_id: ConversationId,
    with_document: bool,
) -> TaskId {
    session
        .commit(
            move |tx| async move {
                let task_id = tx
                    .create_task(
                        work_task(),
                        json(r#"{"path":"a"}"#),
                        conversation_options(conversation_id),
                    )
                    .await?;
                if with_document {
                    let progress = tx.doc(&PROGRESS_DOC, task_id).await?;
                    child(&progress, "lines").push([json(r#""started""#)])?;
                }
                Ok(task_id)
            },
            context(),
        )
        .await
        .unwrap()
}

#[track_caller]
fn assert_read_after_write<T: std::fmt::Debug>(result: SessionResult<T>) {
    match result {
        Err(SessionError::ReadAfterWrite(_)) => {}
        other => panic!("expected ReadAfterWrite, got {other:?}"),
    }
}

fn conversation(id: ConversationId) -> ConversationRecord {
    ConversationRecord {
        id,
        parent: None,
        owner: None,
    }
}

#[tokio::test]
async fn allows_table_reads_only_before_the_first_table_write() {
    let TestSession { session, .. } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    session
        .commit(
            move |tx| async move {
                assert_eq!(
                    tx.conversation(conversation_id).await?,
                    Some(conversation(conversation_id))
                );
                assert_eq!(
                    tx.scan_conversations(ConversationQuery::default(), 1, None)
                        .await?,
                    Page {
                        items: vec![conversation(conversation_id)],
                        next: None
                    }
                );
                let tasks = TaskQuery {
                    conversation_id: Some(conversation_id),
                    ..TaskQuery::default()
                };
                assert_eq!(
                    tx.scan_tasks(tasks, 10, None).await?,
                    Page {
                        items: vec![],
                        next: None
                    }
                );
                assert_eq!(
                    tx.scan_entries(EntryQuery::new(conversation_id), 10, None)
                        .await?,
                    Page {
                        items: vec![],
                        next: None
                    }
                );
                tx.append_entry(conversation_id, EntryDraft::new("note"))
                    .await?;
                assert_read_after_write(tx.conversation(conversation_id).await);
                assert_error(
                    tx.task(TaskId::from_number(1)).await,
                    "Tx.task() cannot read tables after the first table write",
                );
                assert_read_after_write(tx.entry(EntryId::from_number(1)).await);
                assert_read_after_write(
                    tx.scan_conversations(ConversationQuery::default(), 10, None)
                        .await,
                );
                assert_read_after_write(
                    tx.scan_entries(EntryQuery::new(conversation_id), 10, None)
                        .await,
                );
                // Document access remains available after table writes.
                tx.doc(&NOTES_DOC, conversation_id)
                    .await?
                    .set("text", "after write")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let snapshot = session
        .snapshot(&NOTES_DOC, conversation_id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        JsonValue::Object(snapshot),
        json(r#"{"text":"after write"}"#)
    );
}

#[tokio::test]
async fn passes_caller_selected_limits_and_cursors_through_table_scans() {
    let TestSession { session, .. } = open_test_session();
    let ids = [
        create_conversation(&session).await,
        create_conversation(&session).await,
        create_conversation(&session).await,
    ];
    session
        .commit(
            move |tx| async move {
                let first = tx
                    .scan_conversations(ConversationQuery::default(), 2, None)
                    .await?;
                assert_eq!(
                    first
                        .items
                        .iter()
                        .map(|record| record.id)
                        .collect::<Vec<_>>(),
                    ids[..2]
                );
                assert!(first.next.is_some());
                let second = tx
                    .scan_conversations(ConversationQuery::default(), 2, first.next)
                    .await?;
                assert_eq!(
                    second
                        .items
                        .iter()
                        .map(|record| record.id)
                        .collect::<Vec<_>>(),
                    ids[2..]
                );
                assert!(second.next.is_none());
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

#[tokio::test]
async fn treats_synchronous_set_task_as_the_first_table_write() {
    let TestSession { session, .. } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    let task_id = create_task(&session, conversation_id, /*with_document*/ false).await;
    commit_with(&session, move |tx| async move {
        let task = tx.task(task_id).await?.expect("task exists");
        tx.set_task(task)?;
        assert_read_after_write(tx.task(task_id).await);
        Ok(())
    })
    .await
    .unwrap();
}

#[tokio::test]
#[allow(clippy::too_many_lines)] // 1:1 port of one long TS case.
async fn creates_conversations_entries_and_tasks_with_minted_ids() {
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();
    let (created_conversation, first, headed, task) = session
        .commit(
            |tx| async move {
                let conversation = tx
                    .create_conversation(ConversationOwnership::Ownerless)
                    .await?;
                let first = tx
                    .append_entry(
                        conversation.id,
                        EntryDraft {
                            data: Some(json(r#""one""#)),
                            ..EntryDraft::new("note")
                        },
                    )
                    .await?;
                let headed = tx
                    .append_entry(
                        conversation.id,
                        EntryDraft {
                            head: Some(EntryHead::SelfEntry),
                            ..EntryDraft::new("summary")
                        },
                    )
                    .await?;
                let task = tx
                    .create_task(
                        work_task(),
                        json(r#"{"path":"x"}"#),
                        TaskOptions {
                            background: Some(true),
                            ..conversation_options(conversation.id)
                        },
                    )
                    .await?;
                Ok((conversation, first, headed, task))
            },
            context(),
        )
        .await
        .unwrap();
    let mut ids = vec![
        created_conversation.id.get(),
        first.id.get(),
        headed.id.get(),
        task.get(),
    ];
    ids.sort_unstable();
    ids.dedup();
    assert_eq!(ids.len(), 4);
    assert_eq!(headed.head, Some(headed.id));
    assert_eq!(
        first,
        crate::types::EntryRecord {
            model: None,
            data: Some(json(r#""one""#)),
            edits: None,
            kind: "note".to_owned(),
            id: first.id,
            conversation_id: created_conversation.id,
            head: None,
            by_task_id: None,
        }
    );
    assert_eq!(
        storage
            .entry(headed.id, context())
            .await
            .unwrap()
            .unwrap()
            .entry,
        headed
    );
    assert_eq!(
        storage.task(task, context()).await.unwrap(),
        Some(AnyTaskRecord {
            id: task,
            conversation_id: created_conversation.id,
            kind: "test.work".to_owned(),
            version: 1,
            input: json(r#"{"path":"x"}"#),
            owner: None,
            background: true,
            abort_requested: false,
            state: TaskState::Pending {
                checkpoint: json(r#"{"phase":"start"}"#),
            },
            memos: None,
        })
    );
    flush().await;
    let changes = publications.last().changes;
    assert_eq!(changes.len(), 4);
    // TS checks reference identity with the admitted batch; Rust storage keeps
    // copies, so each change must equal one admitted write.
    let admitted = storage.admitted_commits().pop().unwrap();
    for change in &changes {
        let write = match change {
            CommitChange::Conversation(value) => StorageWrite::Conversation { value: *value },
            CommitChange::Entry(value) => StorageWrite::Entry {
                value: value.clone(),
            },
            CommitChange::Task(value) => StorageWrite::Task {
                value: value.clone(),
            },
            other => panic!("unexpected change {other:?}"),
        };
        assert!(admitted.contains(&write));
    }
    let mut types = changes
        .iter()
        .map(|change| match change {
            CommitChange::Conversation(_) => "conversation",
            CommitChange::Entry(_) => "entry",
            CommitChange::Task(_) => "task",
            CommitChange::Submission(_) => "submission",
            CommitChange::Document(_) => "document",
        })
        .collect::<Vec<_>>();
    types.sort_unstable();
    assert_eq!(types, ["conversation", "entry", "entry", "task"]);
    assert!(changes
        .iter()
        .any(|change| *change == CommitChange::Conversation(created_conversation)));
    let entries = changes
        .iter()
        .filter_map(|change| match change {
            CommitChange::Entry(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(entries.contains(&first));
    assert!(entries.contains(&headed));
    assert_error(
        session
            .commit(
                |tx| {
                    tx.create_task(
                        work_task(),
                        json(r#"{"path":"x"}"#),
                        TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: None,
                            background: None,
                        },
                    )
                },
                context(),
            )
            .await,
        "requires options.conversationId",
    );
    assert_error(
        session
            .commit(
                |tx| tx.append_entry(ConversationId::from_number(12345), EntryDraft::new("note")),
                context(),
            )
            .await,
        "Conversation 12345 does not exist",
    );
}

#[tokio::test]
async fn creates_a_conversation_with_an_explicitly_staged_task_owner() {
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let parent_id = create_conversation(&session).await;
    let (supervisor_id, created_child) = session
        .commit(
            move |tx| async move {
                let supervisor_id = tx
                    .create_task(
                        work_task(),
                        json(r#"{"path":"background"}"#),
                        TaskOptions {
                            background: Some(true),
                            ..conversation_options(parent_id)
                        },
                    )
                    .await?;
                let child = tx
                    .create_conversation(ConversationOwnership::Task {
                        task_id: supervisor_id,
                    })
                    .await?;
                Ok((supervisor_id, child))
            },
            context(),
        )
        .await
        .unwrap();

    assert_eq!(
        created_child.owner,
        Some(ConversationOwner {
            conversation_id: parent_id,
            task_id: supervisor_id,
        })
    );
    assert_eq!(
        storage
            .conversation(created_child.id, context())
            .await
            .unwrap(),
        Some(created_child)
    );

    assert_error(
        commit_with(&session, move |tx| async move {
            let supervisor = tx.task(supervisor_id).await?.expect("task exists");
            tx.set_task(AnyTaskRecord {
                conversation_id: created_child.id,
                ..supervisor
            })
        })
        .await,
        &format!("Task {supervisor_id} cannot change conversations"),
    );
    assert_eq!(
        storage
            .task(supervisor_id, context())
            .await
            .unwrap()
            .map(|task| task.conversation_id),
        Some(parent_id)
    );
}

fn work_record(
    id: TaskId,
    conversation_id: ConversationId,
    path: &str,
    abort_requested: bool,
    state: TaskState,
) -> AnyTaskRecord {
    AnyTaskRecord {
        id,
        conversation_id,
        kind: "test.work".to_owned(),
        version: 1,
        input: json(&format!(r#"{{"path":"{path}"}}"#)),
        owner: None,
        background: false,
        abort_requested,
        state,
        memos: None,
    }
}

fn start() -> TaskState {
    TaskState::Pending {
        checkpoint: json(r#"{"phase":"start"}"#),
    }
}

#[tokio::test]
#[allow(clippy::too_many_lines)] // 1:1 port of one long TS case.
async fn rejects_missing_terminal_and_abort_marked_conversation_owners_atomically() {
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let parent_id = create_conversation(&session).await;
    let moved_staged_task_id: Arc<Mutex<Option<TaskId>>> = Arc::default();
    let sink = Arc::clone(&moved_staged_task_id);
    assert_error(
        commit_with(&session, move |tx| async move {
            let task_id = tx
                .create_task(
                    work_task(),
                    json(r#"{"path":"move"}"#),
                    conversation_options(parent_id),
                )
                .await?;
            *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(task_id);
            tx.set_task(work_record(
                task_id,
                ConversationId::from_number(998),
                "move",
                /*abort_requested*/ false,
                start(),
            ))
        })
        .await,
        "cannot change conversations",
    );
    let moved_staged_task_id = moved_staged_task_id
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .expect("Expected a staged task ID");
    assert_eq!(
        storage.task(moved_staged_task_id, context()).await.unwrap(),
        None
    );

    let missing_task_id = TaskId::from_number(999);
    assert_error(
        session
            .commit(
                move |tx| {
                    tx.create_conversation(ConversationOwnership::Task {
                        task_id: missing_task_id,
                    })
                },
                context(),
            )
            .await,
        "Conversation owner task 999 does not exist",
    );

    let rejected_child_id: Arc<Mutex<Option<ConversationId>>> = Arc::default();
    let sink = Arc::clone(&rejected_child_id);
    assert_error(
        commit_with(&session, move |tx| async move {
            let supervisor_id = tx
                .create_task(
                    work_task(),
                    json(r#"{"path":"aborting"}"#),
                    conversation_options(parent_id),
                )
                .await?;
            let child = tx
                .create_conversation(ConversationOwnership::Task {
                    task_id: supervisor_id,
                })
                .await?;
            *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(child.id);
            tx.set_task(work_record(
                supervisor_id,
                parent_id,
                "aborting",
                /*abort_requested*/ true,
                start(),
            ))
        })
        .await,
        "is abort-marked",
    );
    let rejected_child_id = rejected_child_id
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .expect("Expected a rejected child ID");
    assert_eq!(
        storage
            .conversation(rejected_child_id, context())
            .await
            .unwrap(),
        None
    );

    assert_error(
        commit_with(&session, move |tx| async move {
            let supervisor_id = tx
                .create_task(
                    work_task(),
                    json(r#"{"path":"terminal"}"#),
                    conversation_options(parent_id),
                )
                .await?;
            tx.create_conversation(ConversationOwnership::Task {
                task_id: supervisor_id,
            })
            .await?;
            tx.set_task(work_record(
                supervisor_id,
                parent_id,
                "terminal",
                /*abort_requested*/ false,
                TaskState::Terminal {
                    outcome: TaskOutcome::Completed {
                        result: json(r#"{"ok":true}"#),
                    },
                },
            ))
        })
        .await,
        "is terminal",
    );

    let terminal_owner_id = create_task(&session, parent_id, /*with_document*/ false).await;
    commit_with(&session, move |tx| async move {
        let task = tx.task(terminal_owner_id).await?.expect("task exists");
        tx.set_task(terminal(&task))
    })
    .await
    .unwrap();
    assert_error(
        session
            .commit(
                move |tx| {
                    tx.create_conversation(ConversationOwnership::Task {
                        task_id: terminal_owner_id,
                    })
                },
                context(),
            )
            .await,
        "is terminal",
    );
}

#[tokio::test]
async fn takes_ownership_of_table_json_and_rejects_non_strict_values() {
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    // TS mutates the payload after appending; Rust JSON values are immutable,
    // so the stored data is checked against the appended value.
    let payload = json(r#"{"nested":{"value":1}}"#);
    let entry = session
        .commit(
            move |tx| async move {
                tx.append_entry(
                    conversation_id,
                    EntryDraft {
                        data: Some(payload),
                        ..EntryDraft::new("data")
                    },
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        storage
            .entry(entry.id, context())
            .await
            .unwrap()
            .unwrap()
            .entry
            .data,
        Some(json(r#"{"nested":{"value":1}}"#))
    );
    // TS `data: undefined` is an absent Rust `data`.
    let omitted = session
        .commit(
            move |tx| tx.append_entry(conversation_id, EntryDraft::new("omitted")),
            context(),
        )
        .await
        .unwrap();
    assert!(omitted.data.is_none());
    assert!(storage
        .entry(omitted.id, context())
        .await
        .unwrap()
        .unwrap()
        .entry
        .data
        .is_none());

    // `JsonValue` cannot hold NaN; a typed entry with NaN data reaches the
    // same strict-JSON rejection.
    let commits = storage.commit_count();
    assert_error(
        session
            .commit(
                move |tx| async move {
                    tx.append_typed_entry(
                        &INVALID,
                        conversation_id,
                        TypedEntryDraft {
                            data: f64::NAN,
                            ..TypedEntryDraft::default()
                        },
                    )
                    .await?;
                    Ok(())
                },
                context(),
            )
            .await,
        "strict JSON",
    );
    assert_eq!(storage.commit_count(), commits);
}

#[tokio::test]
async fn replaces_task_records_completely() {
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    let task_id = create_task(&session, conversation_id, /*with_document*/ false).await;
    commit_with(&session, move |tx| async move {
        let task = tx.task(task_id).await?.expect("task exists");
        tx.set_task(AnyTaskRecord {
            id: task.id,
            conversation_id: task.conversation_id,
            kind: task.kind,
            version: task.version,
            input: task.input,
            owner: None,
            background: task.background,
            abort_requested: task.abort_requested,
            state: TaskState::Running {
                checkpoint: json(r#"{"phase":"next","step":2}"#),
            },
            memos: Some(super::support::object(r#"{"choice":"b"}"#)),
        })
    })
    .await
    .unwrap();
    let stored = storage.task(task_id, context()).await.unwrap().unwrap();
    assert_eq!(
        stored.state,
        TaskState::Running {
            checkpoint: json(r#"{"phase":"next","step":2}"#),
        }
    );
    assert_eq!(
        stored.memos.map(JsonValue::Object),
        Some(json(r#"{"choice":"b"}"#))
    );
}

#[tokio::test]
async fn creates_a_task_and_then_its_document_in_one_transaction_without_read_after_write() {
    let TestSession {
        session,
        publications,
        ..
    } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    let task_id = session
        .commit(
            move |tx| async move {
                let created_task_id = tx
                    .create_task(
                        work_task(),
                        json(r#"{"path":"a"}"#),
                        conversation_options(conversation_id),
                    )
                    .await?;
                // Validation uses the candidate task record, not a caller table read.
                let progress = tx.doc(&PROGRESS_DOC, created_task_id).await?;
                child(&progress, "lines").push([json(r#""created""#)])?;
                let step = tx
                    .doc_member(&STEP_DOC, (created_task_id, "one"), &NULL)
                    .await?;
                child(&step, "lines").push([json(r#""step""#)])?;
                Ok(created_task_id)
            },
            context(),
        )
        .await
        .unwrap();
    let snapshot = session
        .snapshot(&PROGRESS_DOC, task_id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        JsonValue::Object(snapshot),
        json(r#"{"lines":["created"]}"#)
    );
    flush().await;
    let publication = publications.last();
    let documents = document_changes(&publication);
    assert!(publication
        .changes
        .iter()
        .any(|change| matches!(change, CommitChange::Task(task) if task.id == task_id)));
    assert_eq!(documents.len(), 2);
    // Task documents derive their conversation from the task record.
    for document in &documents {
        assert_eq!(document.conversation_id, Some(conversation_id));
    }

    session
        .commit(
            move |tx| async move {
                tx.create_conversation(ConversationOwnership::Ownerless)
                    .await?;
                let progress = tx.doc(&PROGRESS_DOC, task_id).await?;
                child(&progress, "lines").push([json(r#""committed task""#)])?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    assert_eq!(
        document_changes(&publications.last())[0].conversation_id,
        Some(conversation_id)
    );
}

#[tokio::test]
async fn rejects_task_documents_after_a_terminal_candidate() {
    let TestSession { session, .. } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    let task_id = create_task(&session, conversation_id, /*with_document*/ true).await;
    commit_with(&session, move |tx| async move {
        let task = tx.task(task_id).await?.expect("task exists");
        let progress = tx.doc(&PROGRESS_DOC, task_id).await?;
        tx.set_task(terminal(&task))?;
        let expected = format!("Task {task_id} is terminal");
        assert_error(tx.doc(&PROGRESS_DOC, task_id).await.map(|_| ()), &expected);
        assert_error(
            tx.doc_member(&STEP_DOC, (task_id, "late"), &NULL)
                .await
                .map(|_| ()),
            &expected,
        );
        assert_error(tx.set_task(task), "terminal candidate");
        child(&progress, "lines").push([json(r#""final""#)])?;
        Ok(())
    })
    .await
    .unwrap();
    assert_error(
        session
            .commit(
                move |tx| async move {
                    tx.doc(&PROGRESS_DOC, task_id).await?;
                    Ok(())
                },
                context(),
            )
            .await,
        &format!("Task {task_id} is terminal"),
    );
}

#[tokio::test]
#[allow(clippy::too_many_lines)] // 1:1 port of one long TS case.
async fn retires_task_documents_at_terminal_settlement_including_documents_created_in_the_same_transaction(
) {
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    let task_id = create_task(&session, conversation_id, /*with_document*/ true).await;
    session
        .commit(
            move |tx| async move {
                let step = tx
                    .doc_member(&STEP_DOC, (task_id, "committed"), &NULL)
                    .await?;
                child(&step, "lines").push([json(r#""x""#)])?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    let published = publications.len();
    commit_with(&session, move |tx| async move {
        let task = tx.task(task_id).await?.expect("task exists");
        let step = tx.doc_member(&STEP_DOC, (task_id, "new"), &NULL).await?;
        child(&step, "lines").push([json(r#""created then retired""#)])?;
        tx.set_task(terminal(&task))
    })
    .await
    .unwrap();
    let writes = storage.last_commit();
    assert_eq!(writes.len(), 5);
    assert_eq!(
        writes
            .iter()
            .filter(|write| matches!(write, StorageWrite::Task { .. }))
            .count(),
        1
    );
    let creations = writes
        .iter()
        .filter_map(|write| match write {
            StorageWrite::DocumentCreate { record, .. } => Some(record.id),
            _ => None,
        })
        .collect::<Vec<_>>();
    let retirements = writes
        .iter()
        .filter_map(|write| match write {
            StorageWrite::DocumentRetire { id } => Some(*id),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(creations.len(), 1);
    assert_eq!(retirements.len(), 3);
    assert!(retirements.contains(&creations[0]));
    flush().await;
    assert_eq!(publications.len(), published + 1);
    let publication = publications.last();
    let documents = document_changes(&publication);
    assert_eq!(
        publication
            .changes
            .iter()
            .filter(|change| matches!(change, CommitChange::Task(_)))
            .count(),
        1
    );
    assert_eq!(
        documents
            .iter()
            .map(|document| document.value.clone())
            .collect::<Vec<_>>(),
        [None, None, None]
    );
    for document in &documents {
        assert!(document.ops.is_empty());
        assert_eq!(document.conversation_id, Some(conversation_id));
    }
    assert_eq!(
        session
            .snapshot(&PROGRESS_DOC, task_id, context())
            .await
            .unwrap(),
        None
    );
    assert_eq!(
        session
            .snapshot(&STEP_DOC, (task_id, "committed"), context())
            .await
            .unwrap(),
        None
    );
    let query = DocumentQuery {
        scope: DocumentScope::Task { task_id },
        at: DocumentPoint::Current,
        kind: None,
    };
    let alive = storage
        .scan_documents(&query, 10, None, context())
        .await
        .unwrap();
    assert!(alive.items.is_empty());
    assert_error(
        commit_with(&session, move |tx| async move {
            let task = tx.task(task_id).await?.expect("task exists");
            tx.set_task(terminal(&task))
        })
        .await,
        &format!("Task {task_id} is already terminal"),
    );
}

#[tokio::test]
async fn validates_document_owners() {
    let TestSession { session, .. } = open_test_session();
    assert_error(
        session
            .commit(
                |tx| async move {
                    tx.doc(&PROGRESS_DOC, TaskId::from_number(4242)).await?;
                    Ok(())
                },
                context(),
            )
            .await,
        "Task 4242 does not exist",
    );
    assert_error(
        session
            .commit(
                |tx| async move {
                    tx.doc(&NOTES_DOC, ConversationId::from_number(4242))
                        .await?;
                    Ok(())
                },
                context(),
            )
            .await,
        "Conversation 4242 does not exist",
    );
}
