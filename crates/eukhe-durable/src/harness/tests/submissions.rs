//! Port of `test/harness-submissions.test.ts`.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use eukhe_chord::context::{with_cancel, Context};
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, FauxAssistantMessageOptions, FauxResponseStep,
    RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{AssistantMessage, Message, UserContent, UserMessage};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::{Deserialize, Serialize};

use super::chat_support::{all_entries, chat_setup, open_chat, unanswered, OpenChat};
use super::support::{context, generation_task};
use super::task_support::{deferred, Deferred};
use crate::entries::{Entry, ASSISTANT_ENTRY, USER_ENTRY};
use crate::errors::{ConversationBusy, StorageError};
use crate::harness::live::{LiveState, LIVE_DOC};
use crate::harness::types::{
    ConversationCreateOptions, InputSubmissionDraft, SubmissionAbort, WhenBusy,
    WriteSubmissionDraft,
};
use crate::harness::AbortSubmissionResult;
use crate::session::tests::support::ControlledStorage;
use crate::session::SessionError;
use crate::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationOwnership, ConversationQuery, ConversationRecord,
    Cursor, DocumentAddress, DocumentId, DocumentPoint, DocumentQuery, DocumentRecord, EntryDraft,
    EntryId, EntryQuery, EntryRecord, InputSubmission, Page, Seq, Storage, StorageWrite,
    StoredDocument, StoredEntry, SubmissionCreate, SubmissionId, SubmissionQuery, SubmissionRecord,
    SubmissionSettlement, SubmissionState, SubmissionStatus, TaskId, TaskOptions, TaskOwnership,
    TaskQuery, TaskStatus, TypedEntryDraft, WriteSubmission,
};

fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

fn controlled() -> Arc<dyn Storage> {
    ControlledStorage::new()
}

/// A sqlite path in a fresh temp directory; the directory lives as long as
/// the returned guard (TS `afterEach` removes it).
fn sqlite_path() -> (tempfile::TempDir, std::path::PathBuf) {
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-submissions-")
        .tempdir()
        .expect("temp dir");
    let path = directory.path().join("session.sqlite");
    (directory, path)
}

async fn sqlite(path: &std::path::Path) -> Arc<dyn Storage> {
    Arc::new(
        open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
            .await
            .expect("open sqlite storage"),
    )
}

fn answer(text: &str) -> AssistantMessage {
    faux_assistant_message(
        vec![faux_text(text)],
        FauxAssistantMessageOptions::default(),
    )
}

fn input(text: &str) -> InputSubmissionDraft {
    InputSubmissionDraft::new(text)
}

fn input_with_request(text: &str, request_id: &str) -> InputSubmissionDraft {
    InputSubmissionDraft {
        request_id: Some(request_id.to_owned()),
        ..input(text)
    }
}

fn write(entry: EntryDraft, request_id: Option<&str>) -> WriteSubmissionDraft {
    WriteSubmissionDraft {
        request_id: request_id.map(str::to_owned),
        entry,
    }
}

fn ownerless() -> ConversationCreateOptions {
    ConversationCreateOptions::new(ConversationOwnership::Ownerless)
}

/// Faux step that answers `message` once `release` resolves.
fn held(release: &Deferred, message: AssistantMessage) -> FauxResponseStep {
    let release = release.clone();
    FauxResponseStep::Factory(Arc::new(move |_, _, _, _| {
        let (release, message) = (release.clone(), message.clone());
        async move {
            release.wait().await;
            Ok(message)
        }
        .boxed()
    }))
}

#[tokio::test]
async fn appends_an_idle_write_and_settles_it_done_without_a_turn() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(controlled(), &setup, None).await.unwrap();
    let mut note = EntryDraft::new("note");
    note.data = Some(json(r#"{"text":"x"}"#));
    let submission = root.submit(write(note, None), context()).await.unwrap();
    let settled = submission.wait(context()).await.unwrap();
    let entry = settled.state.entry().expect("a done write has an entry");
    assert_eq!(
        settled.record(),
        &SubmissionRecord {
            id: submission.id(),
            conversation_id: root.id(),
            request_id: None,
            state: SubmissionState::Write(WriteSubmission::Done { entry }),
        }
    );
    let entries = all_entries(&root, context()).await.unwrap();
    assert_eq!(
        entries,
        [EntryRecord {
            model: None,
            data: Some(json(r#"{"text":"x"}"#)),
            edits: None,
            kind: "note".to_owned(),
            id: entry,
            conversation_id: root.id(),
            head: None,
            by_task_id: None,
        }]
    );
    assert_eq!(
        harness
            .snapshot(&LIVE_DOC, root.id(), context())
            .await
            .unwrap()
            .map(JsonValue::Object),
        Some(json("{}"))
    );
    let root_id = root.id();
    let tasks = harness
        .commit(
            move |tx| async move {
                tx.scan_tasks(
                    TaskQuery {
                        conversation_id: Some(root_id),
                        ..TaskQuery::default()
                    },
                    10,
                    None,
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    assert!(tasks.items.is_empty());
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn places_idle_input_and_rejects_busy_input_with_when_busy_reject_without_writing() {
    let storage = ControlledStorage::new();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.set_now(|| 42.0);
    let busy = unanswered();
    setup.faux.set_responses(vec![busy.step.clone()]);
    let OpenChat { harness, root } =
        open_chat(Arc::clone(&storage) as Arc<dyn Storage>, &setup, None)
            .await
            .unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    busy.reached().await;
    let record = submission.status(context()).await.unwrap();
    let SubmissionState::Input(InputSubmission::Placed { entry: placed }) = record.state else {
        panic!("Unexpected {:?}", record.state.status());
    };
    let entry = root
        .commit(
            move |tx| async move { tx.typed_entry(&USER_ENTRY, placed).await },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        entry.and_then(|entry| entry.model.clone()),
        Some(vec![Message::User(UserMessage {
            content: UserContent::Text("hi".to_owned()),
            timestamp: 42,
        })])
    );
    let live: LiveState = from_json(&JsonValue::Object(
        harness
            .snapshot(&LIVE_DOC, root.id(), context())
            .await
            .unwrap()
            .unwrap(),
    ))
    .unwrap();
    let run = live.run.expect("a busy conversation has a run");
    assert_eq!(run.inputs, [submission.id()]);
    assert_eq!(
        harness
            .get_task(run.task_id, context())
            .await
            .unwrap()
            .map(|task| task.kind),
        Some("pi.generation".to_owned())
    );

    let commits = storage.commit_count();
    let rejected = root
        .submit(
            InputSubmissionDraft {
                when_busy: Some(WhenBusy::Reject),
                ..input("again")
            },
            context(),
        )
        .await
        .unwrap_err();
    let SessionError::Other(error) = &rejected else {
        panic!("expected ConversationBusy, got {rejected:?}");
    };
    let busy_error = error
        .downcast_ref::<ConversationBusy>()
        .expect("a ConversationBusy");
    assert_eq!(busy_error.conversation_id, root.id());
    assert_eq!(storage.commit_count(), commits);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn deduplicates_request_ids_per_conversation_before_any_write() {
    let storage = ControlledStorage::new();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let busy = unanswered();
    setup.faux.set_responses(vec![busy.step.clone()]);
    let OpenChat { harness, root } =
        open_chat(Arc::clone(&storage) as Arc<dyn Storage>, &setup, None)
            .await
            .unwrap();
    let first = root
        .submit(input_with_request("hi", "r1"), context())
        .await
        .unwrap();
    busy.reached().await;
    let commits = storage.commit_count();
    // Deduplication runs before the busy check.
    let again = root
        .submit(input_with_request("different", "r1"), context())
        .await
        .unwrap();
    assert_eq!(again.id(), first.id());
    assert_eq!(storage.commit_count(), commits);
    let error = root
        .submit(write(EntryDraft::new("note"), Some("r1")), context())
        .await
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Request r1 already identifies a submission of type input"),
        "{error}"
    );
    let status = first.status(context()).await.unwrap();
    assert_eq!(status.request_id.as_deref(), Some("r1"));
    assert_eq!(status.state.status(), SubmissionStatus::Placed);

    let other = harness
        .create_conversation(ownerless(), context())
        .await
        .unwrap();
    let written = other
        .submit(write(EntryDraft::new("note"), Some("r1")), context())
        .await
        .unwrap();
    assert_ne!(written.id(), first.id());
    assert_eq!(
        other
            .submit(write(EntryDraft::new("note"), Some("r1")), context())
            .await
            .unwrap()
            .id(),
        written.id()
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reports_abort_results_and_looks_submissions_up_by_conversation() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let release: Deferred = deferred();
    setup
        .faux
        .set_responses(vec![held(&release, answer("answer"))]);
    let OpenChat { harness, root } = open_chat(controlled(), &setup, None).await.unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    assert_eq!(
        submission.abort(context()).await.unwrap(),
        SubmissionAbort::AlreadyPlaced
    );
    assert_eq!(
        harness
            .abort_submission(submission.id(), Some(root.id()), context())
            .await
            .unwrap(),
        AbortSubmissionResult::AlreadyPlaced
    );
    let other = harness
        .create_conversation(ownerless(), context())
        .await
        .unwrap();
    assert_eq!(
        harness
            .abort_submission(submission.id(), Some(other.id()), context())
            .await
            .unwrap(),
        AbortSubmissionResult::NotFound
    );
    assert_eq!(
        harness
            .abort_submission(SubmissionId::from_number(999_999), None, context())
            .await
            .unwrap(),
        AbortSubmissionResult::NotFound
    );
    assert!(harness
        .submission(SubmissionId::from_number(999_999), context())
        .await
        .unwrap()
        .is_none());

    release.resolve(());
    submission.wait(context()).await.unwrap();
    assert_eq!(
        submission.abort(context()).await.unwrap(),
        SubmissionAbort::Settled
    );
    assert_eq!(
        harness
            .abort_submission(submission.id(), None, context())
            .await
            .unwrap(),
        AbortSubmissionResult::Settled
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn cancels_only_a_wait_and_rejects_pending_waits_on_close() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.faux.set_responses(vec![unanswered().step]);
    let OpenChat { harness, root } = open_chat(controlled(), &setup, None).await.unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    let (cancel_cx, controller) = with_cancel(context());
    let cancelled = tokio::spawn(submission.wait(&cancel_cx));
    let pending = tokio::spawn(submission.wait(context()));
    controller.cancel(Some(Arc::new(SessionError::error("stop waiting"))));
    let error = cancelled.await.unwrap().unwrap_err();
    assert!(error.to_string().contains("stop waiting"), "{error}");
    assert_eq!(
        submission.status(context()).await.unwrap().state.status(),
        SubmissionStatus::Placed
    );
    harness.close(context()).await.unwrap();
    let error = pending.await.unwrap().unwrap_err();
    assert!(error.to_string().contains("Harness is closed"), "{error}");
}

/// Controlled storage whose submission reads block while `hold` is set
/// (TS `class HeldReads extends ControlledStorage`).
struct HeldReads {
    inner: Arc<ControlledStorage>,
    hold: AtomicBool,
    entered: Deferred,
    release: Deferred,
}

impl Storage for HeldReads {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        self.inner.commit(writes, cx)
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        self.inner.mint_id()
    }

    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>> {
        self.inner.conversation(id, cx)
    }

    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>> {
        self.inner.scan_conversations(query, limit, cursor, cx)
    }

    fn entry<'a>(
        &'a self,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.inner.entry(id, cx)
    }

    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.inner.entry_in(conversation_id, id, cx)
    }

    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>> {
        self.inner
            .find_latest_head_marker(conversation_id, at_or_before_entry_id, cx)
    }

    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>> {
        self.inner.scan_entries(query, limit, cursor, cx)
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        self.inner.task(id, cx)
    }

    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>> {
        self.inner.scan_tasks(query, limit, cursor, cx)
    }

    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        async move {
            if self.hold.load(Ordering::SeqCst) {
                self.entered.resolve(());
                self.release.wait().await;
            }
            self.inner.submission(id, cx).await
        }
        .boxed()
    }

    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>> {
        self.inner.scan_submissions(query, limit, cursor, cx)
    }

    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.inner
            .submission_by_request(conversation_id, request_id, cx)
    }

    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>> {
        self.inner.find_document(address, at, cx)
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
        self.inner.document(id, at, cx)
    }

    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>> {
        self.inner.scan_documents(query, limit, cursor, cx)
    }

    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        self.inner.close(cx)
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn rejects_a_wait_whose_submission_read_spans_the_start_of_close() {
    let storage = Arc::new(HeldReads {
        inner: ControlledStorage::new(),
        hold: AtomicBool::new(false),
        entered: deferred(),
        release: deferred(),
    });
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.faux.set_responses(vec![unanswered().step]);
    let OpenChat { harness, root } =
        open_chat(Arc::clone(&storage) as Arc<dyn Storage>, &setup, None)
            .await
            .unwrap();
    let submission = root.submit(input("hi"), context()).await.unwrap();
    storage.hold.store(true, Ordering::SeqCst);
    let waiting = tokio::spawn(submission.wait(context()));
    storage.entered.wait().await;
    let closing = tokio::spawn(harness.close(context()));
    storage.release.resolve(());
    let error = waiting.await.unwrap().unwrap_err();
    assert!(error.to_string().contains("Harness is closed"), "{error}");
    closing.await.unwrap().unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn reacquires_a_submission_after_reopen_and_settles_it_durably() {
    let (_directory, path) = sqlite_path();
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    // The first process never answers; the reopened one does.
    let busy = unanswered();
    setup
        .faux
        .set_responses(vec![busy.step.clone(), answer("after reopen").into()]);
    let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    let id = opened
        .root
        .submit(input_with_request("hi", "print"), context())
        .await
        .unwrap()
        .id();
    busy.reached().await;
    opened.harness.close(context()).await.unwrap();

    let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    let submission = opened
        .harness
        .submission(id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        submission.status(context()).await.unwrap().state.status(),
        SubmissionStatus::Placed
    );
    opened.harness.resume().unwrap();
    let settled = submission.wait(context()).await.unwrap();
    assert!(
        matches!(
            settled.state,
            SubmissionState::Input(InputSubmission::Done { .. })
        ),
        "Unexpected {:?}",
        settled.state.status()
    );
    opened.harness.close(context()).await.unwrap();

    let opened = open_chat(sqlite(&path).await, &setup, None).await.unwrap();
    let reacquired = opened
        .harness
        .submission(id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(reacquired.wait(context()).await.unwrap(), settled);
    let again = opened
        .root
        .submit(input_with_request("hi", "print"), context())
        .await
        .unwrap();
    assert_eq!(again.id(), id);
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test(flavor = "multi_thread")]
async fn enables_scheduling_when_a_caller_submits_or_waits() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    setup.faux.set_responses(vec![answer("answer").into()]);
    let OpenChat { harness, root } = open_chat(controlled(), &setup, None).await.unwrap();
    // No resume(): submitting asks for progress.
    let settled = root
        .submit(input("hi"), context())
        .await
        .unwrap()
        .wait(context())
        .await
        .unwrap();
    assert_eq!(settled.state.status(), SubmissionStatus::Done);
    harness.close(context()).await.unwrap();

    let passive = open_chat(
        controlled(),
        &chat_setup(RegisterFauxProviderOptions::default()),
        None,
    )
    .await
    .unwrap();
    let generation = generation_task().erase().as_definition_ref();
    let task_id = passive
        .root
        .commit(
            move |tx| async move {
                tx.create_task(
                    generation,
                    json("{}"),
                    TaskOptions {
                        ownership: TaskOwnership::Conversation,
                        conversation_id: None,
                        background: None,
                        abandon_on_restart: None,
                    },
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    // A committed task alone does not start scheduling; waiting for it does.
    assert_eq!(
        passive
            .harness
            .get_task(task_id, context())
            .await
            .unwrap()
            .map(|task| task.state.status()),
        Some(TaskStatus::Pending)
    );
    // A `SettledTask` exists only for a terminal task (TS `state.status === "terminal"`).
    passive
        .harness
        .wait_for_task(task_id, context())
        .await
        .unwrap();
    passive.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn settles_submissions_by_their_current_record_in_the_transaction() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(controlled(), &setup, None).await.unwrap();
    let root_id = root.id();
    let entry = root
        .commit(
            move |tx| async move { Ok(tx.append_entry(root_id, EntryDraft::new("note")).await?.id) },
            context(),
        )
        .await
        .unwrap();
    // TS `session.commitWith(...)` on the unscoped Session.
    let create = |state: SubmissionState| {
        harness.commit(
            move |tx| async move {
                Ok(tx
                    .create_submission(SubmissionCreate {
                        conversation_id: root_id,
                        request_id: None,
                        state,
                    })
                    .await?
                    .id)
            },
            context(),
        )
    };
    let queued = create(SubmissionState::Input(InputSubmission::Queued))
        .await
        .unwrap();
    let written = create(SubmissionState::Write(WriteSubmission::Queued))
        .await
        .unwrap();
    let settle = |id: SubmissionId, settlement: SubmissionSettlement| {
        root.commit(
            move |tx| async move { tx.settle_submission(id, settlement) },
            context(),
        )
    };
    let done = SubmissionSettlement::Done { answer: entry };
    let error = settle(queued, done.clone()).await.unwrap_err();
    assert!(
        error.to_string().contains("is not a placed input"),
        "{error}"
    );
    let error = settle(written, done.clone()).await.unwrap_err();
    assert!(
        error.to_string().contains("is not a placed input"),
        "{error}"
    );
    let error = settle(
        SubmissionId::from_number(999_999),
        SubmissionSettlement::Unanswered {
            reason: "x".to_owned(),
            detail: None,
        },
    )
    .await
    .unwrap_err();
    assert!(error.to_string().contains("does not exist"), "{error}");

    // A submission created earlier in the same commit settles; a second settlement leaves the first.
    let placed = harness
        .commit(
            move |tx| async move {
                let id = tx
                    .create_submission(SubmissionCreate {
                        conversation_id: root_id,
                        request_id: None,
                        state: SubmissionState::Input(InputSubmission::Placed { entry }),
                    })
                    .await?
                    .id;
                tx.settle_submission(id, done)?;
                tx.settle_submission(
                    id,
                    SubmissionSettlement::Unanswered {
                        reason: "late".to_owned(),
                        detail: None,
                    },
                )?;
                Ok(id)
            },
            context(),
        )
        .await
        .unwrap();
    let status = harness
        .submission(placed, context())
        .await
        .unwrap()
        .unwrap()
        .status(context())
        .await
        .unwrap();
    assert_eq!(
        status.state,
        SubmissionState::Input(InputSubmission::Done {
            entry,
            answer: entry,
        })
    );
    harness.close(context()).await.unwrap();
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct CounterData {
    n: u64,
}

#[tokio::test]
async fn appends_and_reads_typed_entries_through_tokens() {
    const COUNTER: Entry<CounterData> = match Entry::define("app.counter") {
        Ok(token) => token,
        Err(_) => panic!("valid entry kind"),
    };
    const MARKER: Entry = match Entry::define("app.marker") {
        Ok(token) => token,
        Err(_) => panic!("valid entry kind"),
    };
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let OpenChat { harness, root } = open_chat(controlled(), &setup, None).await.unwrap();
    let root_id = root.id();
    let counter = root
        .commit(
            move |tx| async move {
                tx.append_typed_entry(
                    &COUNTER,
                    root_id,
                    TypedEntryDraft {
                        model: None,
                        data: CounterData { n: 1 },
                        head: None,
                        edits: None,
                    },
                )
                .await
            },
            context(),
        )
        .await
        .unwrap();
    let n: u64 = counter.data().n;
    assert_eq!(n, 1);
    assert_eq!(
        counter.entry(),
        &EntryRecord {
            model: None,
            data: Some(json(r#"{"n":1}"#)),
            edits: None,
            kind: "app.counter".to_owned(),
            id: counter.id,
            conversation_id: root_id,
            head: None,
            by_task_id: None,
        }
    );
    let marker = root
        .commit(
            move |tx| async move {
                tx.append_typed_entry(&MARKER, root_id, TypedEntryDraft::default())
                    .await
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(marker.kind, "app.marker");
    let counter_id = counter.id;
    assert_eq!(
        root.commit(
            move |tx| async move { tx.typed_entry(&COUNTER, counter_id).await },
            context()
        )
        .await
        .unwrap(),
        Some(counter.clone())
    );
    assert!(root
        .commit(
            move |tx| async move { tx.typed_entry(&MARKER, counter_id).await },
            context()
        )
        .await
        .unwrap()
        .is_none());
    assert!(root
        .commit(
            |tx| async move {
                tx.typed_entry(&COUNTER, EntryId::from_number(999_999))
                    .await
            },
            context()
        )
        .await
        .unwrap()
        .is_none());
    assert!(COUNTER.is(Some(counter.entry())));
    assert!(!ASSISTANT_ENTRY.is(Some(counter.entry())));
    assert_eq!(
        [USER_ENTRY.kind(), ASSISTANT_ENTRY.kind()],
        ["pi.user", "pi.assistant"]
    );
    harness.close(context()).await.unwrap();
}
