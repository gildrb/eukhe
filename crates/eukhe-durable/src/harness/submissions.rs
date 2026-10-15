//! Durable submissions of one Harness (`harness/submissions.ts`, spec §6):
//! admission, awaitable handles, waits, and withdrawal.

use std::future::Future;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError, Weak};

use eukhe_chord::context::Context;
use eukhe_chord::json::to_json;
use futures::future::BoxFuture;
use futures::FutureExt;

use crate::errors::ConversationBusy;
use crate::harness::inbox::{
    append_input, apply_boundary, has_queued_reset, is_display_only, is_stale, prepare_boundary,
    remove_inbox_item, BoundaryAt, InboxItem, PlacedInput, QueueModes, INBOX_DOC,
};
use crate::harness::live::run::{start_run, timestamp};
use crate::harness::live::LIVE_DOC;
use crate::harness::types::{
    InputEntry, InputSubmissionDraft, SettledSubmissionRecord, Submission, SubmissionAbort,
    SubmissionDraft, WhenBusy, WriteSubmissionDraft,
};
use crate::harness::util::{closed_error, Waiters};
use crate::session::Session;
use crate::session::{SessionError, SessionResult, Tx, Unsubscribe};
use crate::tasks::AnyTask;
use crate::types::{
    CommitChange, CommitPublication, ConversationId, EntryDraft, InputSubmission, SubmissionCreate,
    SubmissionId, SubmissionRecord, SubmissionState, SubmissionStatus, SubmissionType,
    WriteSubmission,
};

/// Result of withdrawing a submission by ID (`Harness.abortSubmission()`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbortSubmissionResult {
    /// It was queued: it settled `unanswered` with `aborted` and left the inbox.
    Aborted,
    /// A run already placed it.
    AlreadyPlaced,
    /// It had settled.
    Settled,
    /// Unknown, or of another conversation than the one asked for.
    NotFound,
}

impl AbortSubmissionResult {
    /// The TS string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Aborted => "aborted",
            Self::AlreadyPlaced => "already_placed",
            Self::Settled => "settled",
            Self::NotFound => "not_found",
        }
    }
}

/// What admission reads at each commit, on the Session line.
pub(crate) struct SubmissionServices {
    pub(crate) now: Arc<dyn Fn() -> f64 + Send + Sync>,
    pub(crate) queue_modes: Arc<dyn Fn() -> QueueModes + Send + Sync>,
    /// The built-in generation task, which runs admitted input.
    pub(crate) generation: Arc<dyn Fn() -> SessionResult<AnyTask> + Send + Sync>,
    /// Enable task scheduling; submitting or waiting asks for progress.
    pub(crate) resume: Arc<dyn Fn() + Send + Sync>,
}

struct Inner {
    session: Session,
    services: SubmissionServices,
    waiters: Waiters<SubmissionId, SettledSubmissionRecord>,
    closed: AtomicBool,
    subscriptions: Mutex<Vec<Unsubscribe>>,
}

/// Admission, waits, and withdrawal of the durable submissions of one
/// Harness. Clones share the state.
#[derive(Clone)]
pub(crate) struct Submissions {
    inner: Arc<Inner>,
}

impl std::fmt::Debug for Submissions {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Submissions")
            .finish_non_exhaustive()
    }
}

impl Submissions {
    /// Submissions over `session`; [`Submissions::subscribe`] starts
    /// observing its commits and close.
    pub(crate) fn new(session: Session, services: SubmissionServices) -> Self {
        Self {
            inner: Arc::new(Inner {
                session,
                services,
                waiters: Waiters::new(),
                closed: AtomicBool::new(false),
                subscriptions: Mutex::new(Vec::new()),
            }),
        }
    }

    /// Observe settling commits and the start of close.
    ///
    /// # Errors
    ///
    /// The Session is closed or failed.
    pub(crate) fn subscribe(&self) -> SessionResult<()> {
        let session = &self.inner.session;
        let weak = Arc::downgrade(&self.inner);
        let commits = session.observe_commits(Arc::new(move |publication, _cx| {
            if let Some(inner) = weak.upgrade() {
                observe(&inner, publication);
            }
            Ok(())
        }))?;
        let weak: Weak<Inner> = Arc::downgrade(&self.inner);
        let close = session.subscribe_close(Arc::new(move || {
            if let Some(inner) = weak.upgrade() {
                inner.closed.store(true, Ordering::SeqCst);
                inner.waiters.reject_all(&closed_error(&inner.session));
            }
        }))?;
        self.inner
            .subscriptions
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .extend([commits, close]);
        Ok(())
    }

    /// Admit a submission in one commit; see [`admit_submission`].
    pub(crate) fn submit(
        &self,
        conversation_id: ConversationId,
        draft: SubmissionDraft,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SubmissionHandle>> {
        (self.inner.services.resume)();
        let inner = Arc::clone(&self.inner);
        let committed = self.inner.session.commit(
            move |tx| async move {
                let services = &inner.services;
                let generation = (services.generation)()?;
                admit_submission(
                    &tx,
                    conversation_id,
                    draft,
                    (services.now)(),
                    (services.queue_modes)(),
                    &generation,
                )
                .await
            },
            cx,
        );
        let submissions = self.clone();
        async move {
            let id = committed.await?;
            Ok(SubmissionHandle { id, submissions })
        }
        .boxed()
    }

    /// Handle for an existing submission, or `None`.
    pub(crate) fn get(
        &self,
        id: SubmissionId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<SubmissionHandle>>> {
        let record = self.read(id, cx);
        let submissions = self.clone();
        async move {
            Ok(record.await?.map(|record| SubmissionHandle {
                id: record.id,
                submissions,
            }))
        }
        .boxed()
    }

    fn read(
        &self,
        id: SubmissionId,
        cx: &Context,
    ) -> impl Future<Output = SessionResult<Option<SubmissionRecord>>> + Send + 'static {
        let storage = Arc::clone(self.inner.session.storage());
        let cx = cx.clone();
        self.inner
            .session
            .read_on_line(async move { Ok(storage.submission(id, &cx).await?) })
    }

    pub(crate) fn status(
        &self,
        id: SubmissionId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SubmissionRecord>> {
        let record = self.read(id, cx);
        async move { record.await?.ok_or_else(|| missing(id)) }.boxed()
    }

    pub(crate) fn wait(
        &self,
        id: SubmissionId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SettledSubmissionRecord>> {
        (self.inner.services.resume)();
        let inner = Arc::clone(&self.inner);
        let storage = Arc::clone(self.inner.session.storage());
        let line_cx = cx.clone();
        // Check and register on the line so no settling publication falls between them.
        let found = self.inner.session.read_on_line(async move {
            let Some(record) = storage.submission(id, &line_cx).await? else {
                return Err(missing(id));
            };
            if let Ok(settled) = SettledSubmissionRecord::try_from(record) {
                return Ok(futures::future::ready(Ok(settled)).boxed());
            }
            // Close rejects registered waiters synchronously and may begin during the read.
            if inner.closed.load(Ordering::SeqCst) {
                return Err(closed_error(&inner.session));
            }
            Ok(inner.waiters.add(id, &line_cx).boxed())
        });
        async move { found.await?.await }.boxed()
    }

    /// Withdraw a queued submission and remove its inbox item; placed inputs
    /// and settled submissions are reported.
    pub(crate) fn abort(
        &self,
        id: SubmissionId,
        conversation_id: Option<ConversationId>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<AbortSubmissionResult>> {
        self.inner
            .session
            .commit(
                move |tx| async move {
                    let record = tx.submission(id).await?;
                    let Some(record) = record.filter(|record| {
                        conversation_id.is_none_or(|expected| record.conversation_id == expected)
                    }) else {
                        return Ok(AbortSubmissionResult::NotFound);
                    };
                    Ok(match record.state.status() {
                        SubmissionStatus::Queued => {
                            tx.settle_submission(id, unanswered("aborted"))?;
                            remove_inbox_item(&tx, record.conversation_id, id).await?;
                            AbortSubmissionResult::Aborted
                        }
                        SubmissionStatus::Placed => AbortSubmissionResult::AlreadyPlaced,
                        SubmissionStatus::Done | SubmissionStatus::Unanswered => {
                            AbortSubmissionResult::Settled
                        }
                    })
                },
                cx,
            )
            .boxed()
    }
}

fn observe(inner: &Inner, publication: &CommitPublication) {
    for change in &publication.changes {
        let CommitChange::Submission(record) = change else {
            continue;
        };
        if let Ok(settled) = SettledSubmissionRecord::try_from(record.clone()) {
            inner.waiters.resolve(&record.id, &settled);
        }
    }
}

fn missing(id: SubmissionId) -> SessionError {
    SessionError::error(format!("Submission {id} does not exist"))
}

fn unanswered(reason: &str) -> crate::types::SubmissionSettlement {
    crate::types::SubmissionSettlement::Unanswered {
        reason: reason.to_owned(),
        detail: None,
    }
}

/// Awaitable host object for one durably admitted submission.
#[derive(Clone)]
pub struct SubmissionHandle {
    id: SubmissionId,
    submissions: Submissions,
}

impl std::fmt::Debug for SubmissionHandle {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("SubmissionHandle")
            .field("id", &self.id)
            .finish_non_exhaustive()
    }
}

impl SubmissionHandle {
    /// The submission's ID.
    #[must_use]
    pub fn id(&self) -> SubmissionId {
        self.id
    }

    /// The committed record.
    ///
    /// # Errors
    ///
    /// `Submission {id} does not exist`, and Session failures.
    #[must_use]
    pub fn status(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SubmissionRecord>> {
        self.submissions.status(self.id, cx)
    }

    /// Resolve with the settled record. Cancelling `cx` cancels only this
    /// wait; close rejects it.
    ///
    /// # Errors
    ///
    /// `Harness is closed`, the abort reason of `cx`, and Session failures.
    #[must_use]
    pub fn wait(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SettledSubmissionRecord>> {
        self.submissions.wait(self.id, cx)
    }

    /// Withdraw the submission if still queued.
    ///
    /// # Errors
    ///
    /// `Submission {id} does not exist`, and Session failures.
    #[must_use]
    pub fn abort(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SubmissionAbort>> {
        let id = self.id;
        let result = self.submissions.abort(id, None, cx);
        async move {
            match result.await? {
                AbortSubmissionResult::Aborted => Ok(SubmissionAbort::Aborted),
                AbortSubmissionResult::AlreadyPlaced => Ok(SubmissionAbort::AlreadyPlaced),
                AbortSubmissionResult::Settled => Ok(SubmissionAbort::Settled),
                AbortSubmissionResult::NotFound => Err(missing(id)),
            }
        }
        .boxed()
    }
}

impl Submission for SubmissionHandle {
    fn id(&self) -> SubmissionId {
        self.id
    }

    fn status(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SubmissionRecord>> {
        SubmissionHandle::status(self, cx)
    }

    fn wait(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SettledSubmissionRecord>> {
        SubmissionHandle::wait(self, cx)
    }

    fn abort(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SubmissionAbort>> {
        SubmissionHandle::abort(self, cx)
    }
}

fn type_name(kind: SubmissionType) -> &'static str {
    match kind {
        SubmissionType::Input => "input",
        SubmissionType::Write => "write",
    }
}

/// Admit a submission inside a commit (spec §6); `Conversation.submit()` and
/// conversation-owned compactions share it. A known request ID returns its
/// existing submission without writing. A display-only write (only `kind` and
/// `data`) is appended and settled `done` at once, busy or not, as it changes
/// nothing the model sees; only behind a queued reset it queues, so it lands
/// after the reset instead of before it in the context the reset ends. A busy
/// conversation queues anything else in `pi.inbox`, or rejects
/// `whenBusy: "reject"` input with `ConversationBusy`. An idle conversation
/// with queued items queues it behind them and runs a final boundary.
/// Otherwise idle input places a user entry and starts a run, and an idle
/// write appends its entry and settles `done`, or `stale` when its head
/// reaches before the active range.
///
/// `generation` is the built-in generation task a started run creates.
///
/// # Errors
///
/// An input entry whose kind is empty or starts with `pi.` (a TS
/// `TypeError`), `ConversationBusy` (as [`SessionError::Other`]), a request
/// ID of another type, and transaction failures.
pub async fn admit_submission(
    tx: &Tx,
    conversation_id: ConversationId,
    draft: SubmissionDraft,
    now: f64,
    queue_modes: QueueModes,
    generation: &AnyTask,
) -> SessionResult<SubmissionId> {
    if let SubmissionDraft::Input(InputSubmissionDraft {
        entry: Some(InputEntry { kind, .. }),
        ..
    }) = &draft
    {
        if kind.is_empty() || kind.starts_with("pi.") {
            return Err(SessionError::Type(
                format!(
                    "An input entry's kind must be a non-empty string not starting with \"pi.\", got {kind}"
                )
                .into(),
            ));
        }
    }
    let request_id = draft.request_id().map(str::to_owned);
    if let Some(request_id) = &request_id {
        if let Some(existing) = known_request(tx, conversation_id, &draft, request_id).await? {
            return Ok(existing);
        }
    }
    let draft = match draft {
        SubmissionDraft::Write(write) if is_display_only(&write.entry) => {
            let items = tx
                .doc(&INBOX_DOC, conversation_id)
                .await?
                .child("items")?
                .value()?;
            let items = items
                .as_array()
                .ok_or_else(|| SessionError::error("pi.inbox items is not an array"))?;
            if !has_queued_reset(items) {
                return append_write(tx, conversation_id, request_id, write.entry).await;
            }
            SubmissionDraft::Write(write)
        }
        draft @ (SubmissionDraft::Write(_) | SubmissionDraft::Input(_)) => draft,
    };
    let live = tx.doc(&LIVE_DOC, conversation_id).await?;
    let busy = live.get("run")?.is_some();
    if busy {
        if let SubmissionDraft::Input(InputSubmissionDraft {
            when_busy: Some(WhenBusy::Reject),
            ..
        }) = &draft
        {
            return Err(SessionError::other(ConversationBusy::new(conversation_id)));
        }
    }
    // A boundary reads the table, so it is prepared before the first table write; a busy one needs none.
    let mut boundary = if busy {
        None
    } else {
        Some(prepare_boundary(tx, conversation_id, queue_modes).await?)
    };
    let idle = match &boundary {
        Some(prepared) if prepared.is_empty()? => boundary.take(),
        Some(_) | None => None,
    };
    if let Some(boundary) = idle {
        return admit_idle(
            tx,
            conversation_id,
            draft,
            request_id,
            now,
            &boundary,
            &live,
            generation,
        )
        .await;
    }
    let state = match &draft {
        SubmissionDraft::Input(_) => SubmissionState::Input(InputSubmission::Queued),
        SubmissionDraft::Write(_) => SubmissionState::Write(WriteSubmission::Queued),
    };
    let record = tx
        .create_submission(SubmissionCreate {
            conversation_id,
            request_id,
            state,
        })
        .await?;
    let id = record.id;
    let item = InboxItem::queued(id, draft)?;
    let items = match &boundary {
        Some(boundary) => boundary.items()?,
        None => tx.doc(&INBOX_DOC, conversation_id).await?.child("items")?,
    };
    items.push([to_json(&item)?])?;
    let Some(boundary) = boundary.as_mut() else {
        return Ok(id);
    };
    let result = apply_boundary(tx, boundary, BoundaryAt::Final, timestamp(now)?).await?;
    if !result.users.is_empty() {
        start_run(tx, generation, conversation_id, &live, result.users).await?;
    }
    Ok(id)
}

/// The submission `request_id` already identifies, if any.
///
/// # Errors
///
/// The request ID identifies a submission of another type than `draft`, or
/// the read fails.
async fn known_request(
    tx: &Tx,
    conversation_id: ConversationId,
    draft: &SubmissionDraft,
    request_id: &str,
) -> SessionResult<Option<SubmissionId>> {
    let Some(existing) = tx
        .submission_by_request(conversation_id, request_id.to_owned())
        .await?
    else {
        return Ok(None);
    };
    let draft_type = match draft {
        SubmissionDraft::Input(_) => SubmissionType::Input,
        SubmissionDraft::Write(_) => SubmissionType::Write,
    };
    let existing_type = existing.state.submission_type();
    if existing_type != draft_type {
        return Err(SessionError::error(format!(
            "Request {request_id} already identifies a submission of type {}",
            type_name(existing_type)
        )));
    }
    Ok(Some(existing.id))
}

/// Append a write's entry and record its submission settled `done`.
///
/// # Errors
///
/// Transaction failures.
async fn append_write(
    tx: &Tx,
    conversation_id: ConversationId,
    request_id: Option<String>,
    entry: EntryDraft,
) -> SessionResult<SubmissionId> {
    let entry = tx.append_entry(conversation_id, entry).await?;
    let write = SubmissionCreate {
        conversation_id,
        request_id,
        state: SubmissionState::Write(WriteSubmission::Done { entry: entry.id }),
    };
    Ok(tx.create_submission(write).await?.id)
}

/// Admission to an idle conversation with an empty inbox.
#[expect(
    clippy::too_many_arguments,
    reason = "the admission inputs, split out of admit_submission"
)]
async fn admit_idle(
    tx: &Tx,
    conversation_id: ConversationId,
    draft: SubmissionDraft,
    request_id: Option<String>,
    now: f64,
    boundary: &crate::harness::inbox::Boundary,
    live: &eukhe_chord::delta::Draft,
    generation: &AnyTask,
) -> SessionResult<SubmissionId> {
    match draft {
        SubmissionDraft::Write(WriteSubmissionDraft { entry, .. }) => {
            if is_stale(boundary, &entry) {
                let stale = SubmissionCreate {
                    conversation_id,
                    request_id,
                    state: SubmissionState::Write(WriteSubmission::Unanswered {
                        reason: "stale".to_owned(),
                        detail: None,
                    }),
                };
                return Ok(tx.create_submission(stale).await?.id);
            }
            append_write(tx, conversation_id, request_id, entry).await
        }
        SubmissionDraft::Input(InputSubmissionDraft {
            content,
            origin,
            entry,
            ..
        }) => {
            let input = PlacedInput {
                content,
                entry,
                origin,
            };
            let entry = append_input(tx, conversation_id, input, timestamp(now)?).await?;
            let input = SubmissionCreate {
                conversation_id,
                request_id,
                state: SubmissionState::Input(InputSubmission::Placed { entry }),
            };
            let id = tx.create_submission(input).await?.id;
            start_run(tx, generation, conversation_id, live, vec![id]).await?;
            Ok(id)
        }
    }
}
