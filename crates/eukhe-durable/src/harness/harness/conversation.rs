//! Conversation handles: the stateless host handle bound to a Harness, and
//! the invocation-bound handle tasks and tools receive.

use std::sync::Arc;

use eukhe_chord::context::{with_abort_signal, Context};
use eukhe_types::pi_ai::{Message, UserContent, UserMessage};
use futures::future::{self, BoxFuture};
use futures::{Future, FutureExt};

use super::{Core, CreateOptions, CreateTarget};
use crate::entries::RESET_ENTRY;
use crate::harness::agent::configure;
use crate::harness::context::read_context;
use crate::harness::live::run::{create_compaction, timestamp, CompactionInput};
use crate::harness::scheduler::{ConversationAbortReach, InvocationBinding, TaskScheduler};
use crate::harness::submissions::{SubmissionHandle, Submissions};
use crate::harness::types::{
    Agent, AgentChange, CompactionReason, CompactionResult, ContextOptions, ContextView,
    ConversationAbortOptions, ConversationCreateOptions, ConversationHandle, InputSubmissionDraft,
    SettledSubmissionRecord, Submission, SubmissionAbort, SubmissionDraft, WriteSubmissionDraft,
};
use crate::session::{SessionResult, TransactionScope, Tx};
use crate::types::{
    ConversationId, Cursor, EntryDraft, EntryHead, EntryId, EntryQuery, EntryRecord, Page,
    ScanOrder, SubmissionId, SubmissionRecord, TaskId,
};

/// The bounds of [`Conversation::entries`] (TS `Omit<EntryQuery,
/// "conversationId">`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ConversationEntryQuery {
    pub min_entry_id: Option<EntryId>,
    pub max_entry_id: Option<EntryId>,
    /// Default descending; with a cursor, the cursor's order.
    pub order: Option<ScanOrder>,
}

fn reach(options: ConversationAbortOptions) -> ConversationAbortReach {
    if options.background {
        ConversationAbortReach::Background
    } else {
        ConversationAbortReach::Ordinary
    }
}

/// Stateless handle for one conversation, bound to the Harness that returned
/// it. Compare handles by [`Conversation::id`].
#[derive(Clone)]
pub struct Conversation {
    id: ConversationId,
    core: Arc<Core>,
}

impl std::fmt::Debug for Conversation {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Conversation")
            .field("id", &self.id)
            .finish_non_exhaustive()
    }
}

impl Conversation {
    pub(super) fn new(id: ConversationId, core: Arc<Core>) -> Self {
        Self { id, core }
    }

    /// Harness-private services, for sibling harness modules.
    pub(crate) fn core(&self) -> &Arc<Core> {
        &self.core
    }

    /// The conversation's ID.
    #[must_use]
    pub fn id(&self) -> ConversationId {
        self.id
    }

    /// The agent resolved with the current registry snapshot and settings.
    #[must_use]
    pub fn agent(&self, cx: &Context) -> BoxFuture<'static, SessionResult<Agent>> {
        self.core.resolve_agent(self.id, None, cx)
    }

    /// `configure()` in its own commit.
    #[must_use]
    pub fn configure(
        &self,
        change: AgentChange,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        let id = self.id;
        self.core
            .session
            .commit(
                move |tx| async move { configure(&tx, id, &change).await },
                cx,
            )
            .boxed()
    }

    /// Durably admit user input or a passive entry write. A busy
    /// conversation, or one with queued items, queues it in `pi.inbox`;
    /// `WhenBusy::Reject` rejects with `ConversationBusy` instead and writes
    /// nothing.
    pub fn submit(
        &self,
        submission: impl Into<SubmissionDraft>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SubmissionHandle>> {
        self.core.submissions.submit(self.id, submission.into(), cx)
    }

    /// Admit a write of a `pi.reset` entry that starts a new context,
    /// carrying `handoff` as a user message when given. Resolves after
    /// admission; while busy, it is placed at the next boundary.
    #[must_use]
    pub fn reset(
        &self,
        handoff: Option<String>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        let mut entry = EntryDraft::new(RESET_ENTRY.kind());
        entry.head = Some(EntryHead::SelfEntry);
        if let Some(handoff) = handoff {
            let timestamp = match timestamp((self.core.now)()) {
                Ok(timestamp) => timestamp,
                Err(error) => return future::ready(Err(error)).boxed(),
            };
            entry.model = Some(vec![Message::User(UserMessage {
                content: UserContent::Text(handoff),
                timestamp,
            })]);
        }
        let draft = SubmissionDraft::Write(WriteSubmissionDraft {
            request_id: None,
            entry,
        });
        let submitted = self.core.submissions.submit(self.id, draft, cx);
        async move {
            submitted.await?;
            Ok(())
        }
        .boxed()
    }

    /// Admit a manual compaction task and return its ID. It summarizes while
    /// the conversation keeps working and places its summary through a write
    /// submission: at once when idle, otherwise at the next boundary (spec
    /// §8.7).
    #[must_use]
    pub fn compact(
        &self,
        instructions: Option<String>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<TaskId<CompactionResult>>> {
        self.core.tasks.resume();
        let id = self.id;
        let compaction = self.core.compaction();
        let input = CompactionInput {
            reason: CompactionReason::Manual,
            instructions,
        };
        self.core
            .session
            .commit(
                move |tx| async move { create_compaction(&tx, &compaction, id, input, None).await },
                cx,
            )
            .boxed()
    }

    /// Session commit whose `tx.create_task()` defaults to this conversation.
    pub fn commit<T, F, Fut>(&self, change: F, cx: &Context) -> BoxFuture<'static, SessionResult<T>>
    where
        T: Send + 'static,
        F: FnOnce(Tx) -> Fut + Send + 'static,
        Fut: Future<Output = SessionResult<T>> + Send + 'static,
    {
        let scope = TransactionScope {
            conversation_id: Some(self.id),
            task_id: None,
        };
        self.core.session.commit_with(change, cx, scope).boxed()
    }

    /// Committed raw active transcript and model context. With `at`, the
    /// context as of that visible entry: the same view `fork(at)` would start
    /// with, without creating a conversation.
    #[must_use]
    pub fn context(
        &self,
        cx: &Context,
        options: ContextOptions,
    ) -> BoxFuture<'static, SessionResult<ContextView>> {
        read_context(&self.core.session, self.id, cx, options.at)
    }

    /// Fork-aware history of this conversation, newest first unless
    /// `query.order` is ascending.
    #[must_use]
    pub fn entries(
        &self,
        query: ConversationEntryQuery,
        limit: usize,
        cursor: Option<Cursor>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Page<EntryRecord>>> {
        let bounded = EntryQuery {
            conversation_id: self.id,
            min_entry_id: query.min_entry_id,
            max_entry_id: query.max_entry_id,
            order: query.order,
        };
        let storage = Arc::clone(&self.core.storage);
        let cx = cx.clone();
        self.core
            .session
            .read_on_line(async move {
                Ok(storage
                    .scan_entries(&bounded, limit, cursor.as_ref(), &cx)
                    .await?)
            })
            .boxed()
    }

    /// Fork this conversation at the visible entry `at`.
    #[must_use]
    pub fn fork(
        &self,
        at: EntryId,
        options: ConversationCreateOptions,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Conversation>> {
        self.core.create(
            CreateTarget::Fork {
                parent_id: self.id,
                at,
                ownership: options.ownership,
            },
            CreateOptions {
                agent: options.agent,
                init: options.init,
            },
            cx,
        )
    }

    /// Withdraw queued inputs (queued writes stay), mark every live
    /// non-background task of the ordinary ownership scope, signal them, and
    /// resolve once the scope is idle. Background subtrees survive unless
    /// `options.background` is set.
    #[must_use]
    pub fn abort(
        &self,
        options: ConversationAbortOptions,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        self.core.tasks.resume();
        self.core
            .tasks
            .abort_conversation(self.id, reach(options), cx)
            .boxed()
    }

    /// Resolve when the ordinary ownership scope has no live non-background
    /// task: this conversation and the conversations owned, transitively, by
    /// its non-background tasks.
    #[must_use]
    pub fn wait_for_idle(&self, cx: &Context) -> BoxFuture<'static, SessionResult<()>> {
        self.core.tasks.resume();
        self.core.tasks.wait_for_idle(Some(self.id), cx).boxed()
    }
}

/// Invocation-bound handle for tasks and tools. Every operation, and every
/// operation of a submission it returns, first checks the invocation and
/// runs under its signal, so it rejects once the invocation ends; admitted
/// work stays durable.
struct BoundConversation {
    id: ConversationId,
    binding: InvocationBinding,
    submissions: Submissions,
    tasks: TaskScheduler,
}

fn bind(binding: &InvocationBinding, cx: &Context) -> Context {
    with_abort_signal(&binding.signal(), cx)
}

/// The invocation-bound handle of conversation `id`.
pub(crate) fn bound_conversation(
    id: ConversationId,
    binding: InvocationBinding,
    submissions: Submissions,
    tasks: TaskScheduler,
) -> Arc<dyn ConversationHandle> {
    Arc::new(BoundConversation {
        id,
        binding,
        submissions,
        tasks,
    })
}

impl ConversationHandle for BoundConversation {
    fn id(&self) -> ConversationId {
        self.id
    }

    fn submit(
        &self,
        submission: InputSubmissionDraft,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Arc<dyn Submission>>> {
        if let Err(error) = self.binding.check() {
            return future::ready(Err(error)).boxed();
        }
        let submitted = self.submissions.submit(
            self.id,
            SubmissionDraft::Input(submission),
            &bind(&self.binding, cx),
        );
        let binding = self.binding.clone();
        async move {
            let inner = submitted.await?;
            Ok(Arc::new(BoundSubmission { inner, binding }) as Arc<dyn Submission>)
        }
        .boxed()
    }

    fn abort(
        &self,
        options: ConversationAbortOptions,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        if let Err(error) = self.binding.check() {
            return future::ready(Err(error)).boxed();
        }
        self.tasks
            .abort_conversation(self.id, reach(options), &bind(&self.binding, cx))
            .boxed()
    }

    fn wait_for_idle(&self, cx: &Context) -> BoxFuture<'static, SessionResult<()>> {
        if let Err(error) = self.binding.check() {
            return future::ready(Err(error)).boxed();
        }
        self.tasks
            .wait_for_idle(Some(self.id), &bind(&self.binding, cx))
            .boxed()
    }
}

/// A submission returned by a bound handle; bound like it.
struct BoundSubmission {
    inner: SubmissionHandle,
    binding: InvocationBinding,
}

impl Submission for BoundSubmission {
    fn id(&self) -> SubmissionId {
        self.inner.id()
    }

    fn status(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SubmissionRecord>> {
        match self.binding.check() {
            Ok(()) => self.inner.status(&bind(&self.binding, cx)),
            Err(error) => future::ready(Err(error)).boxed(),
        }
    }

    fn wait(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SettledSubmissionRecord>> {
        match self.binding.check() {
            Ok(()) => self.inner.wait(&bind(&self.binding, cx)),
            Err(error) => future::ready(Err(error)).boxed(),
        }
    }

    fn abort(&self, cx: &Context) -> BoxFuture<'static, SessionResult<SubmissionAbort>> {
        match self.binding.check() {
            Ok(()) => self.inner.abort(&bind(&self.binding, cx)),
            Err(error) => future::ready(Err(error)).boxed(),
        }
    }
}
