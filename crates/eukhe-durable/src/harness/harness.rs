//! The Harness: a Session kernel extended with conversation handles, a
//! registry, a task scheduler, and submissions (`harness/harness.ts`, spec
//! §2.2).

mod conversation;

use std::ops::Deref;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Weak};

use eukhe_chord::context::{without_abort_signal, Context};
use eukhe_chord::json::{from_json, JsonObject, JsonValue};

use crate::documents::{AnyDocDefinition, ResolvedAddress};
use crate::session::DocumentWatch;
use crate::types::{DocumentObserver, DocumentReader};
use futures::future::{self, BoxFuture};
use futures::FutureExt;

use self::conversation::bound_conversation;
pub use self::conversation::{Conversation, ConversationEntryQuery};
use crate::env::ExecutionEnv;
use crate::harness::agent::{configure, create_agent, resolve_agent, resolve_settings, AGENT_DOC};
use crate::harness::inbox::{withdraw_queued_inputs, QueueModes, INBOX_DOC};
use crate::harness::live::{settle_scheduler_outcome, LIVE_DOC};
use crate::harness::provider::PROVIDER_DOC;
use crate::harness::scheduler::{TaskAbortResult, TaskScheduler, TaskSchedulerOptions};
use crate::harness::submissions::{
    AbortSubmissionResult, SubmissionHandle, SubmissionServices, Submissions,
};
use crate::harness::task_graph::TaskGraphView;
use crate::harness::types::{
    Agent, AgentChange, AgentState, ConversationCreateOptions, ConversationInit, EnvTarget,
    HarnessInspection, HarnessOptions, RegistrySnapshot, Settings,
};
use crate::harness::usage::{add_usage_state, UsageState, USAGE_DOC};
use crate::harness::util::{closed_error, scan_all};
use crate::harness::view::ConversationViews;
use crate::session::{Session, SessionError, SessionHooks, SessionResult, Tx};
use crate::tasks::SettledTask;
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationOwnership, ConversationQuery, ConversationRecord,
    EntryId, Storage, SubmissionId, SubmissionQuery, SubmissionStatus, TaskId,
    ROOT_CONVERSATION_ID,
};

const SCAN_PAGE_SIZE: usize = 256;

/// Which conversation a creation makes.
enum CreateTarget {
    Root,
    Independent(ConversationOwnership),
    Fork {
        parent_id: ConversationId,
        at: EntryId,
        ownership: ConversationOwnership,
    },
}

/// What the conveniences apply in the creating commit, after the creation hook.
#[derive(Default)]
struct CreateOptions {
    agent: Option<AgentChange>,
    init: Option<ConversationInit>,
}

/// Options of [`Harness::root`].
#[derive(Default)]
pub struct RootOptions {
    /// Applied in the creating commit after the creation hook, before `init`.
    pub agent: Option<AgentChange>,
    /// Runs inside the creating commit.
    pub init: Option<ConversationInit>,
}

/// Harness-private services shared by the Harness and its conversation
/// handles (TS `ConversationHost`).
pub(crate) struct Core {
    session: Session,
    storage: Arc<dyn Storage>,
    options: HarnessOptions,
    now: Arc<dyn Fn() -> f64 + Send + Sync>,
    report: Arc<dyn Fn(SessionError) + Send + Sync>,
    tasks: TaskScheduler,
    submissions: Submissions,
    task_graph: TaskGraphView,
    views: ConversationViews,
    closed: AtomicBool,
}

impl Core {
    fn settings(options: &HarnessOptions) -> Settings {
        let current = options.settings.as_ref().map(|source| source.current());
        resolve_settings(current.as_deref())
    }

    /// The conversation view mounts.
    pub(crate) fn views(&self) -> &ConversationViews {
        &self.views
    }

    /// The task graph mount.
    pub(crate) fn task_graph(&self) -> &TaskGraphView {
        &self.task_graph
    }

    fn assert_open(&self) -> SessionResult<()> {
        if self.closed.load(Ordering::SeqCst) {
            return Err(closed_error());
        }
        Ok(())
    }

    /// Resolve a conversation's committed `pi.agent` against `snapshot`, or
    /// the current one, and the current settings.
    fn resolve_agent(
        &self,
        id: ConversationId,
        snapshot: Option<RegistrySnapshot>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Agent>> {
        let registry = snapshot.unwrap_or_else(|| self.options.registry.snapshot());
        let state = self.session.snapshot(&AGENT_DOC, id, cx);
        let options = self.options.clone();
        let report = Arc::clone(&self.report);
        async move {
            let state: Option<AgentState> = match state.await? {
                Some(value) => Some(from_json(&JsonValue::Object(value))?),
                None => None,
            };
            let settings = Self::settings(&options);
            Ok(resolve_agent(
                state.as_ref(),
                &registry,
                &settings,
                &*report,
            ))
        }
        .boxed()
    }

    /// Build a conversation's environment from its current `cwd`; `None`
    /// without an `env` option.
    fn build_env(
        &self,
        id: ConversationId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ExecutionEnv>>>> {
        let Some(build) = self.options.env.clone() else {
            return future::ready(Ok(None)).boxed();
        };
        let session = self.session.clone();
        let cx = cx.clone();
        async move {
            let state: Option<AgentState> = match session.snapshot(&AGENT_DOC, id, &cx).await? {
                Some(value) => Some(from_json(&JsonValue::Object(value))?),
                None => None,
            };
            let target = EnvTarget {
                conversation_id: id,
                cwd: state.and_then(|state| state.cwd),
                read: Arc::new(session),
            };
            build(target, &cx).await
        }
        .boxed()
    }

    fn generation(&self) -> crate::tasks::AnyTask {
        self.options
            .registry
            .snapshot()
            .builtins()
            .generation
            .clone()
    }

    fn compaction(&self) -> crate::tasks::AnyTask {
        self.options
            .registry
            .snapshot()
            .builtins()
            .compaction
            .clone()
    }

    fn create(
        self: &Arc<Self>,
        target: CreateTarget,
        options: CreateOptions,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Conversation>> {
        if let Err(error) = self.assert_open() {
            return future::ready(Err(error)).boxed();
        }
        let committed = self.session.commit(
            move |tx: Tx| async move {
                if matches!(target, CreateTarget::Root)
                    && tx.conversation(ROOT_CONVERSATION_ID).await?.is_some()
                {
                    return Ok(ROOT_CONVERSATION_ID);
                }
                let record = match target {
                    CreateTarget::Root => tx.create_root_conversation().await?,
                    CreateTarget::Independent(ownership) => {
                        tx.create_conversation(ownership).await?
                    }
                    CreateTarget::Fork {
                        parent_id,
                        at,
                        ownership,
                    } => tx.fork_conversation(parent_id, at, ownership).await?,
                };
                if let Some(agent) = &options.agent {
                    configure(&tx, record.id, agent).await?;
                }
                if let Some(init) = options.init {
                    init(tx.clone(), record.id).await?;
                }
                Ok(record.id)
            },
            cx,
        );
        let core = Arc::clone(self);
        async move {
            let id = committed.await?;
            Ok(Conversation::new(id, core))
        }
        .boxed()
    }
}

/// The Session hooks of a Harness: the built-in creation hook and the task
/// join before Storage closes.
struct HarnessHooks {
    conversation_created: Option<crate::harness::types::ConversationCreated>,
    core: Weak<Core>,
}

impl SessionHooks for HarnessHooks {
    /// The built-in creation hook, in every commit that creates or forks a
    /// conversation: empty `pi.live`, `pi.inbox`, and `pi.usage`, a fresh
    /// `pi.provider`, the conversation's `pi.agent` (see `create_agent()`),
    /// then `HarnessOptions.conversation_created`.
    fn conversation_created(
        &self,
        tx: Tx,
        record: ConversationRecord,
    ) -> BoxFuture<'static, SessionResult<()>> {
        let hook = self.conversation_created.clone();
        async move {
            tx.doc(&LIVE_DOC, record.id).await?;
            tx.doc(&INBOX_DOC, record.id).await?;
            tx.doc(&USAGE_DOC, record.id).await?;
            tx.doc(&PROVIDER_DOC, record.id).await?;
            create_agent(&tx, &record).await?;
            if let Some(hook) = hook {
                hook(tx, record).await?;
            }
            Ok(())
        }
        .boxed()
    }

    /// Join task invocations after admission is sealed and before Storage
    /// closes; writes no task outcome.
    fn before_close(&self) -> BoxFuture<'static, ()> {
        match self.core.upgrade() {
            Some(core) => core.tasks.join().boxed(),
            None => future::ready(()).boxed(),
        }
    }
}

/// Durable agent harness over one Session. Dereferences to the [`Session`],
/// so every Session operation is available. Clones share the Harness.
#[derive(Clone)]
pub struct Harness {
    core: Arc<Core>,
}

impl std::fmt::Debug for Harness {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("Harness").finish_non_exhaustive()
    }
}

/// A Harness reads documents as its Session does (TS `Harness extends Session`).
impl DocumentReader for Harness {
    fn snapshot_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        self.core
            .session
            .snapshot_definition(definition, resolved, cx)
    }

    fn snapshot_as_of_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        at: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        self.core
            .session
            .snapshot_as_of_definition(definition, resolved, at, cx)
    }
}

impl DocumentObserver for Harness {
    fn watch_doc_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>> {
        self.core
            .session
            .watch_doc_definition(definition, resolved, cx)
    }
}

impl Deref for Harness {
    type Target = Session;

    fn deref(&self) -> &Session {
        &self.core.session
    }
}

fn upgrade(core: &Weak<Core>) -> SessionResult<Arc<Core>> {
    core.upgrade().ok_or_else(closed_error)
}

impl Harness {
    /// Harness-private services, for sibling harness modules.
    pub(crate) fn core(&self) -> &Arc<Core> {
        &self.core
    }

    /// Open a Harness over storage. The registry may keep changing while the
    /// Harness runs; every registry snapshot holds the built-in tasks.
    ///
    /// # Errors
    ///
    /// The abort reason of `cx`, or the failure of reconciling surviving
    /// `running` tasks; the Harness is then closed (a close failure goes to
    /// `on_report`).
    pub async fn open(
        storage: Arc<dyn Storage>,
        options: HarnessOptions,
        cx: &Context,
    ) -> SessionResult<Self> {
        if let Some(reason) = cx.abort_signal().and_then(|signal| signal.reason()) {
            return Err(SessionError::Aborted(reason));
        }
        let harness = Self::new(storage, options, cx)?;
        eprintln!("HARNESS-STAGE new done");
        if let Err(error) = harness.core.tasks.open(cx).await {
            // The caller's context may be what failed open: close without it, and rethrow the open error.
            if let Err(close_error) = harness.close(&without_abort_signal(cx)).await {
                (harness.core.report)(close_error);
            }
            return Err(error);
        }
        eprintln!("HARNESS-STAGE tasks open done");
        Ok(harness)
    }

    fn new(
        storage: Arc<dyn Storage>,
        options: HarnessOptions,
        cx: &Context,
    ) -> SessionResult<Self> {
        eprintln!("HARNESS-STAGE new begin");
        let report: Arc<dyn Fn(SessionError) + Send + Sync> = match &options.on_report {
            Some(report) => Arc::clone(report),
            None => Arc::new(|_| {}),
        };
        let now: Arc<dyn Fn() -> f64 + Send + Sync> = match &options.now {
            Some(now) => Arc::clone(now),
            None => Arc::new(system_now),
        };
        let core = Arc::new_cyclic(|weak: &Weak<Core>| {
            let hooks = HarnessHooks {
                conversation_created: options.conversation_created.clone(),
                core: weak.clone(),
            };
            let session = Session::with_hooks(Arc::clone(&storage), Arc::new(hooks));
            let settings_options = options.clone();
            let settings: Arc<dyn Fn() -> Settings + Send + Sync> =
                Arc::new(move || Core::settings(&settings_options));
            let agent_core = weak.clone();
            let env_core = weak.clone();
            let conversation_core = weak.clone();
            let tasks = TaskScheduler::new(TaskSchedulerOptions {
                session: session.clone(),
                registry: Arc::clone(&options.registry),
                models: options.models.clone(),
                agent: Arc::new(move |id, snapshot, cx| match upgrade(&agent_core) {
                    Ok(core) => core.resolve_agent(id, Some(snapshot), &cx),
                    Err(error) => future::ready(Err(error)).boxed(),
                }),
                settings: Arc::clone(&settings),
                env: Arc::new(move |id, cx| match upgrade(&env_core) {
                    Ok(core) => core.build_env(id, &cx),
                    Err(error) => future::ready(Err(error)).boxed(),
                }),
                now: Arc::clone(&now),
                report: Arc::clone(&report),
                settle_outcome: Arc::new(settle_scheduler_outcome),
                withdraw_inputs: Arc::new(withdraw_queued_inputs),
                conversation: Arc::new(move |id, binding, cx| {
                    let core = match upgrade(&conversation_core) {
                        Ok(core) => core,
                        Err(error) => return future::ready(Err(error)).boxed(),
                    };
                    let storage = Arc::clone(&core.storage);
                    let read = core
                        .session
                        .read_on_line(async move { Ok(storage.conversation(id, &cx).await?) });
                    async move {
                        Ok(read.await?.map(|_| {
                            bound_conversation(
                                id,
                                binding,
                                core.submissions.clone(),
                                core.tasks.clone(),
                            )
                        }))
                    }
                    .boxed()
                }),
                context: without_abort_signal(cx),
            });
            let queue_settings = Arc::clone(&settings);
            let generation_core = weak.clone();
            let resume_tasks = tasks.clone();
            let submissions = Submissions::new(
                session.clone(),
                SubmissionServices {
                    now: Arc::clone(&now),
                    queue_modes: Arc::new(move || {
                        let settings = queue_settings();
                        QueueModes {
                            steering_mode: settings.steering_mode,
                            follow_up_mode: settings.follow_up_mode,
                        }
                    }),
                    generation: Arc::new(move || match generation_core.upgrade() {
                        Some(core) => Ok(core.generation()),
                        None => Err(closed_error()),
                    }),
                    resume: Arc::new(move || resume_tasks.resume()),
                },
            );
            let task_graph = TaskGraphView::new(session.clone(), Arc::clone(&storage));
            let views = ConversationViews::new(session.clone(), Arc::clone(&storage));
            Core {
                session,
                storage,
                options,
                now,
                report,
                tasks,
                submissions,
                task_graph,
                views,
                closed: AtomicBool::new(false),
            }
        });
        // A fresh Session is neither closed nor poisoned, so this succeeds.
        core.submissions.subscribe()?;
        core.task_graph.subscribe()?;
        core.views.subscribe()?;
        Ok(Self { core })
    }

    /// Enable task scheduling. Idempotent. Calls that ask for progress enable
    /// it too: `Conversation::submit`, `compact`, `abort`, `wait_for_idle`,
    /// `SubmissionHandle::wait`, [`Harness::wait_for_task`], and
    /// [`Harness::wait_for_idle`]. Read-only viewers never do.
    ///
    /// # Errors
    ///
    /// `Harness is closed`.
    pub fn resume(&self) -> SessionResult<()> {
        self.core.assert_open()?;
        self.core.tasks.resume();
        Ok(())
    }

    /// Return the reserved root conversation, creating it with `agent` and
    /// `init` in one commit when absent.
    #[must_use]
    pub fn root(
        &self,
        options: RootOptions,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Conversation>> {
        self.core.create(
            CreateTarget::Root,
            CreateOptions {
                agent: options.agent,
                init: options.init,
            },
            cx,
        )
    }

    /// Handle of an existing conversation, or `None`.
    #[must_use]
    pub fn conversation(
        &self,
        id: ConversationId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Conversation>>> {
        if let Err(error) = self.core.assert_open() {
            return future::ready(Err(error)).boxed();
        }
        let storage = Arc::clone(&self.core.storage);
        let line_cx = cx.clone();
        let read = self
            .core
            .session
            .read_on_line(async move { Ok(storage.conversation(id, &line_cx).await?) });
        let core = Arc::clone(&self.core);
        async move { Ok(read.await?.map(|record| Conversation::new(record.id, core))) }.boxed()
    }

    /// Create an independent conversation, applying `agent` and running
    /// `init` in the creating commit.
    #[must_use]
    pub fn create_conversation(
        &self,
        options: ConversationCreateOptions,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Conversation>> {
        self.core.create(
            CreateTarget::Independent(options.ownership),
            CreateOptions {
                agent: options.agent,
                init: options.init,
            },
            cx,
        )
    }

    /// The committed record of a task, or `None`.
    #[must_use]
    pub fn get_task<R>(
        &self,
        id: TaskId<R>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<AnyTaskRecord>>> {
        let storage = Arc::clone(&self.core.storage);
        let id = id.erase();
        let cx = cx.clone();
        self.core
            .session
            .read_on_line(async move { Ok(storage.task(id, &cx).await?) })
            .boxed()
    }

    /// Live tasks and unsettled submissions. Writes nothing and runs no task
    /// code.
    #[must_use]
    pub fn inspect(&self, cx: &Context) -> BoxFuture<'static, SessionResult<HarnessInspection>> {
        let core = Arc::clone(&self.core);
        let cx = cx.clone();
        self.core
            .session
            .read_on_line(async move {
                let inspection = core
                    .tasks
                    .inspect(&core.options.registry.snapshot())
                    .await?;
                let mut submissions = Vec::new();
                for status in [SubmissionStatus::Queued, SubmissionStatus::Placed] {
                    let query = SubmissionQuery {
                        conversation_id: None,
                        status: Some(status),
                    };
                    let storage = &core.storage;
                    let query = &query;
                    let cx = &cx;
                    submissions.extend(
                        scan_all(|cursor| async move {
                            Ok(storage
                                .scan_submissions(query, SCAN_PAGE_SIZE, cursor.as_ref(), cx)
                                .await?)
                        })
                        .await?,
                    );
                }
                submissions.sort_by_key(|record| record.id);
                Ok(HarnessInspection {
                    scheduling: inspection.scheduling,
                    tasks: inspection.tasks,
                    submissions,
                })
            })
            .boxed()
    }

    /// Reacquire a submission, for example after reopen.
    #[must_use]
    pub fn submission(
        &self,
        id: SubmissionId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<SubmissionHandle>>> {
        self.core.submissions.get(id, cx)
    }

    /// Withdraw a queued submission. `NotFound` for an unknown submission or
    /// one of another conversation than `conversation_id`.
    #[must_use]
    pub fn abort_submission(
        &self,
        id: SubmissionId,
        conversation_id: Option<ConversationId>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<AbortSubmissionResult>> {
        self.core.submissions.abort(id, conversation_id, cx)
    }

    /// Commit the abort mark, signal and join an active run invocation, and
    /// schedule the abort invocation. A task whose definition cannot take it
    /// settles as `orphaned` instead.
    #[must_use]
    pub fn abort_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<TaskAbortResult>> {
        self.core.tasks.abort(id, cx).boxed()
    }

    /// Resolve with the terminal receipt; cancelling `cx` cancels only this
    /// wait.
    #[must_use]
    pub fn wait_for_task<R>(
        &self,
        id: TaskId<R>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SettledTask>> {
        self.core.tasks.resume();
        self.core.tasks.wait_for_task(id.erase(), cx).boxed()
    }

    /// Resolve when the ordinary ownership scope of every ownerless
    /// conversation has no live non-background task.
    #[must_use]
    pub fn wait_for_idle(&self, cx: &Context) -> BoxFuture<'static, SessionResult<()>> {
        self.core.tasks.resume();
        self.core.tasks.wait_for_idle(None, cx).boxed()
    }

    /// Sum every conversation's committed `pi.usage`. Each document is read
    /// at its own point; totals only grow.
    #[must_use]
    pub fn usage(&self, cx: &Context) -> BoxFuture<'static, SessionResult<UsageState>> {
        let core = Arc::clone(&self.core);
        let cx = cx.clone();
        let storage = Arc::clone(&core.storage);
        let scan_cx = cx.clone();
        // Enqueued at the call, as the TS promise starts eagerly.
        let scanned = core.session.read_on_line(async move {
            let query = ConversationQuery::default();
            let (storage, query, cx) = (&storage, &query, &scan_cx);
            scan_all(|cursor| async move {
                Ok(storage
                    .scan_conversations(query, SCAN_PAGE_SIZE, cursor.as_ref(), cx)
                    .await?)
            })
            .await
        });
        async move {
            let conversations = scanned.await?;
            let mut total = (USAGE_DOC.definition().initial)();
            for conversation in conversations {
                if let Some(value) = core
                    .session
                    .snapshot(&USAGE_DOC, conversation.id, &cx)
                    .await?
                {
                    let state: UsageState = from_json(&JsonValue::Object(value))?;
                    add_usage_state(&mut total, &state);
                }
            }
            Ok(total)
        }
        .boxed()
    }

    /// Seal admission, join task invocations, settle admitted commits, then
    /// close Storage. Later Harness operations reject with `Harness is
    /// closed`.
    ///
    /// # Errors
    ///
    /// The Storage close failure, or `cx`'s abort reason when the caller
    /// stops waiting; closing continues either way.
    #[must_use]
    pub fn close(&self, cx: &Context) -> BoxFuture<'static, SessionResult<()>> {
        self.core.closed.store(true, Ordering::SeqCst);
        self.core.session.close(cx).boxed()
    }
}

/// `Date.now()`: wall-clock milliseconds since the Unix epoch.
fn system_now() -> f64 {
    let elapsed = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default();
    #[expect(
        clippy::cast_precision_loss,
        reason = "epoch milliseconds stay below 2^53"
    )]
    let millis = elapsed.as_millis() as f64;
    millis
}
