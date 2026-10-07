//! Durable task scheduler of one Harness (`harness/scheduler.ts`, spec
//! §5.1–§5.5).
//!
//! The live mirror holds every committed non-terminal task record: pending,
//! running, waiting, and completing. The synchronous commit listener updates
//! it on the Session line, so code running on the line reads exactly the
//! committed state from it.
//!
//! Tasks and conversations form one ownership tree (spec §5.5): a task's
//! parent is its owner task, or its conversation; a conversation's parent is
//! its owner task, if any. Walks up that tree decide cascades, idle scopes,
//! and whether a task's ordinary owned work is live, which holds its outcome
//! as `completing` and delays its abort handler.
//!
//! Invariant: every task transition is decided and written by one callback
//! serialized on the Session line. That covers reservation, marks, runtime
//! commits, finalization, and the synchronous step before each phase, which
//! applies the precedence rules and writes a fault or handover. Handlers and
//! joins run off the line. An invocation ends inside the step that decides
//! its end, so a runtime commit it queued either lands before that decision or
//! is rejected.

mod cascade;
mod execution;
mod invocation;
mod mirror;
mod ownership;
mod reservation;
mod runtime;
mod state;
#[cfg(test)]
mod tests;
mod waits;

use std::future::Future;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_pi_ai::models::Models;
use futures::future::BoxFuture;

use crate::env::ExecutionEnv;
use crate::harness::types::{
    Agent, ConversationHandle, RegistryReader, RegistrySnapshot, Settings,
};
use crate::session::{Session, SessionError, SessionResult, Tx};
use crate::types::{AnyTaskRecord, ConversationId, Storage, TaskOutcome, TaskOutcomeError};

pub(crate) use cascade::ConversationAbortReach;
pub use cascade::TaskAbortResult;
pub use execution::DefinitionKept;
pub(crate) use invocation::InvocationBinding;

use state::State;

const SCAN_PAGE_SIZE: usize = 256;

/// Terminal outcomes the scheduler writes without running task code (TS
/// `Extract<TaskOutcome, { status: "faulted" | "orphaned" }>`).
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum SchedulerOutcome {
    /// An uncaught error, no durable progress, or an abort handler without an
    /// outcome.
    Faulted {
        /// The fault.
        error: TaskOutcomeError,
    },
    /// An abort of a task no registered definition can take; the reason is the
    /// blocked reason (`missing_task`, `task_too_old`, `migration_failed`).
    Orphaned {
        /// Why the task cannot resume.
        reason: String,
    },
}

impl SchedulerOutcome {
    /// The outcome as persisted.
    #[must_use]
    pub(crate) fn outcome(&self) -> TaskOutcome<JsonValue> {
        match self {
            Self::Faulted { error } => TaskOutcome::Faulted {
                error: error.clone(),
            },
            Self::Orphaned { reason } => TaskOutcome::Orphaned {
                reason: reason.clone(),
            },
        }
    }
}

/// Resolve a conversation's agent against a snapshot; the runtime calls it at
/// most once per phase.
pub(crate) type AgentResolver = Arc<
    dyn Fn(ConversationId, RegistrySnapshot, Context) -> BoxFuture<'static, SessionResult<Agent>>
        + Send
        + Sync,
>;

/// Build a conversation's environment with `HarnessOptions.env`.
pub(crate) type EnvBuilder = Arc<
    dyn Fn(
            ConversationId,
            Context,
        ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ExecutionEnv>>>>
        + Send
        + Sync,
>;

/// Harness cleanup staged in the commit that makes an outcome the scheduler
/// wrote itself terminal.
pub(crate) type SettleOutcome = Arc<
    dyn Fn(Tx, AnyTaskRecord, SchedulerOutcome) -> BoxFuture<'static, SessionResult<()>>
        + Send
        + Sync,
>;

/// Withdraw a conversation's queued inputs, for conversation abort and abort
/// cascades.
pub(crate) type WithdrawInputs =
    Arc<dyn Fn(Tx, ConversationId) -> BoxFuture<'static, SessionResult<()>> + Send + Sync>;

/// Invocation-bound handle of an existing conversation, for task runtimes and
/// tools.
pub(crate) type ConversationSource = Arc<
    dyn Fn(
            ConversationId,
            InvocationBinding,
            Context,
        ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ConversationHandle>>>>
        + Send
        + Sync,
>;

/// Everything a scheduler needs from its Harness (TS `TaskSchedulerOptions`;
/// the storage is the Session's).
pub(crate) struct TaskSchedulerOptions {
    pub(crate) session: Session,
    pub(crate) registry: Arc<dyn RegistryReader>,
    pub(crate) models: Models,
    /// Resolve a conversation's agent against a snapshot; the runtime calls it
    /// at most once per phase.
    pub(crate) agent: AgentResolver,
    /// Resolve the settings; read at each access.
    pub(crate) settings: Arc<dyn Fn() -> Settings + Send + Sync>,
    /// Build a conversation's environment with `HarnessOptions.env`.
    pub(crate) env: EnvBuilder,
    /// The Harness clock, in milliseconds.
    pub(crate) now: Arc<dyn Fn() -> f64 + Send + Sync>,
    /// `HarnessOptions.onReport`.
    pub(crate) report: Arc<dyn Fn(SessionError) + Send + Sync>,
    /// Harness cleanup staged in the commit that makes an outcome the
    /// scheduler wrote itself terminal.
    pub(crate) settle_outcome: SettleOutcome,
    /// Withdraw a conversation's queued inputs, for conversation abort and
    /// abort cascades.
    pub(crate) withdraw_inputs: WithdrawInputs,
    /// Invocation-bound handle of an existing conversation, for task runtimes
    /// and tools.
    pub(crate) conversation: ConversationSource,
    /// Context for scheduler commits and invocations; carries no caller
    /// cancellation.
    pub(crate) context: Context,
}

/// Durable task scheduler of one Harness. Clones share the scheduler.
#[derive(Clone)]
pub(crate) struct TaskScheduler {
    inner: Arc<Inner>,
}

impl std::fmt::Debug for TaskScheduler {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("TaskScheduler")
            .finish_non_exhaustive()
    }
}

/// The shared scheduler: its options and the mutable state.
struct Inner {
    session: Session,
    storage: Arc<dyn Storage>,
    registry: Arc<dyn RegistryReader>,
    models: Models,
    agent: AgentResolver,
    settings: Arc<dyn Fn() -> Settings + Send + Sync>,
    env: EnvBuilder,
    now: Arc<dyn Fn() -> f64 + Send + Sync>,
    report: Arc<dyn Fn(SessionError) + Send + Sync>,
    settle_outcome: SettleOutcome,
    withdraw_inputs: WithdrawInputs,
    conversation: ConversationSource,
    context: Context,
    state: Mutex<State>,
    this: Weak<Inner>,
}

impl Inner {
    fn lock(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn arc(&self) -> Arc<Inner> {
        self.this
            .upgrade()
            .expect("a live scheduler reference exists while its methods run")
    }

    fn report(&self, error: SessionError) {
        (self.report)(error);
    }

    fn closing(&self) -> bool {
        self.lock().closing
    }
}

impl TaskScheduler {
    pub(crate) fn new(options: TaskSchedulerOptions) -> Self {
        let storage = Arc::clone(options.session.storage());
        Self {
            inner: Arc::new_cyclic(|this| Inner {
                session: options.session,
                storage,
                registry: options.registry,
                models: options.models,
                agent: options.agent,
                settings: options.settings,
                env: options.env,
                now: options.now,
                report: options.report,
                settle_outcome: options.settle_outcome,
                withdraw_inputs: options.withdraw_inputs,
                conversation: options.conversation,
                context: options.context,
                state: Mutex::new(State::default()),
                this: this.clone(),
            }),
        }
    }

    /// Load live tasks and change surviving `running` tasks back to `pending`.
    /// Dispatches nothing.
    ///
    /// # Errors
    ///
    /// A subscription or the open commit failed.
    pub(crate) async fn open(&self, cx: &Context) -> SessionResult<()> {
        self.inner.open(cx).await
    }

    /// Enable scheduling. Idempotent; the kick does nothing once closing.
    pub(crate) fn resume(&self) {
        self.inner.lock().enabled = true;
        self.inner.kick();
    }

    /// Wait for every invocation signalled by the close listener. Writes
    /// nothing.
    pub(crate) fn join(&self) -> impl Future<Output = ()> + Send + 'static {
        let done: Vec<_> = self
            .inner
            .lock()
            .invocations
            .values()
            .map(|invocation| invocation.done())
            .collect();
        async move {
            futures::future::join_all(done).await;
        }
    }
}
