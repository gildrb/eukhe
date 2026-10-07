//! The erased runtime of one invocation (TS `#runtime`): every operation
//! rejects after the invocation ends, runtime commits are gated on the line,
//! and watches acquired through it stop when it ends.

use std::future::Future;
use std::sync::Arc;
use std::time::Duration;

use eukhe_chord::context::{await_with_context, with_abort_signal, AbortSignal, Context};
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_pi_ai::models::Models;
use futures::future::{BoxFuture, FutureExt};

use crate::documents::{AnyDocDefinition, ResolvedAddress};
use crate::env::ExecutionEnv;
use crate::harness::agent::agent_hooks;
use crate::harness::context::read_context;
use crate::harness::types::{
    Agent, ContextView, ConversationHandle, HookHandlers, RegistrySnapshot, Settings,
};
use crate::harness::util::closed_error;
use crate::session::{DocumentWatch, SessionError, SessionResult, TransactionScope, Tx};
use crate::tasks::{RunningTask, SettledTask, TaskCommitChange, TaskRuntimeBackend};
use crate::types::{
    AnyTaskRecord, ConversationId, DocumentObserver, DocumentReader, EntryId, EntryRecord, TaskId,
    TaskOutcome, TaskState, TaskStatus,
};

use super::execution::{AgentResolution, Phase};
use super::invocation::{Invocation, InvocationBinding, InvocationMode};
use super::Inner;

/// Longest delay `setTimeout` supports; longer sleeps wait in several steps.
const MAX_TIMER_DELAY: f64 = 2_147_483_647.0;

/// Runtime of one invocation, serving the phase handler its phase describes.
pub(super) struct InvocationRuntime {
    inner: Arc<Inner>,
    invocation: Arc<Invocation>,
    phase: Arc<Phase>,
}

impl InvocationRuntime {
    pub(super) fn new(inner: Arc<Inner>, invocation: Arc<Invocation>, phase: Arc<Phase>) -> Self {
        Self {
            inner,
            invocation,
            phase,
        }
    }

    /// Resolved at most once per phase handler, at first use, with the
    /// invocation's context; fixed for the phase. The resolution runs eagerly,
    /// so a caller that stops waiting leaves it to the next caller.
    fn agent_resolution(&self) -> SessionResult<AgentResolution> {
        self.invocation.check()?;
        let resolve = Arc::clone(&self.inner.agent);
        let conversation_id = self.invocation.conversation_id;
        let context = self.invocation.context.clone();
        Ok(self.phase.agent(move |snapshot| {
            let handle = tokio::spawn(resolve(conversation_id, snapshot.clone(), context));
            async move { joined(handle).await.map(Arc::new) }
                .boxed()
                .shared()
        }))
    }

    /// Run a committed-state read unless the invocation has ended. `read`
    /// runs now, so a read that queues on the Session line queues at call
    /// time.
    fn read<T: Send + 'static>(
        &self,
        read: impl FnOnce() -> BoxFuture<'static, SessionResult<T>>,
    ) -> BoxFuture<'static, SessionResult<T>> {
        match self.invocation.check() {
            Ok(()) => read(),
            Err(error) => futures::future::ready(Err(error)).boxed(),
        }
    }

    /// Commit after rereading the task on the line and gating the invocation.
    fn gated<T, F, Fut>(&self, change: F, cx: &Context) -> BoxFuture<'static, SessionResult<T>>
    where
        T: Send + 'static,
        F: FnOnce(Tx, AnyTaskRecord) -> Fut + Send + 'static,
        Fut: Future<Output = SessionResult<T>> + Send + 'static,
    {
        if let Err(error) = self.invocation.check() {
            return futures::future::ready(Err(error)).boxed();
        }
        let inner = Arc::clone(&self.inner);
        let invocation = Arc::clone(&self.invocation);
        let scope = TransactionScope {
            conversation_id: Some(invocation.conversation_id),
            task_id: Some(invocation.task_id),
        };
        self.inner
            .session
            .commit_with(
                move |tx| async move {
                    invocation.check()?;
                    let found = {
                        let state = inner.lock();
                        if state.closing {
                            return Err(closed_error());
                        }
                        state.live.get(&invocation.task_id).cloned()
                    };
                    let id = invocation.task_id;
                    let Some(current) = found else {
                        return Err(SessionError::error(format!("Task {id} is terminal")));
                    };
                    let status = current.state.status();
                    if status != TaskStatus::Running {
                        let status = status_name(status);
                        return Err(SessionError::error(format!("Task {id} is {status}")));
                    }
                    if invocation.mode == InvocationMode::Run && current.abort_requested {
                        return Err(SessionError::error(format!(
                            "Task {id} has a durable abort mark"
                        )));
                    }
                    change(tx, current).await
                },
                cx,
                scope,
            )
            .boxed()
    }
}

impl TaskRuntimeBackend for InvocationRuntime {
    fn task_id(&self) -> TaskId {
        self.invocation.task_id
    }

    fn conversation_id(&self) -> ConversationId {
        self.invocation.conversation_id
    }

    fn signal(&self) -> AbortSignal {
        self.invocation.signal()
    }

    fn registry(&self) -> RegistrySnapshot {
        self.phase.snapshot()
    }

    fn agent(&self, cx: &Context) -> BoxFuture<'static, SessionResult<Arc<Agent>>> {
        let resolution = match self.agent_resolution() {
            Ok(resolution) => resolution,
            Err(error) => return futures::future::ready(Err(error)).boxed(),
        };
        let cx = cx.clone();
        async move {
            await_with_context(resolution, &cx)
                .await
                .map_err(SessionError::Aborted)?
        }
        .boxed()
    }

    fn settings(&self) -> Settings {
        (self.inner.settings)()
    }

    fn models(&self) -> Models {
        self.inner.models.clone()
    }

    fn env(
        &self,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ExecutionEnv>>>> {
        let env = Arc::clone(&self.inner.env);
        let conversation_id = self.invocation.conversation_id;
        let cx = cx.clone();
        self.read(move || env(conversation_id, cx))
    }

    fn report_failure(&self, error: SessionError) {
        self.inner.report(error);
    }

    fn hook_handlers(&self) -> BoxFuture<'static, SessionResult<Vec<HookHandlers>>> {
        let resolution = match self.agent_resolution() {
            Ok(resolution) => resolution,
            Err(error) => return futures::future::ready(Err(error)).boxed(),
        };
        let phase = Arc::clone(&self.phase);
        async move {
            let agent = resolution.await?;
            Ok(agent_hooks(&agent, phase.task().name()))
        }
        .boxed()
    }

    fn commit(
        &self,
        change: TaskCommitChange,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        let inner = Arc::clone(&self.inner);
        let invocation = Arc::clone(&self.invocation);
        self.gated(
            move |tx, current| async move {
                let running = RunningTask::from_record(current.clone()).ok_or_else(|| {
                    SessionError::error(format!("Task {} is not running", current.id))
                })?;
                if let Some(next) = change(tx.clone(), running).await? {
                    inner.commit_state(&tx, &invocation, &current, next).await?;
                }
                Ok(())
            },
            cx,
        )
    }

    fn memo(
        &self,
        name: &str,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<JsonValue>>> {
        let inner = Arc::clone(&self.inner);
        let id = self.invocation.task_id;
        let name = name.to_owned();
        self.read(move || {
            let memo = memo_of(inner.lock().live.get(&id), &name);
            futures::future::ready(Ok(memo)).boxed()
        })
    }

    fn memo_or_store(
        &self,
        name: &str,
        candidate: JsonValue,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<JsonValue>> {
        let name = name.to_owned();
        self.gated(
            move |tx, current| async move {
                if let Some(winner) = memo_of(Some(&current), &name) {
                    return Ok(winner);
                }
                let mut memos = current
                    .memos
                    .as_deref()
                    .cloned()
                    .unwrap_or_else(JsonObject::new);
                memos.insert(name, candidate.clone());
                tx.set_task(AnyTaskRecord {
                    memos: Some(Arc::new(memos)),
                    ..current
                })?;
                Ok(candidate)
            },
            cx,
        )
    }

    fn get_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<AnyTaskRecord>>> {
        let inner = Arc::clone(&self.inner);
        let cx = cx.clone();
        self.read(move || {
            let storage = Arc::clone(&inner.storage);
            inner
                .session
                .read_on_line(async move { Ok(storage.task(id, &cx).await?) })
                .boxed()
        })
    }

    fn wait_for_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SettledTask>> {
        let inner = Arc::clone(&self.inner);
        let cx = with_abort_signal(&self.invocation.signal(), cx);
        self.read(move || inner.wait_for_task(id, &cx))
    }

    fn outcomes(
        &self,
        ids: Vec<TaskId>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Vec<TaskOutcome>>> {
        let inner = Arc::clone(&self.inner);
        let cx = cx.clone();
        self.read(move || {
            let storage = Arc::clone(&inner.storage);
            inner
                .session
                .read_on_line(async move {
                    let mut outcomes = Vec::with_capacity(ids.len());
                    for id in ids {
                        let record = storage.task(id, &cx).await?;
                        let Some(TaskState::Terminal { outcome }) =
                            record.map(|record| record.state)
                        else {
                            return Err(SessionError::error(format!("Task {id} is not terminal")));
                        };
                        outcomes.push(outcome);
                    }
                    Ok(outcomes)
                })
                .boxed()
        })
    }

    fn conversation(
        &self,
        id: ConversationId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ConversationHandle>>>> {
        let conversation = Arc::clone(&self.inner.conversation);
        let binding = InvocationBinding::new(Arc::clone(&self.invocation));
        let cx = cx.clone();
        self.read(move || conversation(id, binding, cx))
    }

    fn entry(
        &self,
        id: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<EntryRecord>>> {
        let inner = Arc::clone(&self.inner);
        let conversation_id = self.invocation.conversation_id;
        let cx = cx.clone();
        self.read(move || {
            let storage = Arc::clone(&inner.storage);
            inner
                .session
                .read_on_line(async move {
                    let found = storage.entry_in(conversation_id, id, &cx).await?;
                    Ok(found.map(|stored| stored.entry))
                })
                .boxed()
        })
    }

    fn context(
        &self,
        conversation_id: ConversationId,
        at: Option<EntryId>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<ContextView>> {
        let session = self.inner.session.clone();
        let cx = cx.clone();
        self.read(move || {
            async move { read_context(&session, conversation_id, &cx, at).await }.boxed()
        })
    }

    fn now(&self) -> SessionResult<f64> {
        self.invocation.check()?;
        Ok((self.inner.now)())
    }

    fn report(&self, error: SessionError) -> SessionResult<()> {
        self.invocation.check()?;
        self.inner.report(error);
        Ok(())
    }

    /// Wait until the Harness clock reaches `until`, rechecking it after every
    /// timer.
    fn sleep(&self, until: f64, cx: &Context) -> BoxFuture<'static, SessionResult<()>> {
        if let Err(error) = self.invocation.check() {
            return futures::future::ready(Err(error)).boxed();
        }
        let mut signals = vec![self.invocation.signal()];
        signals.extend(cx.abort_signal());
        let signal = AbortSignal::any(&signals);
        let now = Arc::clone(&self.inner.now);
        async move {
            loop {
                signal.throw_if_aborted().map_err(SessionError::Aborted)?;
                let remaining = until - now();
                if remaining <= 0.0 {
                    return Ok(());
                }
                delay(remaining.min(MAX_TIMER_DELAY), &signal).await?;
            }
        }
        .boxed()
    }
}

impl DocumentReader for InvocationRuntime {
    fn snapshot_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        let session = self.inner.session.clone();
        let cx = cx.clone();
        self.read(move || session.snapshot_at(&definition, resolved, &cx))
    }

    fn snapshot_as_of_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        at: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        let session = self.inner.session.clone();
        let cx = cx.clone();
        self.read(move || session.snapshot_as_of_at(&definition, resolved, at, &cx))
    }
}

impl DocumentObserver for InvocationRuntime {
    fn watch_doc_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>> {
        if let Err(error) = self.invocation.check() {
            return futures::future::ready(Err(error)).boxed();
        }
        let watching = self.inner.session.watch_doc_at(&definition, resolved, cx);
        let invocation = Arc::clone(&self.invocation);
        async move {
            let Some(watch) = watching.await? else {
                return Ok(None);
            };
            if invocation.ended() {
                drop(watch.stop());
                return Err(invocation.ended_error());
            }
            let key = invocation.add_watch(watch.clone());
            let closed = watch.closed();
            let weak = Arc::downgrade(&invocation);
            tokio::spawn(async move {
                closed.await;
                if let Some(invocation) = weak.upgrade() {
                    invocation.remove_watch(key);
                }
            });
            Ok(Some(watch))
        }
        .boxed()
    }
}

/// Own memo entry only.
fn memo_of(record: Option<&AnyTaskRecord>, name: &str) -> Option<JsonValue> {
    record?.memos.as_ref()?.get(name).cloned()
}

/// The TS status string of a live state.
fn status_name(status: TaskStatus) -> &'static str {
    match status {
        TaskStatus::Pending => "pending",
        TaskStatus::Running => "running",
        TaskStatus::Waiting => "waiting",
        TaskStatus::Completing => "completing",
        TaskStatus::Terminal => "terminal",
    }
}

/// One timer of at most [`MAX_TIMER_DELAY`] milliseconds; rejects with the
/// signal's reason when it aborts first. Like `setTimeout`, delays below one
/// millisecond wait one.
async fn delay(ms: f64, signal: &AbortSignal) -> SessionResult<()> {
    let ms = if ms >= 1.0 { ms } else { 1.0 };
    tokio::select! {
        () = tokio::time::sleep(Duration::from_secs_f64(ms / 1000.0)) => Ok(()),
        reason = signal.cancelled() => Err(SessionError::Aborted(reason)),
    }
}

/// Await a spawned resolution, resuming its panic.
async fn joined<T>(handle: tokio::task::JoinHandle<SessionResult<T>>) -> SessionResult<T> {
    match handle.await {
        Ok(result) => result,
        Err(error) => match error.try_into_panic() {
            Ok(panic) => std::panic::resume_unwind(panic),
            Err(error) => Err(SessionError::other(error)),
        },
    }
}
