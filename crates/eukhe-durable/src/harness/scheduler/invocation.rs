//! One in-memory execution of a task in run or abort mode (spec §5.4
//! `TaskInvocation`): its mode, abort controller, handler context, watches,
//! and completion.

use std::future::Future;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{with_abort_signal, AbortController, AbortSignal, Context};
use tokio::sync::watch;

use crate::session::{DocumentWatch, SessionError};
use crate::types::{ConversationId, TaskId};

/// Whether an invocation runs phase handlers or the abort handler.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum InvocationMode {
    /// Phase handlers in sequence.
    Run,
    /// The abort handler, once.
    Abort,
}

/// One in-memory execution of a task.
pub(crate) struct Invocation {
    pub(super) task_id: TaskId,
    pub(super) conversation_id: ConversationId,
    pub(super) mode: InvocationMode,
    pub(super) controller: AbortController,
    /// Context passed to handlers; cancelled by `controller`.
    pub(super) context: Context,
    /// Watches acquired through the runtime, by acquisition number; stopped
    /// at invocation end.
    watches: Mutex<Vec<(u64, DocumentWatch)>>,
    next_watch: AtomicU64,
    ended: AtomicBool,
    done: watch::Sender<bool>,
}

impl Invocation {
    pub(super) fn new(
        task_id: TaskId,
        conversation_id: ConversationId,
        mode: InvocationMode,
        scheduler_context: &Context,
    ) -> Self {
        let controller = AbortController::new();
        let context = with_abort_signal(&controller.signal(), scheduler_context);
        Self {
            task_id,
            conversation_id,
            mode,
            controller,
            context,
            watches: Mutex::new(Vec::new()),
            next_watch: AtomicU64::new(0),
            ended: AtomicBool::new(false),
            done: watch::channel(false).0,
        }
    }

    pub(super) fn signal(&self) -> AbortSignal {
        self.controller.signal()
    }

    pub(super) fn ended(&self) -> bool {
        self.ended.load(Ordering::SeqCst)
    }

    /// Mark the invocation ended; `false` when it already was.
    pub(super) fn mark_ended(&self) -> bool {
        !self.ended.swap(true, Ordering::SeqCst)
    }

    /// `Task {id} invocation has ended`.
    pub(super) fn ended_error(&self) -> SessionError {
        ended_error(self.task_id)
    }

    /// Fail with [`Self::ended_error`] once the invocation ended.
    pub(super) fn check(&self) -> Result<(), SessionError> {
        if self.ended() {
            return Err(self.ended_error());
        }
        Ok(())
    }

    /// Resolve every `done()` waiter.
    pub(super) fn finish(&self) {
        self.done.send_replace(true);
    }

    /// Settles once the invocation finished.
    pub(super) fn done(&self) -> impl Future<Output = ()> + Send + 'static {
        let mut receiver = self.done.subscribe();
        async move {
            // The sender lives in the invocation, which every waiter's
            // scheduler keeps alive until `finish()`; a dropped sender means
            // the invocation is gone, which also counts as done.
            let _ = receiver.wait_for(|done| *done).await;
        }
    }

    /// Track a watch acquired through the runtime; returns its key.
    pub(super) fn add_watch(&self, watch: DocumentWatch) -> u64 {
        let key = self.next_watch.fetch_add(1, Ordering::Relaxed);
        self.lock_watches().push((key, watch));
        key
    }

    pub(super) fn remove_watch(&self, key: u64) {
        self.lock_watches().retain(|(other, _)| *other != key);
    }

    /// Stop every tracked watch.
    pub(super) fn stop_watches(&self) {
        let watches: Vec<DocumentWatch> = self
            .lock_watches()
            .iter()
            .map(|(_, watch)| watch.clone())
            .collect();
        for watch in watches {
            // `stop()` terminates synchronously; its `closed` future is not awaited.
            drop(watch.stop());
        }
    }

    fn lock_watches(&self) -> std::sync::MutexGuard<'_, Vec<(u64, DocumentWatch)>> {
        self.watches.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// `Task {id} invocation has ended`.
pub(super) fn ended_error(task_id: TaskId) -> SessionError {
    SessionError::error(format!("Task {task_id} invocation has ended"))
}

/// An invocation a conversation handle is bound to: its signal, and a check
/// that fails once it ended (TS `InvocationBinding`).
#[derive(Clone)]
pub(crate) struct InvocationBinding {
    invocation: Arc<Invocation>,
}

impl InvocationBinding {
    pub(super) fn new(invocation: Arc<Invocation>) -> Self {
        Self { invocation }
    }

    /// The invocation's signal; aborted when it is signalled or ends.
    #[must_use]
    pub(crate) fn signal(&self) -> AbortSignal {
        self.invocation.signal()
    }

    /// Fail once the invocation ended.
    ///
    /// # Errors
    ///
    /// `Task {id} invocation has ended`.
    pub(crate) fn check(&self) -> Result<(), SessionError> {
        self.invocation.check()
    }
}
