//! Task and idle waits: a terminal receipt, or no live non-background task in
//! an ordinary traversal scope.

use std::future::Future;

use eukhe_chord::context::Context;
use futures::future::{BoxFuture, FutureExt};

use crate::harness::util::closed_error;
use crate::session::{SessionError, SessionResult};
use crate::tasks::SettledTask;
use crate::types::{ConversationId, TaskId};

use super::{Inner, TaskScheduler};

impl TaskScheduler {
    /// Resolve with the task's terminal receipt.
    ///
    /// # Errors
    ///
    /// `Task {id} does not exist`, `Harness is closed`, a cancelled `cx`, or a
    /// Session failure.
    pub(crate) fn wait_for_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> impl Future<Output = SessionResult<SettledTask>> + Send + 'static {
        self.inner.wait_for_task(id, cx)
    }

    /// Resolve when ordinary traversal from the conversation, or from every
    /// ownerless conversation for `None`, reaches no live non-background task.
    ///
    /// # Errors
    ///
    /// `Harness is closed`, or a cancelled `cx`.
    pub(crate) fn wait_for_idle(
        &self,
        conversation_id: Option<ConversationId>,
        cx: &Context,
    ) -> impl Future<Output = SessionResult<()>> + Send + 'static {
        self.inner.wait_for_idle(conversation_id, cx)
    }
}

impl Inner {
    pub(super) fn wait_for_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SettledTask>> {
        let inner = self.arc();
        let cx = cx.clone();
        // Check and register on the line so no terminal publication falls between them.
        let found = self.session.read_on_line(async move {
            let waiting = {
                let state = inner.lock();
                if state.closing {
                    return Err(closed_error(&inner.session));
                }
                state
                    .live
                    .contains_key(&id)
                    .then(|| state.task_waiters.add(id, &cx))
            };
            if let Some(waiting) = waiting {
                return Ok(waiting.boxed());
            }
            let record = inner.storage.task(id, &cx).await?;
            let settled = record
                .and_then(SettledTask::from_record)
                .ok_or_else(|| SessionError::error(format!("Task {id} does not exist")))?;
            Ok(futures::future::ready(Ok(settled)).boxed())
        });
        async move { found.await?.await }.boxed()
    }

    pub(super) fn wait_for_idle(
        &self,
        conversation_id: Option<ConversationId>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        let waiting = {
            let state = self.lock();
            if state.closing {
                return futures::future::ready(Err(closed_error(&self.session))).boxed();
            }
            if state.idle(conversation_id) {
                return futures::future::ready(Ok(())).boxed();
            }
            state.idle_waiters.add(conversation_id, cx)
        };
        self.schedule_reconcile();
        waiting.boxed()
    }
}
