//! Each conversation's last context read, kept in memory while it is busy
//! and for `settings.context_retention_ms` once idle (`harness/scheduler.ts`
//! `#contexts`).

use std::sync::Arc;
use std::time::Duration;

use eukhe_chord::context::Context;
use futures::future::BoxFuture;
use futures::FutureExt;

use super::Inner;
use crate::harness::context::{read_context_from, ContextRange};
use crate::harness::types::ContextView;
use crate::session::SessionResult;
use crate::types::{ConversationId, EntryId};

/// Longest delay `setTimeout` supports.
const MAX_TIMER_DELAY: f64 = 2_147_483_647.0;

/// One conversation's kept context. `idle_since` is the Harness time it was
/// first seen idle.
pub(crate) struct KeptContext {
    pub(super) range: Arc<ContextRange>,
    pub(super) idle_since: Option<f64>,
}

/// The pending expiry timer and the Harness time it fires for.
pub(crate) struct Expiry {
    pub(super) at: f64,
    pub(super) timer: tokio::task::JoinHandle<()>,
}

impl Inner {
    /// `settings.context_retention_ms`. TS reports a throwing settings getter
    /// here and drops the kept contexts; a Rust settings source cannot fail.
    fn context_retention_ms(&self) -> f64 {
        (self.settings)().context_retention_ms
    }

    /// Resolve idle waiters, and drop each kept context whose conversation
    /// has been idle for the retention period.
    pub(super) fn settle_idle(&self) {
        self.resolve_idle_waiters();
        let now = (self.now)();
        let retention = self.context_retention_ms();
        {
            let mut state = self.lock();
            let idle: Vec<(ConversationId, bool)> = state
                .contexts
                .keys()
                .map(|id| (*id, state.idle(Some(*id))))
                .collect();
            for (conversation_id, idle) in idle {
                let Some(kept) = state.contexts.get_mut(&conversation_id) else {
                    continue;
                };
                if kept
                    .idle_since
                    .is_some_and(|idle_since| now - idle_since >= retention)
                {
                    state.contexts.remove(&conversation_id);
                } else if !idle {
                    kept.idle_since = None;
                } else if retention > 0.0 {
                    kept.idle_since.get_or_insert(now);
                } else {
                    state.contexts.remove(&conversation_id);
                }
            }
        }
        self.schedule_expiry();
    }

    /// Run [`Inner::settle_idle`] when the earliest idle context expires. A
    /// tokio timer never keeps the process alive, so one is always kept (TS
    /// keeps none where timers cannot be unreferenced).
    fn schedule_expiry(&self) {
        let retention = self.context_retention_ms();
        let now = (self.now)();
        let mut state = self.lock();
        let at = state
            .contexts
            .values()
            .filter_map(|kept| kept.idle_since.map(|idle_since| idle_since + retention))
            .reduce(f64::min);
        if state.expiry.as_ref().map(|expiry| expiry.at) == at {
            return;
        }
        if let Some(expiry) = state.expiry.take() {
            expiry.timer.abort();
        }
        let Some(at) = at else {
            return;
        };
        if state.closing {
            return;
        }
        let delay = (at - now).clamp(0.0, MAX_TIMER_DELAY);
        let this = self.this.clone();
        let timer = tokio::spawn(async move {
            tokio::time::sleep(Duration::from_secs_f64(delay / 1000.0)).await;
            if let Some(inner) = this.upgrade() {
                inner.lock().expiry = None;
                inner.settle_idle();
            }
        });
        state.expiry = Some(Expiry { at, timer });
    }

    /// `runtime.context()`: read through the conversation's kept range, and
    /// keep the new one unless the invocation ended or a concurrent read
    /// already kept a newer range.
    pub(super) fn read_kept_context(
        self: &Arc<Self>,
        conversation_id: ConversationId,
        at: Option<EntryId>,
        cx: &Context,
        ended: impl Fn() -> bool + Send + 'static,
    ) -> BoxFuture<'static, SessionResult<ContextView>> {
        let inner = Arc::clone(self);
        let cx = cx.clone();
        async move {
            let previous = inner
                .lock()
                .contexts
                .get(&conversation_id)
                .map(|kept| Arc::clone(&kept.range));
            let (view, range) =
                read_context_from(&inner.session, conversation_id, &cx, at, previous).await?;
            let Some(range) = range else {
                return Ok(view);
            };
            let retention = inner.context_retention_ms();
            let now = (inner.now)();
            let schedule = {
                let mut state = inner.lock();
                let kept = state.contexts.get(&conversation_id);
                if state.closing
                    || ended()
                    || kept.is_some_and(|kept| kept.range.bounds.tail > range.bounds.tail)
                {
                    false
                } else if !state.idle(Some(conversation_id)) {
                    state.contexts.insert(
                        conversation_id,
                        KeptContext {
                            range,
                            idle_since: None,
                        },
                    );
                    false
                } else if retention > 0.0 {
                    // A read of another, idle conversation starts or continues
                    // its retention period.
                    let idle_since = kept.and_then(|kept| kept.idle_since).unwrap_or(now);
                    state.contexts.insert(
                        conversation_id,
                        KeptContext {
                            range,
                            idle_since: Some(idle_since),
                        },
                    );
                    true
                } else {
                    false
                }
            };
            if schedule {
                inner.schedule_expiry();
            }
            Ok(view)
        }
        .boxed()
    }
}
