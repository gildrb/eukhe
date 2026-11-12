//! The connection's event pump over one session's main conversation: the
//! durable agent events translated to session events, plus
//! the `goal_update` frames of the conversation's goal (TS forwards
//! `event.event` verbatim and `_emitGoalUpdate` on goal changes), the
//! `loop_update` frames of its loop and the `budget_update` frames of the
//! session's budget. Frames go through the connection outputs, so a
//! pending prompt response still precedes them.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_core::durable::budget::BudgetGate;
use eukhe_core::durable::goals::watch_goal_updates;
use eukhe_core::durable::loop_mode::watch_loop_updates;
use eukhe_core::durable::EukheSession;
use eukhe_core::goals::GoalState;
use eukhe_durable::harness::{watch_events, AgentEventBatch, AgentEventStream};
use eukhe_durable::session::SessionResult;
use eukhe_types::budget::BudgetReport;
use eukhe_types::daemon::SessionEvent;
use eukhe_types::loop_mode::LoopStatus;
use futures::future::{self, FutureExt};
use tokio::task::JoinHandle;

use super::session::ConnectionOutputs;
use crate::worker::durable_host::translator::{CoalesceMode, EventTranslator};

/// The pump's translation state: the shared event translator (which also
/// fills each run's `agent_end` messages).
struct Translation {
    translator: EventTranslator,
}

impl Translation {
    fn frames(&mut self, batch: &AgentEventBatch) -> Vec<SessionEvent> {
        self.translator.translate_batch(batch)
    }
}

/// One attached pump. [`EventPump::stop`] detaches it; dropping it without
/// a stop leaves the event watch to the Harness close.
pub(crate) struct EventPump {
    stream: AgentEventStream,
    translation: Arc<Mutex<Translation>>,
    outputs: ConnectionOutputs,
    goals: JoinHandle<()>,
    loops: JoinHandle<()>,
    budgets: JoinHandle<()>,
}

/// The change gate of the `goal_update`, `loop_update` and `budget_update`
/// frames: record `next` as the connection's last published value and
/// answer whether it differs from the one before.
fn changed<T: PartialEq + Clone>(last: &Mutex<T>, next: &T) -> bool {
    let mut last = last.lock().unwrap_or_else(PoisonError::into_inner);
    if *last == *next {
        false
    } else {
        last.clone_from(next);
        true
    }
}

impl EventPump {
    /// Attach to `session`'s current main conversation. `last_goal` is the
    /// connection's last published goal: a `goal_update` frame publishes
    /// only when the goal differs from it (TS change-gated emits), so the
    /// watch's first value (the current goal) publishes nothing unless it
    /// changed across a replacement. `last_loop` gates the `loop_update`
    /// frames and `last_budget` the `budget_update` frames of the
    /// session's budget the same way.
    ///
    /// # Errors
    ///
    /// The event, goal or loop watch cannot attach (the Harness is closed).
    pub(crate) async fn attach(
        session: &EukheSession,
        outputs: &ConnectionOutputs,
        last_goal: &Arc<Mutex<GoalState>>,
        last_loop: &Arc<Mutex<LoopStatus>>,
        last_budget: &Arc<Mutex<Option<BudgetReport>>>,
        cx: &Context,
    ) -> SessionResult<Self> {
        let conversation_id = session.main().id();
        let stream = watch_events(session.harness(), conversation_id, cx).await?;
        let translation = Arc::new(Mutex::new(Translation {
            translator: EventTranslator::new(stream.snapshot(), CoalesceMode::Immediate),
        }));
        let listener_translation = Arc::clone(&translation);
        let listener_outputs = outputs.clone();
        stream.start(Arc::new(move |batch: AgentEventBatch, _cx: Context| {
            let frames = listener_translation
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .frames(&batch);
            listener_outputs.write_events(frames);
            future::ready(Ok(())).boxed()
        }))?;
        let mut updates = watch_goal_updates(session.harness(), conversation_id, cx)?;
        let mut loop_updates = watch_loop_updates(session.harness(), conversation_id, cx)?;
        let goal_outputs = outputs.clone();
        let last_goal = Arc::clone(last_goal);
        let goals = tokio::spawn(async move {
            while let Some(goal) = updates.next().await {
                if changed(&last_goal, &goal) {
                    goal_outputs.write_events([SessionEvent::GoalUpdate { goal }]);
                }
            }
        });
        let loop_outputs = outputs.clone();
        let last_loop = Arc::clone(last_loop);
        let loops = tokio::spawn(async move {
            while let Some(status) = loop_updates.next().await {
                if changed(&last_loop, &status) {
                    loop_outputs.write_events([SessionEvent::LoopUpdate { r#loop: status }]);
                }
            }
        });
        let budgets = tokio::spawn(forward_budget(
            session.budget(),
            outputs.clone(),
            Arc::clone(last_budget),
        ));
        Ok(Self {
            stream,
            translation,
            outputs: outputs.clone(),
            goals,
            loops,
            budgets,
        })
    }

    /// Detach: stop the event watch, publish the translator's held frame,
    /// and end the goal, loop and budget watches.
    pub(crate) async fn stop(self) {
        // The watch's terminal result carries nothing the connection
        // reports: the pump only ever stops on purpose.
        let _end = self.stream.stop().await;
        let held = self
            .translation
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .translator
            .flush();
        self.outputs.write_events(held);
        self.goals.abort();
        self.loops.abort();
        self.budgets.abort();
    }
}

/// Publish the session's budget, then each change of it, as one
/// `budget_update` frame whenever it differs from `last` (the connection's
/// last published budget). The first read is ledger file IO, on the
/// blocking pool.
#[tracing::instrument(skip_all)]
#[expect(
    clippy::assigning_clones,
    reason = "a changed budget was moved into its event: nothing to clone into"
)]
async fn forward_budget(
    gate: Arc<BudgetGate>,
    outputs: ConnectionOutputs,
    last: Arc<Mutex<Option<BudgetReport>>>,
) {
    // Subscribed before the first read: a change the read misses is
    // delivered after it.
    let mut updates = gate.watch();
    let mut budget = match tokio::task::spawn_blocking(move || gate.report()).await {
        Ok(budget) => budget,
        Err(error) => {
            eprintln!("eukhe rpc: reading the session's budget did not finish: {error}");
            return;
        }
    };
    loop {
        if changed(&last, &budget) {
            outputs.write_events([SessionEvent::BudgetUpdate { budget }]);
        }
        if updates.changed().await.is_err() {
            return;
        }
        budget = updates.borrow_and_update().clone();
    }
}
