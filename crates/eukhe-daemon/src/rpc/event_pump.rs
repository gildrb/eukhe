//! The connection's event pump over one session's main conversation: the
//! durable agent events translated to the TS session-event frames, plus
//! the `goal_update` frames of the conversation's goal (TS forwards
//! `event.event` verbatim and `_emitGoalUpdate` on goal changes). Frames
//! go through the connection outputs, so a pending prompt response still
//! precedes them.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_core::durable::goals::watch_goal_updates;
use eukhe_core::durable::EukheSession;
use eukhe_core::goals::GoalState;
use eukhe_durable::harness::{watch_events, AgentEventBatch, AgentEventStream};
use eukhe_durable::session::SessionResult;
use futures::future::{self, FutureExt};
use serde_json::{json, Value};
use tokio::task::JoinHandle;

use super::session::ConnectionOutputs;
use crate::worker::durable_host::translator::{CoalesceMode, EventTranslator};

/// The pump's translation state: the shared event translator (which also
/// fills each run's `agent_end` messages).
struct Translation {
    translator: EventTranslator,
}

impl Translation {
    fn frames(&mut self, batch: &AgentEventBatch) -> Vec<Value> {
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
}

impl EventPump {
    /// Attach to `session`'s current main conversation. `last_goal` is the
    /// connection's last published goal: a `goal_update` frame publishes
    /// only when the goal differs from it (TS change-gated emits), so the
    /// watch's first value (the current goal) publishes nothing unless it
    /// changed across a replacement.
    ///
    /// # Errors
    ///
    /// The event or goal watch cannot attach (the Harness is closed).
    pub(crate) async fn attach(
        session: &EukheSession,
        outputs: &ConnectionOutputs,
        last_goal: &Arc<Mutex<GoalState>>,
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
            listener_outputs.write_all(frames);
            future::ready(Ok(())).boxed()
        }))?;
        let mut updates = watch_goal_updates(session.harness(), conversation_id, cx)?;
        let goal_outputs = outputs.clone();
        let last_goal = Arc::clone(last_goal);
        let goals = tokio::spawn(async move {
            while let Some(goal) = updates.next().await {
                let changed = {
                    let mut last = last_goal.lock().unwrap_or_else(PoisonError::into_inner);
                    if *last == goal {
                        false
                    } else {
                        last.clone_from(&goal);
                        true
                    }
                };
                if changed {
                    goal_outputs.write(json!({ "type": "goal_update", "goal": goal }));
                }
            }
        });
        Ok(Self {
            stream,
            translation,
            outputs: outputs.clone(),
            goals,
        })
    }

    /// Detach: stop the event watch, publish the translator's held frame,
    /// and end the goal watch.
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
        if let Some(frame) = held {
            self.outputs.write(frame);
        }
        self.goals.abort();
    }
}
