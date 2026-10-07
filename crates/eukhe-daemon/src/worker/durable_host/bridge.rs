//! The event bridge of the shown conversation: `watch_events` batches are
//! translated to wire events under the session-core lock (so the event
//! sequence and the attach snapshot's mirror advance together), coalesced
//! `message_update`s flush every 50 ms, inbox changes become
//! `session_action_update` (with the queued inputs' previews read from the
//! `pi.inbox` document), and goal document changes become `goal_update`.

use std::future::Future;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};
use std::time::Duration;

use eukhe_chord::context::{with_cancel, CancelContext, Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::harness::{
    watch_events, AgentEvent, AgentEventBatch, AgentEventStream, Harness, InboxItem, InboxState,
    INBOX_DOC,
};
use eukhe_durable::session::{SessionError, SessionResult, WatchListenerError};
use eukhe_durable::types::{ConversationId, DocumentReaderExt, SubmissionId};
use eukhe_types::pi_ai::{UserContent, UserContentBlock};
use futures::FutureExt as _;
use serde_json::{json, Value};
use tokio::task::JoinHandle;

use super::translator::{CoalesceMode, EventTranslator};
use crate::worker::{EventPump, SessionCore};

/// How often a parked `message_update` flushes.
pub(crate) const UPDATE_FLUSH_INTERVAL: Duration = Duration::from_millis(50);

/// Bridges are numbered so a stopped bridge's late callbacks never touch
/// its successor's view.
static NEXT_EPOCH: AtomicU64 = AtomicU64::new(1);

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// How a queued input waits in the inbox.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum QueuedMode {
    Steer,
    FollowUp,
}

/// One queued input with its preview text.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct QueuedInput {
    pub(crate) id: SubmissionId,
    pub(crate) mode: QueuedMode,
    /// The queue-strip preview.
    pub(crate) text: String,
    pub(crate) content: UserContent,
}

/// The shown conversation's state on the session core.
pub(crate) struct ShownView {
    pub(crate) epoch: u64,
    pub(crate) translator: EventTranslator,
    /// Queued inputs (steer/follow-up) in inbox order; writes are not shown.
    pub(crate) inbox: Vec<QueuedInput>,
    /// The served goal (`goal_update` payload); `Null` without a goal.
    pub(crate) goal: Value,
}

impl ShownView {
    /// A run is active (pi.live `run` present).
    pub(crate) fn is_busy(&self) -> bool {
        self.translator.mirror().is_streaming()
    }
}

/// Run activity flips the bridge reports to the worker (journal busy
/// verdict, roster push, idle waiters).
pub(crate) type RunHook = Arc<dyn Fn(RunChange) + Send + Sync>;

/// A run started, retried, or ended on the shown conversation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RunChange {
    Started,
    /// An automatic provider retry began (the run stays busy).
    RetryStarted,
    /// The run ended; `error_hold` is the provider error of a run whose
    /// last assistant message failed (the pane's error hold).
    Ended { error_hold: Option<String> },
}

/// Where the bridge emits.
#[derive(Clone)]
pub(crate) struct BridgeSink {
    pub(crate) core: Arc<Mutex<SessionCore>>,
    pub(crate) events: Arc<EventPump>,
    pub(crate) on_run: RunHook,
}

/// A running bridge. Dropping it without [`EventBridge::stop`] cancels its
/// tasks too.
pub(crate) struct EventBridge {
    stream: AgentEventStream,
    cancel: CancelContext,
    tasks: Vec<JoinHandle<()>>,
}

impl Drop for EventBridge {
    fn drop(&mut self) {
        self.cancel.cancel(None);
        for task in &self.tasks {
            task.abort();
        }
    }
}

impl EventBridge {
    /// Resolves once every batch queued so far went through the listener.
    pub(crate) fn delivered(&self) -> impl Future<Output = ()> + Send + 'static {
        self.stream.delivered()
    }

    /// Attach to `conversation_id`'s events, install its view on the core,
    /// and start the listener, the flush timer, and the goal watch.
    ///
    /// # Errors
    ///
    /// The event stream or the inbox cannot be read.
    pub(crate) async fn start(
        harness: &Harness,
        conversation_id: ConversationId,
        sink: BridgeSink,
    ) -> SessionResult<Self> {
        let (cx, cancel) = with_cancel(&BACKGROUND_CONTEXT);
        let epoch = NEXT_EPOCH.fetch_add(1, Ordering::Relaxed);
        let stream = watch_events(harness, conversation_id, &cx).await?;
        let inbox = inbox_previews(harness, conversation_id, &cx).await?;
        let busy = {
            let mut core = lock(&sink.core);
            let view = ShownView {
                epoch,
                translator: EventTranslator::new(stream.snapshot(), CoalesceMode::Coalesced),
                inbox,
                goal: Value::Null,
            };
            let busy = view.is_busy();
            core.view = Some(view);
            crate::worker::emit_action_update_locked(&mut core, &sink.events);
            busy
        };
        if busy {
            (sink.on_run)(RunChange::Started);
        }
        stream.start(listener(
            harness.clone(),
            epoch,
            conversation_id,
            sink.clone(),
        ))?;
        let tasks = vec![
            tokio::spawn(flush_loop(epoch, sink.clone())),
            tokio::spawn(goal_loop(harness.clone(), epoch, conversation_id, sink, cx)),
        ];
        Ok(Self {
            stream,
            cancel,
            tasks,
        })
    }

    /// Stop delivering events; the core keeps the last view.
    pub(crate) async fn stop(self) {
        self.cancel.cancel(None);
        for task in &self.tasks {
            task.abort();
        }
        self.stream.stop().await;
    }
}

fn listener(
    harness: Harness,
    epoch: u64,
    conversation_id: ConversationId,
    sink: BridgeSink,
) -> eukhe_durable::harness::AgentEventListener {
    Arc::new(move |batch: AgentEventBatch, cx: Context| {
        let harness = harness.clone();
        let sink = sink.clone();
        async move {
            let inbox_changed = batch
                .iter()
                .any(|event| matches!(event, AgentEvent::InboxUpdate { .. } | AgentEvent::Snapshot(_)));
            let inbox = if inbox_changed {
                match inbox_previews(&harness, conversation_id, &cx).await {
                    Ok(inbox) => Some(inbox),
                    Err(error) => {
                        eprintln!("eukhe-daemon worker: reading the inbox for the queue projection failed: {error}");
                        None
                    }
                }
            } else {
                None
            };
            apply_batch(&sink, epoch, &batch, inbox);
            Ok::<(), WatchListenerError>(())
        }
        .boxed()
    })
}

/// Translate one batch into wire events under the core lock.
fn apply_batch(
    sink: &BridgeSink,
    epoch: u64,
    batch: &[AgentEvent],
    inbox: Option<Vec<QueuedInput>>,
) {
    let changes = {
        let mut core = lock(&sink.core);
        let Some(view) = core.view.as_mut().filter(|view| view.epoch == epoch) else {
            return;
        };
        view.active = super::queue_view::next_active(view.active.take(), &view.inbox, batch);
        let frames = view.translator.translate_batch(batch);
        if let Some(inbox) = inbox {
            view.inbox = inbox;
        }
        let changes = run_changes(&frames);
        for frame in frames {
            crate::worker::emit_event_locked(&mut core, &sink.events, frame);
        }
        crate::worker::emit_action_update_locked(&mut core, &sink.events);
        changes
    };
    for change in changes {
        (sink.on_run)(change);
    }
}

/// The run boundaries one batch's wire frames carry, in order: a run's
/// start, an automatic retry, and its end with the pane's error hold (a
/// follow-up run may end one run and start the next in one batch).
fn run_changes(frames: &[Value]) -> Vec<RunChange> {
    frames
        .iter()
        .filter_map(|frame| match frame.get("type").and_then(Value::as_str)? {
            "agent_start" => Some(RunChange::Started),
            "auto_retry_start" => Some(RunChange::RetryStarted),
            "agent_end" => Some(RunChange::Ended {
                error_hold: frame
                    .get("messages")
                    .and_then(Value::as_array)
                    .and_then(|messages| crate::herdr::error_hold_message(messages)),
            }),
            _ => None,
        })
        .collect()
}

async fn flush_loop(epoch: u64, sink: BridgeSink) {
    let mut interval = tokio::time::interval(UPDATE_FLUSH_INTERVAL);
    interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
    loop {
        interval.tick().await;
        let mut core = lock(&sink.core);
        let Some(view) = core.view.as_mut().filter(|view| view.epoch == epoch) else {
            return;
        };
        if let Some(frame) = view.translator.flush() {
            crate::worker::emit_event_locked(&mut core, &sink.events, frame);
        }
    }
}

async fn goal_loop(
    harness: Harness,
    epoch: u64,
    conversation_id: ConversationId,
    sink: BridgeSink,
    cx: Context,
) {
    let mut updates =
        match eukhe_core::durable::goals::watch_goal_updates(&harness, conversation_id, &cx) {
            Ok(updates) => updates,
            Err(error) => {
                eprintln!("eukhe-daemon worker: goal updates unavailable: {error}");
                return;
            }
        };
    while let Some(goal) = updates.next().await {
        let goal = json!(goal);
        let mut core = lock(&sink.core);
        let Some(view) = core.view.as_mut().filter(|view| view.epoch == epoch) else {
            return;
        };
        if view.goal == goal {
            continue;
        }
        view.goal = goal.clone();
        crate::worker::emit_event_locked(
            &mut core,
            &sink.events,
            json!({ "type": "goal_update", "goal": goal }),
        );
    }
}

/// The queued inputs of `conversation_id` with their preview texts, in
/// inbox order (writes excluded).
///
/// # Errors
///
/// The `pi.inbox` document cannot be read or decoded.
pub async fn inbox_previews(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Vec<QueuedInput>> {
    let Some(value) = harness.snapshot(&INBOX_DOC, conversation_id, cx).await? else {
        return Ok(Vec::new());
    };
    let state: InboxState = from_json(&JsonValue::Object(value)).map_err(SessionError::other)?;
    Ok(state
        .items
        .into_iter()
        .filter_map(|item| match item {
            InboxItem::Steer { id, content } => Some(QueuedInput {
                id,
                mode: QueuedMode::Steer,
                text: content_preview(&content),
                content,
            }),
            InboxItem::FollowUp { id, content } => Some(QueuedInput {
                id,
                mode: QueuedMode::FollowUp,
                text: content_preview(&content),
                content,
            }),
            InboxItem::Write { .. } => None,
        })
        .collect())
}

/// The queue-strip text of one input: its text blocks joined; an
/// image-only input previews as `[image]`.
pub(crate) fn content_preview(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => {
            let texts: Vec<&str> = blocks
                .iter()
                .filter_map(|block| match block {
                    UserContentBlock::Text(text) => Some(text.text.as_str()),
                    UserContentBlock::Image(_) => None,
                })
                .collect();
            if texts.is_empty() && !blocks.is_empty() {
                "[image]".to_owned()
            } else {
                texts.join("\n")
            }
        }
    }
}
