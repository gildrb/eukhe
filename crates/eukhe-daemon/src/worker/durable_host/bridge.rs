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
use eukhe_core::durable::ProviderWireEvent;
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

use super::translator::{CoalesceMode, EventTranslator, RetryPolicySource};
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
    /// The queue projection's active action (TS `getSessionActionSnapshot`
    /// reads the store's first active action): the labeled row of a
    /// queue-visible delivery the run is working through, at its phase
    /// (`preparing` at pickup, `committing` once the turn's first row
    /// landed, `running` at its first assistant frame), cleared when the
    /// run ends.
    pub(crate) active: Option<crate::types::SessionActionActive>,
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
    Ended {
        error_hold: Option<String>,
    },
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
    /// and start the listener, the flush timer, the goal watch, and the
    /// provider failover relay.
    ///
    /// # Errors
    ///
    /// The event stream or the inbox cannot be read.
    pub(crate) async fn start(
        harness: &Harness,
        conversation_id: ConversationId,
        provider_events: Option<tokio::sync::broadcast::Receiver<ProviderWireEvent>>,
        retry_policy: RetryPolicySource,
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
                translator: EventTranslator::new(stream.snapshot(), CoalesceMode::Coalesced)
                    .with_retry_policy(retry_policy),
                inbox,
                active: None,
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
        let mut tasks = vec![
            tokio::spawn(flush_loop(epoch, sink.clone())),
            tokio::spawn(goal_loop(
                harness.clone(),
                epoch,
                conversation_id,
                sink.clone(),
                cx,
            )),
        ];
        if let Some(events) = provider_events {
            tasks.push(tokio::spawn(provider_loop(epoch, events, sink)));
        }
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

/// Translate one batch into wire events under the core lock. The queue
/// projection rides the frames it describes (TS #2063): a live pickup's
/// projection (its rows gone from the lanes, the action `preparing`) goes
/// out right before the delivered run's first frame, every later phase
/// change right after the frame that moved it, and whatever else changed
/// projects after the batch.
fn apply_batch(
    sink: &BridgeSink,
    epoch: u64,
    batch: &[AgentEvent],
    inbox: Option<Vec<QueuedInput>>,
) {
    let changes = {
        let mut core = lock(&sink.core);
        let (steps, changes) = {
            let Some(view) = core.view.as_mut().filter(|view| view.epoch == epoch) else {
                return;
            };
            let frames = view.translator.translate_batch(batch);
            // An inbox read answers what this batch picked up: the rows
            // that disappeared.
            let armed = inbox
                .as_ref()
                .and_then(|inbox| armed_pickup(&view.inbox, inbox, view.is_busy()));
            let changes = run_changes(&frames);
            (plan_batch(view.active.take(), frames, armed), changes)
        };
        let mut inbox = inbox;
        for step in steps {
            match step {
                Step::Frame(frame) => {
                    crate::worker::emit_event_locked(&mut core, &sink.events, frame);
                }
                Step::Inbox => {
                    if let Some(inbox) = inbox.take() {
                        // The ids no longer queued leave the rider provenance.
                        core.injected
                            .retain(|id, _| inbox.iter().any(|item| item.id == *id));
                        if let Some(view) = core.view.as_mut() {
                            view.inbox = inbox;
                        }
                    }
                }
                Step::Project(active) => {
                    if let Some(view) = core.view.as_mut() {
                        view.active = active;
                    }
                    crate::worker::emit_action_update_locked(&mut core, &sink.events);
                }
            }
        }
        changes
    };
    for change in changes {
        (sink.on_run)(change);
    }
}

/// One step of a batch's emission ([`plan_batch`]).
#[derive(Debug, PartialEq)]
enum Step {
    /// A wire frame.
    Frame(Value),
    /// Apply the batch's inbox read: the lanes lose the picked-up rows.
    Inbox,
    /// Project the queue with this active action.
    Project(Option<crate::types::SessionActionActive>),
}

/// The active action a batch's pickup arms (the strip's Starting row):
/// `preparing`, labeled with the compact text of the first row that left
/// the inbox (`before` -> `after`) while a run is live. Rows that
/// disappear with no run live were withdrawn (an abort), not picked up.
fn armed_pickup(
    before: &[QueuedInput],
    after: &[QueuedInput],
    run_live: bool,
) -> Option<crate::types::SessionActionActive> {
    if !run_live {
        return None;
    }
    let picked = before
        .iter()
        .find(|row| !after.iter().any(|kept| kept.id == row.id))?;
    Some(crate::types::SessionActionActive {
        kind: "turn".to_string(),
        phase: "preparing".to_string(),
        label: Some(super::super::compact_action_label(&picked.text)),
    })
}

/// One batch's emission (TS #2063's projection, the old turn runner's
/// phase ladder): the inbox read applies at the pickup frame
/// ([`pickup_frame`]) when `armed` (a live pickup), else after the frames;
/// the active action is `armed` from the pickup on, moves by every frame
/// ([`step_active`]), and projects at the pickup, after each frame that
/// moved it, and once more at the batch end.
fn plan_batch(
    mut active: Option<crate::types::SessionActionActive>,
    frames: Vec<Value>,
    mut armed: Option<crate::types::SessionActionActive>,
) -> Vec<Step> {
    let count = frames.len();
    let pickup_at = if armed.is_some() {
        pickup_frame(&frames)
    } else {
        count
    };
    let mut steps = Vec::with_capacity(count + 4);
    for (index, frame) in frames.into_iter().enumerate() {
        if index == pickup_at {
            steps.push(Step::Inbox);
            active = armed.take();
            steps.push(Step::Project(active.clone()));
        }
        let moved = step_active(&mut active, &frame);
        steps.push(Step::Frame(frame));
        if moved {
            steps.push(Step::Project(active.clone()));
        }
    }
    if pickup_at == count {
        steps.push(Step::Inbox);
        if armed.is_some() {
            active = armed;
        }
    }
    steps.push(Step::Project(active));
    steps
}

fn frame_type(frame: &Value) -> Option<&str> {
    frame.get("type").and_then(Value::as_str)
}

fn frame_role(frame: &Value) -> Option<&str> {
    frame
        .get("message")
        .and_then(|message| message.get("role"))
        .and_then(Value::as_str)
}

/// Where a live pickup projects: before the delivered run's `agent_start`
/// (a run's end starts the next run on its picked-up inputs in one
/// commit), else, for inputs placed into the running run at a tool
/// boundary, before their first user row.
fn pickup_frame(frames: &[Value]) -> usize {
    frames
        .iter()
        .rposition(|frame| frame_type(frame) == Some("agent_start"))
        .or_else(|| {
            frames
                .iter()
                .position(|frame| frame_role(frame) == Some("user"))
        })
        .unwrap_or(frames.len())
}

/// Move the active action by one wire frame: a run end clears it, the
/// delivered turn's first user row moves it to `committing`, its first
/// assistant frame to `running`; phases only advance. Answers whether it
/// moved.
fn step_active(active: &mut Option<crate::types::SessionActionActive>, frame: &Value) -> bool {
    if frame_type(frame) == Some("agent_end") {
        return active.take().is_some();
    }
    let Some(active) = active.as_mut() else {
        return false;
    };
    let phase_rank = |phase: &str| match phase {
        "running" => 2,
        "committing" => 1,
        _ => 0,
    };
    let phase = match frame_role(frame) {
        Some("user") => "committing",
        Some("assistant") => "running",
        _ => return false,
    };
    if phase_rank(phase) <= phase_rank(&active.phase) {
        return false;
    }
    active.phase = phase.to_string();
    true
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

/// The session's provider failover events onto the wire (the old engine's
/// backup-switch frames): translated under the core lock so the parked
/// update flush keeps stream order; a start also reports the retry to the
/// run hook. A stopped bridge's late events drop on the epoch check.
async fn provider_loop(
    epoch: u64,
    mut events: tokio::sync::broadcast::Receiver<ProviderWireEvent>,
    sink: BridgeSink,
) {
    loop {
        let event = match events.recv().await {
            Ok(event) => event,
            Err(tokio::sync::broadcast::error::RecvError::Lagged(_)) => continue,
            Err(tokio::sync::broadcast::error::RecvError::Closed) => return,
        };
        let changes = {
            let mut core = lock(&sink.core);
            let Some(view) = core.view.as_mut().filter(|view| view.epoch == epoch) else {
                return;
            };
            let mut frames = Vec::new();
            view.translator.provider_event(&event, &mut frames);
            let changes = run_changes(&frames);
            for frame in frames {
                crate::worker::emit_event_locked(&mut core, &sink.events, frame);
            }
            changes
        };
        for change in changes {
            (sink.on_run)(change);
        }
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

/// The queue-strip text of one input: its non-empty text blocks joined; an
/// image-only input (an empty text block, then the images) previews as
/// `[image]`.
pub(crate) fn content_preview(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => {
            let texts: Vec<&str> = blocks
                .iter()
                .filter_map(|block| match block {
                    UserContentBlock::Text(text) => {
                        Some(text.text.as_str()).filter(|text| !text.is_empty())
                    }
                    UserContentBlock::Image(_) => None,
                })
                .collect();
            let has_image = blocks
                .iter()
                .any(|block| matches!(block, UserContentBlock::Image(_)));
            if texts.is_empty() && has_image {
                "[image]".to_owned()
            } else {
                texts.join("\n")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn queued(id: u64, mode: QueuedMode, text: &str) -> QueuedInput {
        QueuedInput {
            id: SubmissionId::from_number(id),
            mode,
            text: text.to_owned(),
            content: UserContent::Text(text.to_owned()),
        }
    }

    fn message_frame(kind: &str, role: &str) -> Value {
        json!({ "type": kind, "message": { "role": role } })
    }

    fn active(phase: &str, label: &str) -> crate::types::SessionActionActive {
        crate::types::SessionActionActive {
            kind: "turn".to_owned(),
            phase: phase.to_owned(),
            label: Some(label.to_owned()),
        }
    }

    /// TS #2063's ladder, projected where a client renders it: a run's end
    /// starts the follow-up's run in one commit, and the pickup projects
    /// `preparing` (lanes already without the row, compact label) right
    /// before the delivered run's `agent_start`, `committing` right after
    /// its user row, `running` right after its first assistant frame, and
    /// the run end clears it. Phases only advance.
    #[test]
    fn the_active_action_walks_the_phase_ladder_at_its_frames() {
        let before = [queued(7, QueuedMode::FollowUp, "please  do the thing")];
        let armed = armed_pickup(&before, &[], true);
        assert_eq!(armed, Some(active("preparing", "please do the thing")));
        let pickup = [
            message_frame("message_end", "assistant"),
            json!({ "type": "turn_end" }),
            json!({ "type": "agent_end" }),
            json!({ "type": "agent_start" }),
            json!({ "type": "turn_start" }),
            message_frame("message_start", "user"),
            message_frame("message_end", "user"),
        ];
        let committing = Some(active("committing", "please do the thing"));
        assert_eq!(
            plan_batch(None, pickup.to_vec(), armed.clone()),
            vec![
                Step::Frame(pickup[0].clone()),
                Step::Frame(pickup[1].clone()),
                Step::Frame(pickup[2].clone()),
                Step::Inbox,
                Step::Project(armed),
                Step::Frame(pickup[3].clone()),
                Step::Frame(pickup[4].clone()),
                Step::Frame(pickup[5].clone()),
                Step::Project(committing.clone()),
                Step::Frame(pickup[6].clone()),
                Step::Project(committing.clone()),
            ]
        );

        // The first assistant frame runs it; a later user row never moves
        // it back.
        let streaming = [
            message_frame("message_start", "assistant"),
            message_frame("message_end", "user"),
        ];
        let running = Some(active("running", "please do the thing"));
        assert_eq!(
            plan_batch(committing, streaming.to_vec(), None),
            vec![
                Step::Frame(streaming[0].clone()),
                Step::Project(running.clone()),
                Step::Frame(streaming[1].clone()),
                Step::Inbox,
                Step::Project(running.clone()),
            ]
        );

        // The run end clears it.
        let end = json!({ "type": "agent_end" });
        assert_eq!(
            plan_batch(running, vec![end.clone()], None),
            vec![
                Step::Frame(end),
                Step::Project(None),
                Step::Inbox,
                Step::Project(None),
            ]
        );
    }

    /// Steers placed into the running run at a tool boundary start no run:
    /// their pickup projects right before their first user row.
    #[test]
    fn a_mid_run_pickup_projects_before_its_first_user_row() {
        let armed = Some(active("preparing", "steer"));
        let frames = [
            json!({ "type": "tool_execution_end" }),
            message_frame("message_end", "toolResult"),
            message_frame("message_start", "user"),
        ];
        let committing = Some(active("committing", "steer"));
        assert_eq!(
            plan_batch(None, frames.to_vec(), armed.clone()),
            vec![
                Step::Frame(frames[0].clone()),
                Step::Frame(frames[1].clone()),
                Step::Inbox,
                Step::Project(armed),
                Step::Frame(frames[2].clone()),
                Step::Project(committing.clone()),
                Step::Project(committing),
            ]
        );
    }

    /// A withdrawal is not a pickup: rows that disappear while no run is
    /// live (an abort withdrew them) never arm the action, and the lanes
    /// update after the batch's frames.
    #[test]
    fn a_withdrawal_without_a_live_run_never_arms() {
        let before = [queued(1, QueuedMode::FollowUp, "x")];
        assert_eq!(armed_pickup(&before, &[], false), None);
        assert_eq!(armed_pickup(&before, &before, true), None);
        let end = json!({ "type": "agent_end" });
        assert_eq!(
            plan_batch(None, vec![end.clone()], None),
            vec![Step::Frame(end), Step::Inbox, Step::Project(None)]
        );
    }

    /// The label caps like TS `compactRlmText(text, 160)`.
    #[test]
    fn the_active_label_caps_at_160_chars() {
        let long = "word ".repeat(60);
        let armed = armed_pickup(&[queued(1, QueuedMode::Steer, &long)], &[], true).expect("armed");
        let label = armed.label.expect("label");
        assert_eq!(label.chars().count(), 160);
        assert!(label.ends_with("..."));
    }

    /// The run boundaries: an automatic retry frame is a `RetryStarted`
    /// (the pane reporter's retry hold clear), beside the run's start and
    /// end.
    #[test]
    fn run_changes_carry_the_retry_boundary() {
        let changes = run_changes(&[
            json!({ "type": "agent_start" }),
            json!({ "type": "auto_retry_start", "attempt": 1 }),
            json!({ "type": "agent_end", "messages": [] }),
        ]);
        assert_eq!(
            changes,
            vec![
                RunChange::Started,
                RunChange::RetryStarted,
                RunChange::Ended { error_hold: None },
            ]
        );
    }
}
