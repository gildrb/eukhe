//! Durable agent events -> the typed [`SessionEvent`]s every view folds.
//!
//! The Harness publishes one batch of [`AgentEvent`]s per commit for the
//! shown conversation. [`EventTranslator`] keeps a [`ConversationMirror`] of
//! that conversation (seeded by the stream's snapshot) and turns each event
//! into session events: `agent_start`, `message_*`, `tool_execution_*`,
//! `auto_retry_*`, `compaction_*`, and so on. Envelope and sequence stamping
//! stay with the caller.
//!
//! In [`CoalesceMode::Coalesced`] the streamed `message_update` frames park in
//! one slot instead of going out per change: same-kind updates merge their
//! delta text, a kind switch replaces the parked update, and block ends
//! (`text_end`, ...) and every other frame flush it first, so wire order
//! matches uncoalesced streaming. The parked frame is built from the current
//! partial when it flushes ([`EventTranslator::flush`], the worker's 50 ms
//! timer).

use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use eukhe_chord::json::JsonValue;
use eukhe_core::durable::messages::REFINEMENT_AUDIT_CUSTOM_TYPE;
use eukhe_core::durable::{
    CustomEntryData, CustomStateData, ProviderWireEvent, BASH_ENTRY, BRANCH_SUMMARY_ENTRY,
    CUSTOM_ENTRY, CUSTOM_STATE_ENTRY,
};
use eukhe_durable::entries::{ASSISTANT_ENTRY, COMPACTION_ENTRY, USER_ENTRY};
use eukhe_durable::harness::types::{AgentState, CompactionReason, ConversationRetryPolicy};
use eukhe_durable::harness::usage::UsageState;
use eukhe_durable::harness::{
    summary_task_id, AgentEvent, MessageChange, PathSegment, QueuedItem, SnapshotEvent,
    ToolEventCall, ToolOutputUpdate, ToolSlotStatus, COMPACTION_TASK, GENERATION_TASK, TOOL_TASK,
};
use eukhe_durable::types::{
    EntryId, EntryRecord, SubmissionId, SubmissionRecord, SubmissionState, TaskId, WriteSubmission,
};
use eukhe_types::ai::{TextContent, UserContent, UserContentBlock};
use eukhe_types::daemon::{
    CompactionReason as WireCompactionReason, CompactionResult, ErrorSeverity, Failover,
    FailoverReason, SessionEvent, StreamUpdate, ToolOutput, TurnAnswer,
};
use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, Message, StopReason, Usage};
use eukhe_types::session::{AgentMessage, CustomMessage};
use serde_json::{Map, Value};

use super::wire_messages::{
    assistant_context_tokens, assistant_wire_message, entry_data, entry_wire_message, to_wire,
};

/// Result text of a tool that ended without a result entry or a known failure.
const NO_RESULT_TEXT: &str = "Tool execution ended without a result";

/// How streamed `message_update` frames go out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CoalesceMode {
    /// Park updates in one slot; the caller flushes them on a timer.
    Coalesced,
    /// One frame per message change.
    Immediate,
}

/// One running tool as the events describe it.
#[derive(Debug, Clone, PartialEq)]
pub struct RunningTool {
    pub call_id: String,
    pub name: String,
    pub args: Value,
    pub output: String,
    pub details: Option<Value>,
}

/// The shown conversation's state as its events describe it (initialized
/// from the stream's `SnapshotEvent`, replaced by any later `Snapshot` event).
#[derive(Debug, Clone, PartialEq)]
pub struct ConversationMirror {
    /// Every entry, append order.
    pub entries: Vec<EntryRecord>,
    /// Live run inputs (busy iff Some).
    pub run: Option<Vec<SubmissionId>>,
    /// In-flight assistant message (message changes applied).
    pub partial: Option<AssistantMessage>,
    pub tools: Vec<RunningTool>,
    pub compactions: Vec<(TaskId, CompactionReason)>,
    pub inbox: Vec<QueuedItem>,
    pub agent: AgentState,
    pub usage: UsageState,
    pub retry_attempt: Option<u64>,
}

impl ConversationMirror {
    /// The mirror a snapshot describes. Running tool slots carry no
    /// arguments; they come from the tool call in the partial or the latest
    /// assistant entry that made it (`{}` when neither has it).
    #[must_use]
    pub fn from_snapshot(snapshot: &SnapshotEvent) -> Self {
        let partial = snapshot
            .generation
            .as_ref()
            .and_then(|generation| generation.message.clone());
        let tools = snapshot
            .tools
            .iter()
            .filter(|slot| slot.status == ToolSlotStatus::Running)
            .map(|slot| RunningTool {
                call_id: slot.call_id.clone(),
                name: slot.name.clone(),
                args: tool_call_arguments(&snapshot.entries, partial.as_ref(), &slot.call_id),
                output: slot.output.clone().unwrap_or_default(),
                details: slot.details.as_ref().map(Value::from),
            })
            .collect();
        Self {
            entries: snapshot.entries.clone(),
            run: snapshot.run.as_ref().map(|run| run.inputs.clone()),
            partial,
            tools,
            compactions: snapshot
                .compactions
                .iter()
                .map(|status| (status.task_id, status.reason))
                .collect(),
            inbox: snapshot.inbox.clone(),
            agent: snapshot.agent.clone(),
            usage: snapshot.usage.clone(),
            retry_attempt: snapshot
                .generation
                .as_ref()
                .and_then(|generation| generation.retry.as_ref().map(|_| generation.attempt)),
        }
    }

    /// Whether a run is live.
    #[must_use]
    pub fn is_streaming(&self) -> bool {
        self.run.is_some()
    }

    /// Whether a compaction is live.
    #[must_use]
    pub fn is_compacting(&self) -> bool {
        !self.compactions.is_empty()
    }

    /// The running tool of `call_id`.
    #[must_use]
    pub fn tool(&self, call_id: &str) -> Option<&RunningTool> {
        self.tools.iter().find(|tool| tool.call_id == call_id)
    }
}

/// A placed compaction summary waiting for its `compaction_end`.
#[derive(Debug)]
struct PlacedSummary {
    task_id: Option<TaskId>,
    /// The summary entry.
    entry_id: EntryId,
    summary: String,
    /// Context size the last answer before the summary measured.
    tokens_before: u64,
}

/// A task failure a later frame reports (`tool_execution_end` of a faulted
/// tool, `compaction_end` of a faulted compaction).
#[derive(Debug)]
struct Failure {
    task_id: TaskId,
    kind: String,
    message: String,
}

/// The `compact` command's claim on its manual compaction: the run's
/// `compaction_start` carries the command's instructions, and its
/// `compaction_end` is the command's frame (the `CompactionResult` its
/// response carries, or the abort), emitted by whichever side settles last.
#[derive(Debug, Default)]
struct ManualClaim {
    instructions: Option<String>,
    /// The claimed task, bound at the first manual `compaction_start`.
    task_id: Option<TaskId>,
    /// The claimed task's `compaction_end` arrived before the command's frame.
    ended: bool,
    /// The command's end frame, waiting for the task's `compaction_end`.
    end_frame: Option<SessionEvent>,
}

/// Where [`EventTranslator::settle_manual_compaction`] placed the `compact`
/// command's `compaction_end` frame.
#[derive(Debug, PartialEq)]
pub enum ManualSettle {
    /// The claimed task already ended: the caller emits the frame now.
    Emit(Box<SessionEvent>),
    /// The claimed task's `compaction_end` emits the frame.
    Deferred,
    /// No compaction task started: nothing of the run reached the wire.
    NoTask,
}

/// A background compaction whose `compaction_end` waits for the write
/// that places its summary.
#[derive(Debug)]
struct PlacingEnd {
    task_id: TaskId,
    reason: CompactionReason,
    /// The summary's write submission, queued in the inbox.
    write: SubmissionId,
}

/// Translates one conversation's agent events into wire session events.
#[derive(Debug)]
pub struct EventTranslator {
    mirror: ConversationMirror,
    mode: CoalesceMode,
    /// The parked `message_update` change, its deltas merged.
    parked: Option<StreamUpdate>,
    /// A generation failure since the last turn boundary.
    turn_error: Option<String>,
    /// Where the current turn's messages start in `run_messages`.
    turn_from: usize,
    summaries: Vec<PlacedSummary>,
    /// Tool and compaction failures not reported yet.
    failures: Vec<Failure>,
    /// A batch's failures were collected ahead ([`Self::translate_batch`]).
    failures_prescanned: bool,
    /// The running run's messages, carried by its `agent_end`.
    run_messages: Vec<AgentMessage>,
    /// The `compact` command's manual run ([`Self::claim_manual_compaction`]).
    manual_claim: Option<ManualClaim>,
    /// Threshold/overflow compactions that ended without a summary, oldest
    /// first: their `compaction_end` waits for the `compaction_outcome`
    /// row the eukhe compaction observer appends once the task settled (TS
    /// `_endCompactionUnsuccessfully` broadcasts the disclosure row first,
    /// then the end event shaped by its outcome), unless the summary's
    /// write submission queued in the same commit (then it moves to
    /// `placing`). A snapshot ends them all: the outcome row may have gone
    /// by in the events the snapshot replaces.
    held_ends: Vec<(TaskId, CompactionReason)>,
    /// Background compactions that ended while a run was live: their
    /// summary waits in the inbox for the run's next boundary, and their
    /// `compaction_end` for that write's settlement. Writes outlive runs
    /// (an aborted run leaves them queued), so a run end keeps them; a
    /// write that leaves the inbox with no settlement ends its compaction
    /// as unsuccessful.
    placing: Vec<PlacingEnd>,
    /// The open retry episode (TS `auto_retry_start` ... `auto_retry_end`).
    retry_episode: Option<RetryEpisode>,
    /// The session's retry policy: the wire's `maxAttempts`.
    retry_policy: Option<RetryPolicySource>,
}

/// One retry episode: pi-durable pairs every retry wait with its own
/// `AutoRetryEnd` when the next attempt starts, while the wire (TS) closes
/// the whole episode once — recovered on the next settled answer, failed at
/// the turn's end.
#[derive(Debug, Default)]
struct RetryEpisode {
    /// Retry starts so far (the durable retries plus provider switches).
    retries: u64,
    /// The newest failed attempt's error.
    final_error: Option<String>,
}

/// The session's resolved retry policy (settings `retry`), read when a
/// retry starts.
#[derive(Clone)]
pub struct RetryPolicySource(Arc<dyn Fn() -> ConversationRetryPolicy + Send + Sync>);

impl RetryPolicySource {
    #[must_use]
    pub fn new(read: impl Fn() -> ConversationRetryPolicy + Send + Sync + 'static) -> Self {
        Self(Arc::new(read))
    }
}

impl std::fmt::Debug for RetryPolicySource {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("RetryPolicySource")
    }
}

/// A batch's events in emit order: a run start (with its own `TurnStart`)
/// moves ahead of the inputs placed in the same commit, so `agent_start` /
/// `turn_start` precede the user message frames (TS order). The placed
/// inputs are the block right before the run start (a start on an idle
/// conversation) and every entry a submission of the batch points at: a
/// run's end places the next run's inputs in its own commit, where the
/// durable events list them ahead of the ending run's `TurnEnd` /
/// `RunEnd` — on the wire they open the next run.
fn run_start_first(events: &[AgentEvent]) -> Vec<&AgentEvent> {
    let Some(start) = events
        .iter()
        .position(|event| matches!(event, AgentEvent::RunStart { .. }))
    else {
        return events.iter().collect();
    };
    let mut to = start;
    while to > 0
        && matches!(
            events[to - 1],
            AgentEvent::MessageStart { .. }
                | AgentEvent::MessageEnd { .. }
                | AgentEvent::EntryAppended { .. }
                | AgentEvent::Submission { .. }
                | AgentEvent::InboxUpdate { .. }
        )
    {
        to -= 1;
    }
    let end = if matches!(events.get(start + 1), Some(AgentEvent::TurnStart)) {
        start + 2
    } else {
        start + 1
    };
    let placed: Vec<EntryId> = events
        .iter()
        .filter_map(|event| match event {
            AgentEvent::Submission { record } => record.state.entry(),
            _ => None,
        })
        .collect();
    let placed_entry = |event: Option<&AgentEvent>| match event {
        Some(AgentEvent::MessageEnd { entry } | AgentEvent::EntryAppended { entry }) => {
            placed.contains(&entry.id)
        }
        _ => false,
    };
    // A message's start goes with its end.
    let moves = |index: usize| {
        index >= to
            || placed_entry(events.get(index))
            || (matches!(events[index], AgentEvent::MessageStart { .. })
                && placed_entry(events.get(index + 1)))
    };
    let mut ordered = Vec::with_capacity(events.len());
    ordered.extend(
        (0..start)
            .filter(|&index| !moves(index))
            .map(|index| &events[index]),
    );
    ordered.extend(&events[start..end]);
    ordered.extend(
        (0..start)
            .filter(|&index| moves(index))
            .map(|index| &events[index]),
    );
    ordered.extend(&events[end..]);
    ordered
}

impl EventTranslator {
    #[must_use]
    pub fn new(snapshot: &SnapshotEvent, mode: CoalesceMode) -> Self {
        Self {
            mirror: ConversationMirror::from_snapshot(snapshot),
            mode,
            parked: None,
            turn_error: None,
            turn_from: 0,
            summaries: Vec::new(),
            failures: Vec::new(),
            failures_prescanned: false,
            run_messages: Vec::new(),
            manual_claim: None,
            held_ends: Vec::new(),
            placing: Vec::new(),
            retry_episode: None,
            retry_policy: None,
        }
    }

    /// Report every retry start's `maxAttempts` from `policy`.
    #[must_use]
    pub fn with_retry_policy(mut self, policy: RetryPolicySource) -> Self {
        self.retry_policy = Some(policy);
        self
    }

    #[must_use]
    pub fn mirror(&self) -> &ConversationMirror {
        &self.mirror
    }

    /// Claim the next manual compaction for the `compact` command: its
    /// `compaction_start` carries `instructions`, and its `compaction_end`
    /// is the frame [`Self::settle_manual_compaction`] provides.
    pub fn claim_manual_compaction(&mut self, instructions: Option<String>) {
        self.manual_claim = Some(ManualClaim {
            instructions,
            ..ManualClaim::default()
        });
    }

    /// Settle the claim with the command's `compaction_end` frame.
    /// `task_started` says the run certainly started a task (it completed
    /// or was aborted); otherwise only a bound claim proves one.
    pub fn settle_manual_compaction(
        &mut self,
        end_frame: SessionEvent,
        task_started: bool,
    ) -> ManualSettle {
        let Some(claim) = self.manual_claim.as_mut() else {
            return ManualSettle::NoTask;
        };
        if claim.ended {
            self.manual_claim = None;
            return ManualSettle::Emit(Box::new(end_frame));
        }
        if claim.task_id.is_some() || task_started {
            claim.end_frame = Some(end_frame);
            return ManualSettle::Deferred;
        }
        self.manual_claim = None;
        ManualSettle::NoTask
    }

    /// Apply one commit's batch in order. Unlike event-by-event
    /// [`Self::translate`], the batch's task failures are known up front, so a
    /// faulted tool's `tool_execution_end` and a faulted compaction's
    /// `compaction_end` carry their failure message although the durable
    /// events list failures after those ends.
    pub fn translate_batch(&mut self, events: &[AgentEvent]) -> Vec<SessionEvent> {
        for event in events {
            if let AgentEvent::TaskFailed {
                task_id,
                kind,
                message,
            } = event
            {
                if kind == TOOL_TASK.definition().name()
                    || kind == COMPACTION_TASK.definition().name()
                {
                    self.failures.push(Failure {
                        task_id: *task_id,
                        kind: kind.clone(),
                        message: message.clone(),
                    });
                }
            }
        }
        self.failures_prescanned = true;
        let mut frames = Vec::new();
        for event in run_start_first(events) {
            frames.extend(self.translate(event));
        }
        // A failure the batch did not report belongs to no later frame.
        self.failures.clear();
        self.failures_prescanned = false;
        frames
    }

    /// Apply one event to the mirror and return the session events in emit
    /// order. Coalesced mode: `message_update` frames park (single slot; the
    /// same stream update kind merges delta text, a kind switch replaces; a
    /// block-end kind flushes instead of superseding); any other emitted
    /// frame is preceded by the flushed parked update in the returned Vec.
    pub fn translate(&mut self, event: &AgentEvent) -> Vec<SessionEvent> {
        let mut out = Vec::new();
        match event {
            AgentEvent::Snapshot(snapshot) => self.reset(snapshot, &mut out),
            AgentEvent::RunStart { .. }
            | AgentEvent::RunEnd { .. }
            | AgentEvent::TurnStart
            | AgentEvent::TurnEnd => self.lifecycle(event, &mut out),
            AgentEvent::MessageStart { message } => self.message_start(message, &mut out),
            AgentEvent::MessageUpdate { usage, changes } => {
                self.message_update(*usage, changes, &mut out);
            }
            AgentEvent::MessageEnd { entry } => self.message_end(entry, &mut out),
            AgentEvent::EntryAppended { entry } => {
                if entry.kind == CUSTOM_ENTRY.kind() {
                    if let Some(message) = entry_wire_message(entry).as_ref().and_then(to_wire) {
                        self.shown_message(&message, &mut out);
                    }
                } else if let Some(frame) = refine_complete_frame(entry) {
                    self.flush_into(&mut out);
                    out.push(frame);
                }
                self.mirror.entries.push(entry.clone());
            }
            // A nested call (a `codemode` script's `read`, ...) is part of the
            // call that made it, which reports it in its own output and
            // result: the wire's tool frames are the model's calls only.
            AgentEvent::ToolExecutionStart { call, .. }
            | AgentEvent::ToolExecutionUpdate { call, .. }
            | AgentEvent::ToolExecutionEnd { call, .. }
                if call.parent_tool_call_id.is_some() => {}
            AgentEvent::ToolExecutionStart { call, args } => {
                self.tool_start(&call.tool_call_id, &call.tool_name, args, &mut out);
            }
            AgentEvent::ToolExecutionUpdate {
                call,
                output,
                details,
                ..
            } => self.tool_update(
                &call.tool_call_id,
                &call.tool_name,
                output.as_ref(),
                details.as_ref(),
                &mut out,
            ),
            AgentEvent::ToolExecutionEnd { call, entry, .. } => {
                self.tool_end(call, entry.as_ref(), &mut out);
            }
            AgentEvent::InboxUpdate { items } => {
                self.mirror.inbox.clone_from(items);
                self.end_lost_placements(&mut out);
            }
            AgentEvent::AutoRetryStart {
                attempt,
                at,
                error_message,
            } => self.retry_start(*attempt, *at, error_message, &mut out),
            AgentEvent::AutoRetryEnd { .. } => {
                // The wait ended and the next attempt starts; the episode
                // stays open until an answer settles or the turn ends.
                self.flush_into(&mut out);
                self.mirror.retry_attempt = None;
            }
            AgentEvent::AgentChanged { agent } => self.mirror.agent = agent.clone(),
            AgentEvent::UsageChanged { usage } => self.mirror.usage = usage.clone(),
            AgentEvent::TaskFailed {
                task_id,
                kind,
                message,
            } => self.task_failed(*task_id, kind, message),
            AgentEvent::CompactionStart {
                task_id, reason, ..
            } => {
                self.flush_into(&mut out);
                if !self.mirror.compactions.iter().any(|(id, _)| id == task_id) {
                    self.mirror.compactions.push((*task_id, *reason));
                }
                let mut custom_instructions = None;
                if let Some(claim) = self.manual_claim.as_mut() {
                    if claim.task_id.is_none() && *reason == CompactionReason::Manual {
                        claim.task_id = Some(*task_id);
                    }
                    if claim.task_id == Some(*task_id) {
                        custom_instructions.clone_from(&claim.instructions);
                    }
                }
                out.push(SessionEvent::CompactionStart {
                    reason: wire_reason(*reason),
                    custom_instructions,
                });
            }
            AgentEvent::CompactionEnd { task_id, reason } => {
                self.compaction_end(*task_id, *reason, &mut out);
            }
            AgentEvent::Submission { record } => self.summary_write(record, &mut out),
            AgentEvent::DeferredPoll { .. } => {}
        }
        self.collect_run_messages(&mut out);
        out
    }

    /// The run's messages ride its `agent_end` (TS `agent_end {messages}`:
    /// the run's new messages, prompt included): every `message_end` from
    /// the `agent_start` on. A `turn_end` carries its turn's terminal
    /// assistant message and the tool results after it (TS `turn_end
    /// {message, toolResults}`); its separate `error` stays only for a turn
    /// that failed without an assistant message to carry the failure.
    fn collect_run_messages(&mut self, out: &mut [SessionEvent]) {
        for frame in out {
            match frame {
                SessionEvent::AgentStart => {
                    self.run_messages.clear();
                    self.turn_from = 0;
                }
                SessionEvent::TurnStart => self.turn_from = self.run_messages.len(),
                SessionEvent::MessageEnd { message } => self.run_messages.push(message.clone()),
                SessionEvent::TurnEnd { answer, error } => {
                    let turn = self.run_messages.get(self.turn_from..).unwrap_or_default();
                    if let Some(at) = turn
                        .iter()
                        .rposition(|message| matches!(message, AgentMessage::Assistant(_)))
                    {
                        *answer = Some(TurnAnswer {
                            message: turn[at].clone(),
                            tool_results: turn[at + 1..]
                                .iter()
                                .filter(|message| matches!(message, AgentMessage::ToolResult(_)))
                                .cloned()
                                .collect(),
                        });
                        *error = None;
                    }
                }
                SessionEvent::AgentEnd { messages } => {
                    *messages = std::mem::take(&mut self.run_messages);
                    self.turn_from = 0;
                }
                SessionEvent::MessageStart { .. }
                | SessionEvent::MessageUpdate { .. }
                | SessionEvent::PromptProgress { .. }
                | SessionEvent::ToolExecutionStart { .. }
                | SessionEvent::ToolExecutionUpdate { .. }
                | SessionEvent::ToolExecutionEnd { .. }
                | SessionEvent::AutoRetryStart { .. }
                | SessionEvent::AutoRetryEnd { .. }
                | SessionEvent::CompactionStart { .. }
                | SessionEvent::CompactionSummaryDelta { .. }
                | SessionEvent::CompactionEnd { .. }
                | SessionEvent::SessionInfoChanged { .. }
                | SessionEvent::ServiceTierChanged { .. }
                | SessionEvent::SessionActionUpdate { .. }
                | SessionEvent::GoalUpdate { .. }
                | SessionEvent::ChatTurnWait { .. }
                | SessionEvent::MemoryUpdate { .. }
                | SessionEvent::AgentRelay(_)
                | SessionEvent::BashStart { .. }
                | SessionEvent::BashOutput { .. }
                | SessionEvent::BashEnd { .. }
                | SessionEvent::RefineComplete { .. }
                | SessionEvent::RefineFailed { .. }
                | SessionEvent::IpythonSentAgentMessage { .. } => {}
            }
        }
    }

    /// Run and turn boundaries. The durable run start is followed by its own
    /// `TurnStart`, so `agent_start` comes alone.
    fn lifecycle(&mut self, event: &AgentEvent, out: &mut Vec<SessionEvent>) {
        self.flush_into(out);
        match event {
            AgentEvent::RunStart { inputs } => {
                self.mirror.run = Some(inputs.clone());
                out.push(SessionEvent::AgentStart);
            }
            AgentEvent::RunEnd { .. } => {
                self.end_failed_episode(out);
                out.push(SessionEvent::AgentEnd {
                    messages: Vec::new(),
                });
                self.mirror.run = None;
                self.mirror.partial = None;
                self.mirror.tools.clear();
                self.mirror.retry_attempt = None;
            }
            AgentEvent::TurnStart => {
                self.turn_error = None;
                out.push(SessionEvent::TurnStart);
            }
            AgentEvent::TurnEnd => {
                self.end_failed_episode(out);
                out.push(SessionEvent::TurnEnd {
                    answer: None,
                    error: self.turn_error.take(),
                });
            }
            _ => {}
        }
    }

    fn tool_start(
        &mut self,
        call_id: &str,
        name: &str,
        args: &JsonValue,
        out: &mut Vec<SessionEvent>,
    ) {
        self.flush_into(out);
        let args = Value::from(args);
        out.push(SessionEvent::ToolExecutionStart {
            tool_call_id: call_id.to_owned(),
            tool_name: name.to_owned(),
            args: args.clone(),
        });
        let tool = RunningTool {
            call_id: call_id.to_owned(),
            name: name.to_owned(),
            args,
            output: String::new(),
            details: None,
        };
        match self.tool_mut(call_id) {
            Some(running) => *running = tool,
            None => self.mirror.tools.push(tool),
        }
    }

    fn retry_start(
        &mut self,
        attempt: u64,
        at: f64,
        error_message: &str,
        out: &mut Vec<SessionEvent>,
    ) {
        self.flush_into(out);
        // The failed attempt's partial is gone; the next attempt starts a
        // new message.
        self.mirror.partial = None;
        self.mirror.retry_attempt = Some(attempt);
        let episode = self.retry_episode.get_or_insert_with(RetryEpisode::default);
        episode.retries += 1;
        episode.final_error = Some(error_message.to_owned());
        // The wait (TS `delayMs`): pi-durable draws it once per retry (full
        // jitter under the policy's ladder step, never shorter than the
        // server's Retry-After) and commits its end as `at`, so the wire
        // carries what is left of it from now.
        out.push(SessionEvent::AutoRetryStart {
            attempt,
            max_attempts: self
                .retry_policy
                .as_ref()
                .map(|source| u64::from((source.0)().max_retries)),
            delay_ms: retry_delay_ms(at, now_ms()),
            error_message: error_message.to_owned(),
            failover: None,
        });
    }

    /// The failed close of an open retry episode at the turn's end (TS
    /// `auto_retry_end {success: false, attempt, finalError}`).
    fn end_failed_episode(&mut self, out: &mut Vec<SessionEvent>) {
        let Some(episode) = self.retry_episode.take() else {
            return;
        };
        out.push(SessionEvent::AutoRetryEnd {
            success: false,
            attempt: episode.retries,
            final_error: Some(
                episode
                    .final_error
                    .unwrap_or_else(|| "Unknown error".to_owned()),
            ),
            restored_model: None,
        });
    }

    /// A provider runtime wire event (the backup-switch `auto_retry_*`
    /// vocabulary and the serving server's prompt progress, neither of which
    /// the durable Harness itself emits): flushed after any parked update,
    /// like the harness's own retry frames. A switch joins the open retry
    /// episode; a successful switch's end closes it.
    pub fn provider_event(&mut self, event: &ProviderWireEvent, out: &mut Vec<SessionEvent>) {
        self.flush_into(out);
        match event {
            ProviderWireEvent::AutoRetryStart { error_message, .. } => {
                let episode = self.retry_episode.get_or_insert_with(RetryEpisode::default);
                episode.retries += 1;
                episode.final_error = Some(error_message.clone());
            }
            ProviderWireEvent::AutoRetryEnd { .. } => self.retry_episode = None,
            ProviderWireEvent::PromptProgress(_) => {}
        }
        out.push(provider_wire_frame(event));
    }

    /// A settled assistant message inside an open retry episode: a failed
    /// attempt records its error (a retry or the turn's end follows), a
    /// settled answer closes the episode recovered, and an abort leaves it
    /// to the turn's end.
    fn settle_retry_episode(&mut self, message: &AssistantMessage, out: &mut Vec<SessionEvent>) {
        match message.stop_reason {
            StopReason::Error => {
                if let Some(episode) = self.retry_episode.as_mut() {
                    episode.final_error = Some(
                        message
                            .error_message
                            .clone()
                            .filter(|error| !error.is_empty())
                            .unwrap_or_else(|| "Unknown error".to_owned()),
                    );
                }
            }
            StopReason::Aborted => {}
            StopReason::Stop
            | StopReason::Length
            | StopReason::ToolUse
            | StopReason::Pending
            | StopReason::Deferred => {
                if let Some(episode) = self.retry_episode.take() {
                    out.push(SessionEvent::AutoRetryEnd {
                        success: true,
                        attempt: episode.retries,
                        final_error: None,
                        restored_model: None,
                    });
                }
            }
        }
    }

    /// The parked `message_update` (built from the CURRENT partial), if any;
    /// called by the worker's 50 ms timer and at stream end.
    pub fn flush(&mut self) -> Option<SessionEvent> {
        let parked = self.parked.take()?;
        let partial = self.mirror.partial.as_ref()?;
        update_frame(partial, parked)
    }

    #[must_use]
    pub fn has_parked(&self) -> bool {
        self.parked.is_some()
    }

    fn flush_into(&mut self, out: &mut Vec<SessionEvent>) {
        if let Some(frame) = self.flush() {
            out.push(frame);
        }
    }

    fn reset(&mut self, snapshot: &SnapshotEvent, out: &mut Vec<SessionEvent>) {
        self.mirror = ConversationMirror::from_snapshot(snapshot);
        self.parked = None;
        self.turn_error = None;
        self.summaries.clear();
        // A snapshot replaces the conversation's state: an episode it
        // interrupted closes with no frame (the snapshot's own retry state
        // stands for it).
        self.retry_episode = None;
        if !self.failures_prescanned {
            self.failures.clear();
        }
        // An end held for an outcome row may never see it (the row may be
        // in the events the snapshot replaces): it ends now, with no row.
        for (_, reason) in std::mem::take(&mut self.held_ends) {
            out.push(crate::compaction::compaction_end_unsuccessful(
                wire_reason(reason),
                false,
                None,
                None,
                None,
            ));
        }
        self.end_lost_placements(out);
    }

    /// End, as unsuccessful, each placing compaction whose summary write
    /// left the inbox with no settlement: no later event settles it.
    fn end_lost_placements(&mut self, out: &mut Vec<SessionEvent>) {
        let inbox = &self.mirror.inbox;
        let (kept, lost): (Vec<PlacingEnd>, Vec<PlacingEnd>) = std::mem::take(&mut self.placing)
            .into_iter()
            .partition(|placing| inbox.iter().any(|item| item.id == placing.write));
        self.placing = kept;
        if !lost.is_empty() {
            self.flush_into(out);
        }
        for placing in lost {
            out.push(crate::compaction::compaction_end_unsuccessful(
                wire_reason(placing.reason),
                false,
                None,
                None,
                None,
            ));
        }
    }

    fn tool_mut(&mut self, call_id: &str) -> Option<&mut RunningTool> {
        self.mirror
            .tools
            .iter_mut()
            .find(|tool| tool.call_id == call_id)
    }

    /// `message_start` + `message_end` of a non-streamed message.
    fn message_pair(&mut self, message: &AgentMessage, out: &mut Vec<SessionEvent>) {
        self.flush_into(out);
        out.push(SessionEvent::MessageStart {
            message: message.clone(),
            assistant_message_event: None,
        });
        out.push(SessionEvent::MessageEnd {
            message: message.clone(),
        });
    }

    fn message_start(&mut self, message: &Message, out: &mut Vec<SessionEvent>) {
        // Other roles go out from their paired `MessageEnd`, which carries the
        // entry and its kind.
        let Message::Assistant(message) = message else {
            return;
        };
        self.flush_into(out);
        out.extend(start_frame(message));
        self.mirror.partial = Some(message.clone());
    }

    fn message_update(
        &mut self,
        usage: Usage,
        changes: &[MessageChange],
        out: &mut Vec<SessionEvent>,
    ) {
        if let Some(partial) = &mut self.mirror.partial {
            partial.usage = usage;
        }
        for change in changes {
            if self.mirror.partial.is_none() && !matches!(change, MessageChange::Message { .. }) {
                continue;
            }
            let update = change_event(change);
            let parks = self.mode == CoalesceMode::Coalesced && is_parkable(&update);
            if !parks {
                self.flush_into(out);
            }
            apply_change(&mut self.mirror.partial, change);
            if let (MessageChange::Message { .. }, Some(partial)) =
                (change, &mut self.mirror.partial)
            {
                partial.usage = usage;
            }
            if parks {
                self.park(update);
            } else if let Some(partial) = &self.mirror.partial {
                out.extend(update_frame(partial, update));
            }
        }
    }

    /// Park `update`: a delta of the parked kind merges into it, any other
    /// update replaces it.
    fn park(&mut self, update: StreamUpdate) {
        match (&mut self.parked, update) {
            (
                Some(StreamUpdate::TextDelta { delta: parked }),
                StreamUpdate::TextDelta { delta },
            )
            | (
                Some(StreamUpdate::ThinkingDelta { delta: parked }),
                StreamUpdate::ThinkingDelta { delta },
            )
            | (
                Some(StreamUpdate::ToolcallDelta { delta: parked }),
                StreamUpdate::ToolcallDelta { delta },
            ) => parked.push_str(&delta),
            (parked, update) => *parked = Some(update),
        }
    }

    fn message_end(&mut self, entry: &EntryRecord, out: &mut Vec<SessionEvent>) {
        let kind = entry.kind.as_str();
        if kind == ASSISTANT_ENTRY.kind() {
            let message = entry
                .model
                .as_deref()
                .and_then(<[Message]>::first)
                .and_then(Message::as_assistant);
            if let Some(message) = message {
                self.flush_into(out);
                if self.mirror.partial.is_none() {
                    out.extend(start_frame(message));
                }
                if let Some(message) = assistant_wire_message(message) {
                    out.push(SessionEvent::MessageEnd { message });
                }
                self.settle_retry_episode(message, out);
            }
            self.mirror.partial = None;
        } else if kind == COMPACTION_ENTRY.kind() {
            // Reported by its `compaction_end`.
            match eukhe_core::durable::compaction::compaction_summary_text(entry) {
                Ok(summary) => self.summaries.push(PlacedSummary {
                    task_id: entry.by_task_id,
                    entry_id: entry.id,
                    summary,
                    tokens_before: self
                        .mirror
                        .entries
                        .iter()
                        .rev()
                        .find_map(assistant_context_tokens)
                        .unwrap_or(0),
                }),
                Err(error) => eprintln!(
                    "eukhe-daemon worker: compaction entry {} has malformed data: {error}",
                    entry.id
                ),
            }
        } else if kind == USER_ENTRY.kind() && self.suppressed_input_row(entry) {
            // The input row entered just before its input: the row already
            // shows the user message (an injected custom turn).
        } else if kind != BASH_ENTRY.kind() && kind != BRANCH_SUMMARY_ENTRY.kind() {
            // Bash runs and branch summaries are shown by their features' own events.
            if let Some(message) = entry_wire_message(entry).as_ref().and_then(to_wire) {
                self.shown_message(&message, out);
            }
        }
        self.mirror.entries.push(entry.clone());
    }

    /// Whether the entry just before `user` in the mirror is the legacy
    /// input row that stands for it (a model-less `eukhe.custom` row with
    /// `input: true`): the user frames are then the row's, already shown.
    fn suppressed_input_row(&self, user: &EntryRecord) -> bool {
        user.kind.as_str() == USER_ENTRY.kind()
            && self.mirror.entries.last().is_some_and(|row| {
                row.kind.as_str() == CUSTOM_ENTRY.kind()
                    && row.model.is_none()
                    && entry_data::<CustomEntryData>(row).is_some_and(|data| data.input)
            })
    }

    fn tool_update(
        &mut self,
        call_id: &str,
        name: &str,
        output: Option<&ToolOutputUpdate>,
        details: Option<&JsonValue>,
        out: &mut Vec<SessionEvent>,
    ) {
        self.flush_into(out);
        if self.tool_mut(call_id).is_none() {
            self.mirror.tools.push(RunningTool {
                call_id: call_id.to_owned(),
                name: name.to_owned(),
                args: Value::Object(Map::new()),
                output: String::new(),
                details: None,
            });
        }
        let Some(tool) = self.tool_mut(call_id) else {
            return;
        };
        if let Some(output) = output {
            apply_output(&mut tool.output, output);
        }
        if let Some(details) = details {
            let details = Value::from(details);
            tool.details = (!details.is_null()).then_some(details);
        }
        let text = starting_note(tool.details.as_ref()).unwrap_or(&tool.output);
        out.push(SessionEvent::ToolExecutionUpdate {
            tool_call_id: tool.call_id.clone(),
            tool_name: tool.name.clone(),
            args: tool.args.clone(),
            partial_result: ToolOutput {
                content: vec![text_block(text)],
                details: tool.details.clone(),
            },
        });
    }

    fn tool_end(
        &mut self,
        call: &ToolEventCall,
        entry: Option<&EntryRecord>,
        out: &mut Vec<SessionEvent>,
    ) {
        self.flush_into(out);
        let call_id = call.tool_call_id.as_str();
        self.mirror.tools.retain(|tool| tool.call_id != call_id);
        let result = entry
            .and_then(|entry| entry.model.as_deref())
            .and_then(<[Message]>::first)
            .and_then(|message| match message {
                Message::ToolResult(result) => Some(result),
                Message::System(_) | Message::User(_) | Message::Assistant(_) => None,
            });
        let (result, is_error) = if let Some(result) = result {
            (
                ToolOutput {
                    // A content block the wire cannot carry is logged; the
                    // end still settles the tool.
                    content: to_wire(&result.content).unwrap_or_default(),
                    details: result.details.clone().filter(|details| !details.is_null()),
                },
                result.is_error,
            )
        } else {
            // A faulted or orphaned tool: its tool task's failure (commit
            // order; a nested call's task failure is never its parent's),
            // else the bare fact.
            let message = self
                .failures
                .iter()
                .position(|failure| {
                    failure.kind == TOOL_TASK.definition().name()
                        && call
                            .task_id
                            .is_none_or(|task_id| task_id == failure.task_id)
                })
                .map_or_else(
                    || NO_RESULT_TEXT.to_owned(),
                    |index| self.failures.remove(index).message,
                );
            (
                ToolOutput {
                    content: vec![text_block(&message)],
                    details: None,
                },
                true,
            )
        };
        out.push(SessionEvent::ToolExecutionEnd {
            tool_call_id: call_id.to_owned(),
            tool_name: call.tool_name.clone(),
            result,
            is_error,
        });
    }

    fn task_failed(&mut self, task_id: TaskId, kind: &str, message: &str) {
        if kind == GENERATION_TASK.definition().name() {
            self.turn_error = Some(message.to_owned());
            return;
        }
        // Outside a batch a failure follows the end it explains, so only one
        // a later frame can still report is kept: a live compaction's or a
        // running tool's.
        let reportable = if kind == TOOL_TASK.definition().name() {
            !self.mirror.tools.is_empty()
        } else if kind == COMPACTION_TASK.definition().name() {
            self.mirror.compactions.iter().any(|(id, _)| *id == task_id)
        } else {
            false
        };
        if reportable && !self.failures_prescanned {
            self.failures.push(Failure {
                task_id,
                kind: kind.to_owned(),
                message: message.to_owned(),
            });
        }
    }

    /// A committed non-assistant message: its pair, then the
    /// `compaction_end` an outcome row stands for (a reported overflow, or
    /// a held automatic end).
    fn shown_message(&mut self, message: &AgentMessage, out: &mut Vec<SessionEvent>) {
        self.message_pair(message, out);
        let AgentMessage::Custom(row) = message else {
            return;
        };
        if let Some(frame) = reported_overflow_end(row).or_else(|| self.settle_held_end(row)) {
            out.push(frame);
        }
    }

    /// The held `compaction_end` an automatic compaction's outcome row
    /// settles (oldest of the row's reason), shaped like TS
    /// `_endCompactionUnsuccessfully`: a skip carries the row text with the
    /// `warning` severity, a failure the row text, a cancel `aborted` alone.
    fn settle_held_end(&mut self, row: &CustomMessage) -> Option<SessionEvent> {
        let details = row.details.as_ref()?;
        if row.custom_type != "compaction_outcome" || details["reported"] == true {
            return None;
        }
        let text = content_text(&row.content);
        let (aborted, error_message, error_severity) = match details["outcome"].as_str()? {
            "skipped" => (false, Some(text), Some(ErrorSeverity::Warning)),
            "failed" => (false, Some(text), None),
            "cancelled" => (true, None, None),
            _ => return None,
        };
        let reason = details["reason"].as_str()?;
        let index = self
            .held_ends
            .iter()
            .position(|(_, held)| wire_reason(*held).as_str() == reason)?;
        let (_, held) = self.held_ends.remove(index);
        Some(crate::compaction::compaction_end_unsuccessful(
            wire_reason(held),
            aborted,
            error_message,
            error_severity,
            None,
        ))
    }

    fn compaction_end(
        &mut self,
        task_id: TaskId,
        reason: CompactionReason,
        out: &mut Vec<SessionEvent>,
    ) {
        self.flush_into(out);
        self.mirror.compactions.retain(|(id, _)| *id != task_id);
        // Its own summary, else the latest one placed (a summary placed
        // through a write submission names another task).
        let summary = self
            .summaries
            .iter()
            .position(|summary| summary.task_id == Some(task_id))
            .or_else(|| self.summaries.len().checked_sub(1))
            .map(|index| self.summaries.remove(index));
        let failure = self
            .failures
            .iter()
            .position(|failure| {
                failure.kind == COMPACTION_TASK.definition().name() && failure.task_id == task_id
            })
            .map(|index| self.failures.remove(index));
        if let Some(claim) = self
            .manual_claim
            .as_mut()
            .filter(|claim| claim.task_id == Some(task_id))
        {
            // The `compact` command reports its own run's end (the result
            // its response carries, or the abort).
            match claim.end_frame.take() {
                Some(frame) => {
                    out.push(frame);
                    self.manual_claim = None;
                }
                None => claim.ended = true,
            }
            return;
        }
        if summary.is_none() && reason != CompactionReason::Manual {
            // An automatic compaction that skipped, failed, or was aborted:
            // the observer's outcome row reports it (`settle_held_end`),
            // its text the end's error message. One whose summary queued
            // behind a live run ends with that write (`summary_write`).
            self.held_ends.push((task_id, reason));
            return;
        }
        out.push(summary_end(
            reason,
            summary,
            failure.map(|failure| failure.message),
        ));
    }

    /// A compaction summary's write submission ([`summary_task_id`]).
    /// Queued in the commit its compaction ended in, the end waits for
    /// it; the write's settlement then sends that end: with the summary
    /// placed at the boundary, or as a skip when it went stale behind a
    /// later compaction. A summary placed without a waiting end (its end
    /// went out in the same commit, or the `compact` command reports it)
    /// leaves the pending summaries.
    fn summary_write(&mut self, record: &SubmissionRecord, out: &mut Vec<SessionEvent>) {
        let (SubmissionState::Write(write), Some(task_id)) = (
            &record.state,
            record.request_id.as_deref().and_then(summary_task_id),
        ) else {
            return;
        };
        let names = |(id, _): &(TaskId, CompactionReason)| *id == task_id;
        let places = |placing: &PlacingEnd| placing.task_id == task_id;
        match write {
            WriteSubmission::Queued => {
                if let Some(index) = self.held_ends.iter().position(names) {
                    let (task_id, reason) = self.held_ends.remove(index);
                    self.placing.push(PlacingEnd {
                        task_id,
                        reason,
                        write: record.id,
                    });
                }
            }
            WriteSubmission::Done { entry } => {
                let summary = self
                    .summaries
                    .iter()
                    .position(|summary| summary.entry_id == *entry)
                    .map(|index| self.summaries.remove(index));
                if let Some(index) = self.placing.iter().position(places) {
                    let PlacingEnd { reason, .. } = self.placing.remove(index);
                    self.flush_into(out);
                    out.push(summary_end(reason, summary, None));
                }
            }
            WriteSubmission::Unanswered { .. } => {
                if let Some(index) = self.placing.iter().position(places) {
                    let PlacingEnd { reason, .. } = self.placing.remove(index);
                    self.flush_into(out);
                    out.push(crate::compaction::compaction_end_unsuccessful(
                        wire_reason(reason),
                        false,
                        Some(crate::compaction::durable::ALREADY_COMPACTED.to_owned()),
                        Some(ErrorSeverity::Warning),
                        None,
                    ));
                }
            }
        }
    }
}

/// The `compaction_end` of a compaction with its placed `summary`, or of
/// one without a summary: a manual run the `compact` command does not
/// report, with the `error_message` of its failure.
fn summary_end(
    reason: CompactionReason,
    summary: Option<PlacedSummary>,
    error_message: Option<String>,
) -> SessionEvent {
    // pi-durable re-issues the request after a summarized overflow
    // compaction.
    let will_retry = reason == CompactionReason::Overflow && summary.is_some();
    let error_message = error_message.filter(|_| summary.is_none());
    SessionEvent::CompactionEnd {
        reason: wire_reason(reason),
        result: summary.map(|summary| CompactionResult {
            summary: summary.summary,
            first_kept_entry_id: None,
            tokens_before: summary.tokens_before,
        }),
        aborted: false,
        will_retry,
        error_message,
        error_severity: None,
        custom_instructions: None,
    }
}

/// The wire form of a durable compaction reason.
fn wire_reason(reason: CompactionReason) -> WireCompactionReason {
    match reason {
        CompactionReason::Manual => WireCompactionReason::Manual,
        CompactionReason::Threshold => WireCompactionReason::Threshold,
        CompactionReason::Overflow => WireCompactionReason::Overflow,
    }
}

/// The `compaction_end` that reports a run's failed overflow recovery,
/// after its `compaction_outcome` row (TS `_checkCompaction`
/// reported state: no result, no retry, the row's text as the error).
fn reported_overflow_end(row: &CustomMessage) -> Option<SessionEvent> {
    let details = row.details.as_ref()?;
    let reported = row.custom_type == "compaction_outcome"
        && details["reported"] == true
        && details["reason"] == "overflow"
        && details["outcome"] == "failed";
    reported.then(|| SessionEvent::CompactionEnd {
        reason: WireCompactionReason::Overflow,
        result: None,
        aborted: false,
        will_retry: false,
        error_message: Some(content_text(&row.content)),
        error_severity: None,
        custom_instructions: None,
    })
}

/// The text of a custom message's content: the string, or every block's
/// text run together.
fn content_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks.iter().filter_map(UserContentBlock::text).collect(),
    }
}

/// `refine_complete` of a committed refinement audit row: every applied
/// refinement (the `refine` command, `/refine`, a kernel-requested
/// boundary refinement, the compact-trigger auto-refine) commits one
/// `eukhe.refinement` custom-state row carrying the `RefinementResult`.
fn refine_complete_frame(entry: &EntryRecord) -> Option<SessionEvent> {
    if entry.kind != CUSTOM_STATE_ENTRY.kind() {
        return None;
    }
    let data = entry_data::<CustomStateData>(entry)?;
    if data.custom_type != REFINEMENT_AUDIT_CUSTOM_TYPE {
        return None;
    }
    Some(SessionEvent::RefineComplete {
        result: data.data.unwrap_or(Value::Null),
    })
}

/// `message_start` of a streamed assistant message.
fn start_frame(message: &AssistantMessage) -> Option<SessionEvent> {
    Some(SessionEvent::MessageStart {
        message: assistant_wire_message(message)?,
        assistant_message_event: Some(StreamUpdate::Start),
    })
}

/// `message_update` carrying the full partial and its stream update.
fn update_frame(partial: &AssistantMessage, update: StreamUpdate) -> Option<SessionEvent> {
    Some(SessionEvent::MessageUpdate {
        message: assistant_wire_message(partial)?,
        assistant_message_event: update,
    })
}

/// One text content block.
fn text_block(text: &str) -> UserContentBlock {
    UserContentBlock::Text(TextContent {
        text: text.to_owned(),
        text_signature: None,
        cache_breakpoint: None,
        rest: Map::new(),
    })
}

/// Whether `update` parks in coalesced mode (block ends and whole message
/// replacements go out at once).
fn is_parkable(update: &StreamUpdate) -> bool {
    match update {
        StreamUpdate::TextStart
        | StreamUpdate::TextDelta { .. }
        | StreamUpdate::ThinkingStart
        | StreamUpdate::ThinkingDelta { .. }
        | StreamUpdate::ToolcallStart
        | StreamUpdate::ToolcallDelta { .. } => true,
        StreamUpdate::Start
        | StreamUpdate::TextEnd
        | StreamUpdate::ThinkingEnd
        | StreamUpdate::ToolcallEnd
        | StreamUpdate::Message => false,
    }
}

/// The stream update of one change.
fn change_event(change: &MessageChange) -> StreamUpdate {
    match change {
        MessageChange::TextStart { .. } => StreamUpdate::TextStart,
        MessageChange::ThinkingStart { .. } => StreamUpdate::ThinkingStart,
        MessageChange::ToolcallStart { .. } => StreamUpdate::ToolcallStart,
        MessageChange::TextDelta { delta, .. } => StreamUpdate::TextDelta {
            delta: delta.clone(),
        },
        MessageChange::ThinkingDelta { delta, .. } => StreamUpdate::ThinkingDelta {
            delta: delta.clone(),
        },
        MessageChange::ToolcallDelta { delta, .. } => StreamUpdate::ToolcallDelta {
            delta: delta.clone(),
        },
        MessageChange::Block { block, .. } => match block {
            AssistantContentBlock::Text(_) => StreamUpdate::TextEnd,
            AssistantContentBlock::Thinking(_) => StreamUpdate::ThinkingEnd,
            AssistantContentBlock::ToolCall(_) => StreamUpdate::ToolcallEnd,
        },
        MessageChange::Message { .. } => StreamUpdate::Message,
    }
}

/// Apply one change to the partial (absent only before a whole-message change).
fn apply_change(partial: &mut Option<AssistantMessage>, change: &MessageChange) {
    if let MessageChange::Message { message } = change {
        *partial = Some(message.clone());
        return;
    }
    let Some(partial) = partial else {
        return;
    };
    let content = &mut partial.content;
    match change {
        MessageChange::TextStart {
            content_index,
            block,
        }
        | MessageChange::ThinkingStart {
            content_index,
            block,
        }
        | MessageChange::ToolcallStart {
            content_index,
            block,
        } => content.insert((*content_index).min(content.len()), block.clone()),
        MessageChange::TextDelta {
            content_index,
            delta,
        } => {
            if let Some(AssistantContentBlock::Text(text)) = content.get_mut(*content_index) {
                text.text.push_str(delta);
            }
        }
        MessageChange::ThinkingDelta {
            content_index,
            delta,
        } => {
            if let Some(AssistantContentBlock::Thinking(thinking)) = content.get_mut(*content_index)
            {
                thinking.thinking.push_str(delta);
            }
        }
        MessageChange::ToolcallDelta {
            content_index,
            path,
            delta,
        } => {
            if let Some(AssistantContentBlock::ToolCall(call)) = content.get_mut(*content_index) {
                append_at(&mut call.arguments, path, delta);
            }
        }
        MessageChange::Block {
            content_index,
            block,
        } => match content.get_mut(*content_index) {
            Some(slot) => *slot = block.clone(),
            None => content.push(block.clone()),
        },
        MessageChange::Message { .. } => {}
    }
}

/// Append `delta` to the string at `path` inside tool-call arguments.
fn append_at(arguments: &mut Map<String, Value>, path: &[PathSegment], delta: &str) {
    let Some((PathSegment::Key(first), rest)) = path.split_first() else {
        return;
    };
    let Some(mut value) = arguments.get_mut(first) else {
        return;
    };
    for segment in rest {
        let next = match (segment, value) {
            (PathSegment::Key(key), Value::Object(object)) => object.get_mut(key),
            (PathSegment::Index(index), Value::Array(items)) => items.get_mut(*index),
            _ => None,
        };
        let Some(next) = next else {
            return;
        };
        value = next;
    }
    if let Value::String(text) = value {
        text.push_str(delta);
    }
}

/// Apply one output change of a running tool.
fn apply_output(output: &mut String, update: &ToolOutputUpdate) {
    match update {
        ToolOutputUpdate::Set { set } => set.clone_into(output),
        ToolOutputUpdate::Window { trim_start, append } => {
            if let Some(units) = trim_start {
                trim_utf16_front(output, *units);
            }
            if let Some(append) = append {
                output.push_str(append);
            }
        }
    }
}

/// Drop `units` UTF-16 code units from the front, never splitting a char (a
/// count ending inside a surrogate pair drops the whole char).
fn trim_utf16_front(text: &mut String, units: usize) {
    let mut dropped = 0;
    let mut cut = text.len();
    for (index, ch) in text.char_indices() {
        if dropped >= units {
            cut = index;
            break;
        }
        dropped += ch.len_utf16();
    }
    text.drain(..cut);
}

/// The kernel-start loader note: `details.message` of a `starting` status.
fn starting_note(details: Option<&Value>) -> Option<&str> {
    let details = details?;
    if details.get("status").and_then(Value::as_str) != Some("starting") {
        return None;
    }
    details.get("message").and_then(Value::as_str)
}

/// The arguments of tool call `call_id` in the partial or the latest
/// assistant entry that made it, else `{}`.
fn tool_call_arguments(
    entries: &[EntryRecord],
    partial: Option<&AssistantMessage>,
    call_id: &str,
) -> Value {
    let find = |message: &AssistantMessage| {
        message.content.iter().find_map(|block| match block {
            AssistantContentBlock::ToolCall(call) if call.id == call_id => {
                Some(Value::Object(call.arguments.clone()))
            }
            AssistantContentBlock::ToolCall(_)
            | AssistantContentBlock::Text(_)
            | AssistantContentBlock::Thinking(_) => None,
        })
    };
    partial
        .and_then(find)
        .or_else(|| {
            entries.iter().rev().find_map(|entry| {
                entry
                    .model
                    .as_deref()
                    .and_then(<[Message]>::first)
                    .and_then(Message::as_assistant)
                    .and_then(find)
            })
        })
        .unwrap_or_else(|| Value::Object(Map::new()))
}

/// Milliseconds from `from` until `at` (Unix ms), never negative.
fn retry_delay_ms(at: f64, from: f64) -> u64 {
    Duration::try_from_secs_f64((at - from).max(0.0) / 1000.0).map_or(0, |delay| {
        u64::try_from(delay.as_millis()).unwrap_or(u64::MAX)
    })
}

/// The session event of one provider runtime wire event.
fn provider_wire_frame(event: &ProviderWireEvent) -> SessionEvent {
    match event {
        ProviderWireEvent::AutoRetryStart {
            attempt,
            max_attempts,
            delay_ms,
            error_message,
            backup_model,
        } => SessionEvent::AutoRetryStart {
            attempt: u64::from(*attempt),
            max_attempts: Some(u64::from(*max_attempts)),
            delay_ms: *delay_ms,
            error_message: error_message.clone(),
            failover: Some(Failover {
                reason: FailoverReason::Backup,
                backup_model: backup_model.clone(),
            }),
        },
        ProviderWireEvent::AutoRetryEnd {
            success,
            attempt,
            final_error,
            restored_model,
        } => SessionEvent::AutoRetryEnd {
            success: *success,
            attempt: u64::from(*attempt),
            final_error: final_error.clone(),
            restored_model: restored_model.clone(),
        },
        ProviderWireEvent::PromptProgress(progress) => SessionEvent::PromptProgress {
            progress: *progress,
        },
    }
}

/// Now, in Unix milliseconds.
fn now_ms() -> f64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0.0, |elapsed| elapsed.as_secs_f64() * 1000.0)
}

#[cfg(test)]
#[path = "translator/tests.rs"]
mod tests;
