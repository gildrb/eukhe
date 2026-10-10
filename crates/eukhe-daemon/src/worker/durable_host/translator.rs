//! Durable agent events -> the wire session events the TUI reads.
//!
//! The Harness publishes one batch of [`AgentEvent`]s per commit for the
//! shown conversation. [`EventTranslator`] keeps a [`ConversationMirror`] of
//! that conversation (seeded by the stream's snapshot) and turns each event
//! into the `{"type": ...}` objects the old worker broadcast: `agent_start`,
//! `message_*`, `tool_execution_*`, `auto_retry_*`, `compaction_*`, and so
//! on. Envelope and sequence stamping stay with the caller.
//!
//! In [`CoalesceMode::Coalesced`] the streamed `message_update` frames park in
//! one slot instead of going out per change: same-kind updates merge their
//! delta text, a kind switch replaces the parked update, and block ends
//! (`text_end`, ...) and every other frame flush it first, so wire order
//! matches uncoalesced streaming. The parked frame is built from the current
//! partial when it flushes ([`EventTranslator::flush`], the worker's 50 ms
//! timer).

use std::time::{Duration, SystemTime, UNIX_EPOCH};

use eukhe_chord::json::JsonValue;
use eukhe_core::durable::{
    CustomEntryData, CustomStateData, ProviderWireEvent, BASH_ENTRY, BRANCH_SUMMARY_ENTRY,
    CUSTOM_ENTRY, CUSTOM_STATE_ENTRY,
};
use eukhe_core::session_engine::refine::REFINEMENT_AUDIT_CUSTOM_TYPE;
use eukhe_durable::entries::{ASSISTANT_ENTRY, COMPACTION_ENTRY, USER_ENTRY};
use eukhe_durable::harness::types::{AgentState, CompactionReason};
use eukhe_durable::harness::usage::UsageState;
use eukhe_durable::harness::{
    AgentEvent, MessageChange, PathSegment, QueuedItem, SnapshotEvent, ToolOutputUpdate,
    ToolSlotStatus,
};
use eukhe_durable::types::{EntryRecord, SubmissionId, TaskId};
use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, Message, Usage};
use serde_json::{json, Map, Value};

use super::wire_messages::{
    assistant_context_tokens, assistant_wire_message, compaction_summary_text, entry_data,
    entry_wire_message,
};

/// Task kind of a generation (its failures fail the turn).
const GENERATION_TASK: &str = "pi.generation";
/// Task kind of a tool call.
const TOOL_TASK: &str = "pi.tool";
/// Task kind of a compaction.
const COMPACTION_TASK: &str = "pi.compaction";
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

/// The parked `message_update`: its stream event kind and merged delta run.
#[derive(Debug)]
struct Parked {
    kind: &'static str,
    delta: String,
}

/// A placed compaction summary waiting for its `compaction_end`.
#[derive(Debug)]
struct PlacedSummary {
    task_id: Option<TaskId>,
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

/// Translates one conversation's agent events into wire session events.
#[derive(Debug)]
pub struct EventTranslator {
    mirror: ConversationMirror,
    mode: CoalesceMode,
    parked: Option<Parked>,
    /// A generation failure since the last turn boundary.
    turn_error: Option<String>,
    summaries: Vec<PlacedSummary>,
    /// Tool and compaction failures not reported yet.
    failures: Vec<Failure>,
    /// A batch's failures were collected ahead ([`Self::translate_batch`]).
    failures_prescanned: bool,
    /// The running run's messages, carried by its `agent_end`.
    run_messages: Vec<Value>,
}

/// A batch's events in emit order: a run start (with its own `TurnStart`)
/// moves ahead of the inputs placed in the same commit, so `agent_start` /
/// `turn_start` precede the user message frames (TS order).
fn run_start_first(events: &[AgentEvent]) -> Vec<&AgentEvent> {
    let mut ordered: Vec<&AgentEvent> = events.iter().collect();
    let Some(start) = events
        .iter()
        .position(|event| matches!(event, AgentEvent::RunStart { .. }))
    else {
        return ordered;
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
    ordered[to..end].rotate_right(end - start);
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
            summaries: Vec::new(),
            failures: Vec::new(),
            failures_prescanned: false,
            run_messages: Vec::new(),
        }
    }

    #[must_use]
    pub fn mirror(&self) -> &ConversationMirror {
        &self.mirror
    }

    /// Apply one commit's batch in order. Unlike event-by-event
    /// [`Self::translate`], the batch's task failures are known up front, so a
    /// faulted tool's `tool_execution_end` and a faulted compaction's
    /// `compaction_end` carry their failure message although the durable
    /// events list failures after those ends.
    pub fn translate_batch(&mut self, events: &[AgentEvent]) -> Vec<Value> {
        for event in events {
            if let AgentEvent::TaskFailed {
                task_id,
                kind,
                message,
            } = event
            {
                if kind == TOOL_TASK || kind == COMPACTION_TASK {
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

    /// Apply one event to the mirror and return the wire event objects
    /// (`{"type": ...}`, no envelope/meta) in emit order. Coalesced mode:
    /// `message_update` frames park (single slot; same
    /// `assistantMessageEvent` kind merges delta text, kind switch replaces;
    /// a block-end kind flushes instead of superseding); any other emitted
    /// frame is preceded by the flushed parked update in the returned Vec.
    pub fn translate(&mut self, event: &AgentEvent) -> Vec<Value> {
        let mut out = Vec::new();
        match event {
            AgentEvent::Snapshot(snapshot) => self.reset(snapshot),
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
                    if let Some(message) = entry_wire_message(entry) {
                        self.shown_message(&message, &mut out);
                    }
                } else if let Some(frame) = refine_complete_frame(entry) {
                    self.flush_into(&mut out);
                    out.push(frame);
                }
                self.mirror.entries.push(entry.clone());
            }
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
                self.tool_end(
                    &call.tool_call_id,
                    &call.tool_name,
                    entry.as_ref(),
                    &mut out,
                );
            }
            AgentEvent::InboxUpdate { items } => self.mirror.inbox.clone_from(items),
            AgentEvent::AutoRetryStart {
                attempt,
                at,
                error_message,
            } => self.retry_start(*attempt, *at, error_message, &mut out),
            AgentEvent::AutoRetryEnd { attempt } => {
                self.flush_into(&mut out);
                self.mirror.retry_attempt = None;
                out.push(json!({ "type": "auto_retry_end", "success": true, "attempt": attempt }));
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
                out.push(json!({ "type": "compaction_start", "reason": reason }));
            }
            AgentEvent::CompactionEnd { task_id, reason } => {
                self.compaction_end(*task_id, *reason, &mut out);
            }
            AgentEvent::Submission { .. } | AgentEvent::DeferredPoll { .. } => {}
        }
        self.collect_run_messages(&mut out);
        out
    }

    /// The run's messages ride its `agent_end` (TS `agent_end {messages}`:
    /// the run's new messages, prompt included): every `message_end` from
    /// the `agent_start` on.
    fn collect_run_messages(&mut self, out: &mut [Value]) {
        for frame in out {
            match frame.get("type").and_then(Value::as_str) {
                Some("agent_start") => self.run_messages.clear(),
                Some("message_end") => {
                    if let Some(message) = frame.get("message") {
                        self.run_messages.push(message.clone());
                    }
                }
                Some("agent_end") => {
                    frame["messages"] = Value::Array(std::mem::take(&mut self.run_messages));
                }
                _ => {}
            }
        }
    }

    /// Run and turn boundaries. The durable run start is followed by its own
    /// `TurnStart`, so `agent_start` comes alone.
    fn lifecycle(&mut self, event: &AgentEvent, out: &mut Vec<Value>) {
        self.flush_into(out);
        match event {
            AgentEvent::RunStart { inputs } => {
                self.mirror.run = Some(inputs.clone());
                out.push(json!({ "type": "agent_start" }));
            }
            AgentEvent::RunEnd { .. } => {
                out.push(json!({ "type": "agent_end", "messages": [] }));
                self.mirror.run = None;
                self.mirror.partial = None;
                self.mirror.tools.clear();
                self.mirror.retry_attempt = None;
            }
            AgentEvent::TurnStart => {
                self.turn_error = None;
                out.push(json!({ "type": "turn_start" }));
            }
            AgentEvent::TurnEnd => {
                let mut frame = json!({ "type": "turn_end" });
                if let Some(error) = self.turn_error.take() {
                    frame["error"] = Value::from(error);
                }
                out.push(frame);
            }
            _ => {}
        }
    }

    fn tool_start(&mut self, call_id: &str, name: &str, args: &JsonValue, out: &mut Vec<Value>) {
        self.flush_into(out);
        let args = Value::from(args);
        out.push(json!({
            "type": "tool_execution_start",
            "toolCallId": call_id,
            "toolName": name,
            "args": args,
        }));
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

    fn retry_start(&mut self, attempt: u64, at: f64, error_message: &str, out: &mut Vec<Value>) {
        self.flush_into(out);
        // The failed attempt's partial is gone; the next attempt starts a
        // new message.
        self.mirror.partial = None;
        self.mirror.retry_attempt = Some(attempt);
        out.push(json!({
            "type": "auto_retry_start",
            "attempt": attempt,
            "delayMs": retry_delay_ms(at, now_ms()),
            "errorMessage": error_message,
        }));
    }

    /// A provider failover event of the session's provider runtime (the
    /// old engine's backup-switch `auto_retry_*` vocabulary the durable
    /// Harness itself does not emit): flushed after any parked update,
    /// like the harness's own retry frames.
    pub fn provider_event(&mut self, event: &ProviderWireEvent, out: &mut Vec<Value>) {
        self.flush_into(out);
        out.push(provider_wire_frame(event));
    }

    /// The parked `message_update` (built from the CURRENT partial), if any;
    /// called by the worker's 50 ms timer and at stream end.
    pub fn flush(&mut self) -> Option<Value> {
        let parked = self.parked.take()?;
        let partial = self.mirror.partial.as_ref()?;
        Some(update_frame(partial, parked.kind, &parked.delta))
    }

    #[must_use]
    pub fn has_parked(&self) -> bool {
        self.parked.is_some()
    }

    fn flush_into(&mut self, out: &mut Vec<Value>) {
        if let Some(frame) = self.flush() {
            out.push(frame);
        }
    }

    fn reset(&mut self, snapshot: &SnapshotEvent) {
        self.mirror = ConversationMirror::from_snapshot(snapshot);
        self.parked = None;
        self.turn_error = None;
        self.summaries.clear();
        if !self.failures_prescanned {
            self.failures.clear();
        }
    }

    fn tool_mut(&mut self, call_id: &str) -> Option<&mut RunningTool> {
        self.mirror
            .tools
            .iter_mut()
            .find(|tool| tool.call_id == call_id)
    }

    /// `message_start` + `message_end` of a non-streamed message.
    fn message_pair(&mut self, message: &Value, out: &mut Vec<Value>) {
        self.flush_into(out);
        out.push(json!({ "type": "message_start", "message": message }));
        out.push(json!({ "type": "message_end", "message": message }));
    }

    fn message_start(&mut self, message: &Message, out: &mut Vec<Value>) {
        // Other roles go out from their paired `MessageEnd`, which carries the
        // entry and its kind.
        let Message::Assistant(message) = message else {
            return;
        };
        self.flush_into(out);
        out.push(start_frame(message));
        self.mirror.partial = Some(message.clone());
    }

    fn message_update(&mut self, usage: Usage, changes: &[MessageChange], out: &mut Vec<Value>) {
        if let Some(partial) = &mut self.mirror.partial {
            partial.usage = usage;
        }
        for change in changes {
            if self.mirror.partial.is_none() && !matches!(change, MessageChange::Message { .. }) {
                continue;
            }
            let (kind, delta) = change_event(change);
            let parks = self.mode == CoalesceMode::Coalesced && is_parkable(kind);
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
                self.park(kind, delta);
            } else if let Some(partial) = &self.mirror.partial {
                out.push(update_frame(partial, kind, delta));
            }
        }
    }

    fn park(&mut self, kind: &'static str, delta: &str) {
        match &mut self.parked {
            Some(parked) if parked.kind == kind => parked.delta.push_str(delta),
            parked => {
                *parked = Some(Parked {
                    kind,
                    delta: delta.to_owned(),
                });
            }
        }
    }

    fn message_end(&mut self, entry: &EntryRecord, out: &mut Vec<Value>) {
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
                    out.push(start_frame(message));
                }
                out.push(json!({
                    "type": "message_end",
                    "message": assistant_wire_message(message),
                }));
            }
            self.mirror.partial = None;
        } else if kind == COMPACTION_ENTRY.kind() {
            // Reported by its `compaction_end`.
            self.summaries.push(PlacedSummary {
                task_id: entry.by_task_id,
                summary: compaction_summary_text(entry),
                tokens_before: self
                    .mirror
                    .entries
                    .iter()
                    .rev()
                    .find_map(assistant_context_tokens)
                    .unwrap_or(0),
            });
        } else if kind == USER_ENTRY.kind() && self.suppressed_input_row(entry) {
            // The input row entered just before its input: the row already
            // shows the user message (the old engine's injected custom turn).
        } else if kind != BASH_ENTRY.kind() && kind != BRANCH_SUMMARY_ENTRY.kind() {
            // Bash runs and branch summaries are shown by their features' own events.
            if let Some(message) = entry_wire_message(entry) {
                self.shown_message(&message, out);
            }
        }
        self.mirror.entries.push(entry.clone());
    }

    /// Whether the entry just before `user` in the mirror is the input row
    /// that stands for it (an `eukhe.custom` row with `input: true`): the
    /// user frames are then the row's, already shown.
    fn suppressed_input_row(&self, user: &EntryRecord) -> bool {
        user.kind.as_str() == USER_ENTRY.kind()
            && self.mirror.entries.last().is_some_and(|row| {
                row.kind.as_str() == CUSTOM_ENTRY.kind()
                    && entry_data::<CustomEntryData>(row).is_some_and(|data| data.input)
            })
    }

    fn tool_update(
        &mut self,
        call_id: &str,
        name: &str,
        output: Option<&ToolOutputUpdate>,
        details: Option<&JsonValue>,
        out: &mut Vec<Value>,
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
        let frame = json!({
            "type": "tool_execution_update",
            "toolCallId": tool.call_id,
            "toolName": tool.name,
            "args": tool.args,
            "partialResult": {
                "content": [{ "type": "text", "text": text }],
                "details": tool.details.clone().unwrap_or(Value::Null),
            },
        });
        out.push(frame);
    }

    fn tool_end(
        &mut self,
        call_id: &str,
        name: &str,
        entry: Option<&EntryRecord>,
        out: &mut Vec<Value>,
    ) {
        self.flush_into(out);
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
                json!({
                    "content": result.content,
                    "details": result.details.clone().unwrap_or(Value::Null),
                }),
                result.is_error,
            )
        } else {
            // A faulted or orphaned tool: its failure (commit order), else the
            // bare fact.
            let message = self
                .failures
                .iter()
                .position(|failure| failure.kind == TOOL_TASK)
                .map_or_else(
                    || NO_RESULT_TEXT.to_owned(),
                    |index| self.failures.remove(index).message,
                );
            (
                json!({
                    "content": [{ "type": "text", "text": message }],
                    "details": Value::Null,
                }),
                true,
            )
        };
        out.push(json!({
            "type": "tool_execution_end",
            "toolCallId": call_id,
            "toolName": name,
            "result": result,
            "isError": is_error,
        }));
    }

    fn task_failed(&mut self, task_id: TaskId, kind: &str, message: &str) {
        if kind == GENERATION_TASK {
            self.turn_error = Some(message.to_owned());
            return;
        }
        // Outside a batch a failure follows the end it explains, so only one
        // a later frame can still report is kept: a live compaction's or a
        // running tool's.
        let reportable = match kind {
            TOOL_TASK => !self.mirror.tools.is_empty(),
            COMPACTION_TASK => self.mirror.compactions.iter().any(|(id, _)| *id == task_id),
            _ => false,
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
    /// `compaction_end` a reported overflow outcome row stands for.
    fn shown_message(&mut self, message: &Value, out: &mut Vec<Value>) {
        self.message_pair(message, out);
        if let Some(frame) = reported_overflow_end(message) {
            out.push(frame);
        }
    }

    fn compaction_end(&mut self, task_id: TaskId, reason: CompactionReason, out: &mut Vec<Value>) {
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
            .position(|failure| failure.kind == COMPACTION_TASK && failure.task_id == task_id)
            .map(|index| self.failures.remove(index));
        let mut frame = json!({
            "type": "compaction_end",
            "reason": reason,
            "result": summary.as_ref().map_or(Value::Null, |summary| json!({
                "summary": summary.summary,
                "tokensBefore": summary.tokens_before,
            })),
            "aborted": false,
            // pi-durable re-issues the request after a summarized overflow
            // compaction.
            "willRetry": reason == CompactionReason::Overflow && summary.is_some(),
        });
        if let (None, Some(failure)) = (&summary, failure) {
            frame["errorMessage"] = Value::from(failure.message);
        }
        out.push(frame);
    }
}

/// The `compaction_end` that reports a run's failed overflow recovery,
/// after its `compaction_outcome` row (the old engine's `_checkCompaction`
/// reported state: no result, no retry, the row's text as the error).
fn reported_overflow_end(message: &Value) -> Option<Value> {
    let details = &message["details"];
    let reported = message["customType"] == "compaction_outcome"
        && details["reported"] == true
        && details["reason"] == "overflow"
        && details["outcome"] == "failed";
    if !reported {
        return None;
    }
    let text = match &message["content"] {
        Value::String(text) => text.clone(),
        Value::Array(blocks) => blocks
            .iter()
            .filter_map(|block| block["text"].as_str())
            .collect(),
        _ => return None,
    };
    Some(json!({
        "type": "compaction_end",
        "reason": "overflow",
        "result": Value::Null,
        "aborted": false,
        "willRetry": false,
        "errorMessage": text,
    }))
}

/// `refine_complete` of a committed refinement audit row: every applied
/// refinement (the `refine` command, `/refine`, a kernel-requested
/// boundary refinement, the compact-trigger auto-refine) commits one
/// `eukhe.refinement` custom-state row carrying the `RefinementResult`.
fn refine_complete_frame(entry: &EntryRecord) -> Option<Value> {
    if entry.kind != CUSTOM_STATE_ENTRY.kind() {
        return None;
    }
    let data = entry_data::<CustomStateData>(entry)?;
    if data.custom_type != REFINEMENT_AUDIT_CUSTOM_TYPE {
        return None;
    }
    Some(json!({
        "type": "refine_complete",
        "result": data.data.unwrap_or(Value::Null),
    }))
}

/// `message_start` of a streamed assistant message.
fn start_frame(message: &AssistantMessage) -> Value {
    json!({
        "type": "message_start",
        "message": assistant_wire_message(message),
        "assistantMessageEvent": { "type": "start" },
    })
}

/// `message_update` carrying the full partial and its stream event.
fn update_frame(partial: &AssistantMessage, kind: &str, delta: &str) -> Value {
    let mut event = json!({ "type": kind });
    if !delta.is_empty() {
        event["delta"] = Value::from(delta);
    }
    json!({
        "type": "message_update",
        "message": assistant_wire_message(partial),
        "assistantMessageEvent": event,
    })
}

/// Whether updates of `kind` park in coalesced mode (block ends and whole
/// message replacements go out at once).
fn is_parkable(kind: &str) -> bool {
    matches!(
        kind,
        "text_start"
            | "text_delta"
            | "thinking_start"
            | "thinking_delta"
            | "toolcall_start"
            | "toolcall_delta"
    )
}

/// The stream event kind and delta text of one change.
fn change_event(change: &MessageChange) -> (&'static str, &str) {
    match change {
        MessageChange::TextStart { .. } => ("text_start", ""),
        MessageChange::ThinkingStart { .. } => ("thinking_start", ""),
        MessageChange::ToolcallStart { .. } => ("toolcall_start", ""),
        MessageChange::TextDelta { delta, .. } => ("text_delta", delta),
        MessageChange::ThinkingDelta { delta, .. } => ("thinking_delta", delta),
        MessageChange::ToolcallDelta { delta, .. } => ("toolcall_delta", delta),
        MessageChange::Block { block, .. } => (
            match block {
                AssistantContentBlock::Text(_) => "text_end",
                AssistantContentBlock::Thinking(_) => "thinking_end",
                AssistantContentBlock::ToolCall(_) => "toolcall_end",
            },
            "",
        ),
        MessageChange::Message { .. } => ("message", ""),
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

/// Milliseconds until `at` (Unix ms), never negative.
fn retry_delay_ms(at: f64, now: f64) -> u64 {
    Duration::try_from_secs_f64((at - now).max(0.0) / 1000.0).map_or(0, |delay| {
        u64::try_from(delay.as_millis()).unwrap_or(u64::MAX)
    })
}

/// The wire frame of one provider failover event (the old engine's
/// shapes: `maxAttempts`/`delayMs`/`errorMessage`/`backupModel` on the
/// start, `restoredModel` on the end).
fn provider_wire_frame(event: &ProviderWireEvent) -> Value {
    match event {
        ProviderWireEvent::AutoRetryStart {
            attempt,
            max_attempts,
            delay_ms,
            error_message,
            reason,
            backup_model,
        } => json!({
            "type": "auto_retry_start",
            "attempt": attempt,
            "maxAttempts": max_attempts,
            "delayMs": delay_ms,
            "errorMessage": error_message,
            "reason": reason,
            "backupModel": backup_model,
        }),
        ProviderWireEvent::AutoRetryEnd {
            success,
            attempt,
            final_error,
            restored_model,
        } => {
            let mut frame = json!({
                "type": "auto_retry_end",
                "success": success,
                "attempt": attempt,
            });
            if let Some(error) = final_error {
                frame["finalError"] = Value::from(error.clone());
            }
            if let Some(model) = restored_model {
                frame["restoredModel"] = Value::from(model.clone());
            }
            frame
        }
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
