//! The chat memory in a session (`OptChat` spec §6-§9). A root session
//! logs everything it says and does to the endless chat and starts every
//! fresh call from the view; a subagent starts from the view at its spawn
//! and logs nothing. The view rides in front of the call's messages at the
//! LLM boundary (`transform_context`), so it is never persisted, displayed,
//! or compacted away, and it is rendered only after every line of it is a
//! summary.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_agent::abort::AbortSignal;
use eukhe_agent::agent_loop::{
    AfterToolCallFn, BeginNextCallFn, NextCall, ShouldStopBeforeTurnFn, TransformContextFn,
};
use eukhe_agent::types::{
    AfterToolCallResult, AgentEvent, AgentMessage, AssistantContent, CacheBreakpoint, Message,
    StopReason, TextContent, ToolResultContent, UserContent, UserMessage, UserPart,
};

use crate::memory::{cap_text, Kind, Memory, MemoryRole, TurnLease, CAP};
use crate::tools::tool_definition::{ExecuteFn, ToolDefinition, ToolExecutionResult};

/// One session's view of the chat memory.
pub struct ChatMemory {
    memory: Memory,
    role: MemoryRole,
    /// The view of the current call: rendered on the call's first request,
    /// then byte-identical on every later step (the cache prefix).
    view: Mutex<Option<View>>,
    /// Root: the fresh call's own messages, logged only after the view is
    /// rendered (the view covers everything before them).
    deferred: Mutex<Vec<(Kind, String)>>,
    /// Where the current call stands (root only).
    call: Mutex<Call>,
    /// Root: the chat's root-turn lease, held from the call's first request
    /// until its run ends, or while a host holds the turn, until the host's
    /// turn ends (one root turn at a time across every process on the
    /// chat).
    lease: Mutex<Option<TurnLease>>,
    /// Live [`TurnHold`]s: hosts whose turn may re-issue a failed run
    /// (auto-retry, overflow compact-and-retry).
    holds: Mutex<usize>,
    /// Root: told when a fresh call waits for another window's turn, and
    /// when that wait ends (see [`TurnWaitSink`]).
    wait_sink: Mutex<Option<TurnWaitSink>>,
}

/// Where a root call's wait for the chat's turn lease stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnWait {
    /// The lease was not granted at once: another window's turn runs.
    Waiting,
    /// The wait that reported [`TurnWait::Waiting`] ended: the lease was
    /// granted, the wait failed, or it was cancelled.
    Cleared,
}

/// The `chat_turn_wait` session event reporting a status.
impl From<TurnWait> for eukhe_types::daemon::ChatTurnWaitEvent {
    fn from(wait: TurnWait) -> Self {
        Self {
            waiting: match wait {
                TurnWait::Waiting => true,
                TurnWait::Cleared => false,
            },
        }
    }
}

/// The embedding's turn-wait status seam (the daemon's `chat_turn_wait`
/// event, the print mode's stderr line). Called synchronously from the
/// waiting call: `Waiting` once the lease has not been granted within
/// [`WAIT_SHOWN_AFTER`], then exactly one `Cleared` when that wait ends.
/// Implementations must not block.
pub type TurnWaitSink = Arc<dyn Fn(TurnWait) + Send + Sync>;

/// How long a fresh call's lease request may take before the call counts
/// as waiting: a free chat grants within one round trip to its owner, so
/// only a turn queued behind another window's reports a wait.
const WAIT_SHOWN_AFTER: std::time::Duration = std::time::Duration::from_millis(250);

/// A reported wait: [`TurnWait::Cleared`] when it drops, however the wait
/// ends (granted, failed, or its future dropped by an abort).
struct ShownWait {
    sink: TurnWaitSink,
}

impl Drop for ShownWait {
    fn drop(&mut self) {
        (self.sink)(TurnWait::Cleared);
    }
}

/// A host's turn on the chat (see [`ChatMemory::hold_turn`]): while it
/// lives, a run's end keeps the chat's lease, so no other window's turn
/// slips between a failed run and its retry. Dropping it gives the lease
/// back once no call continues.
#[must_use = "the host's turn ends when the hold drops"]
pub struct TurnHold {
    chat: Arc<ChatMemory>,
}

impl Drop for TurnHold {
    fn drop(&mut self) {
        let mut holds = lock(&self.chat.holds);
        *holds -= 1;
        if *holds == 0 && *lock(&self.chat.call) == Call::Ended {
            // Dropping the lease releases it at the owner.
            drop(lock(&self.chat.lease).take());
        }
    }
}

/// The rendered view of one call: its cache-marked pieces.
#[derive(Clone)]
struct View {
    parts: Vec<UserPart>,
    timestamp: i64,
}

/// Where a root session's call stands. A call continues across runs only
/// when its run was cut at a tool boundary to deliver mid-run steering
/// into it; every other end (natural end, abort, error, provider failure,
/// a crash) makes the next admitted message a fresh call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Call {
    /// No call, or the last one ended.
    Ended,
    /// A call runs (its last response asked for tools).
    Running,
    /// The run stopped at a tool boundary to deliver queued steering into
    /// this same call.
    CutForSteering,
}

impl ChatMemory {
    #[must_use]
    pub fn new(memory: Memory, role: MemoryRole) -> Arc<ChatMemory> {
        Arc::new(ChatMemory {
            memory,
            role,
            view: Mutex::new(None),
            deferred: Mutex::new(Vec::new()),
            call: Mutex::new(Call::Ended),
            lease: Mutex::new(None),
            holds: Mutex::new(0),
            wait_sink: Mutex::new(None),
        })
    }

    /// Install the turn-wait status sink ([`TurnWaitSink`]).
    pub fn set_turn_wait_sink(&self, sink: TurnWaitSink) {
        *lock(&self.wait_sink) = Some(sink);
    }

    /// Hold the chat's turn for a host turn that may re-issue a failed run
    /// (the daemon's retry and overflow loop, a print-mode prompt): the
    /// lease the turn's first call takes stays held until the hold drops.
    pub fn hold_turn(self: &Arc<Self>) -> TurnHold {
        *lock(&self.holds) += 1;
        TurnHold {
            chat: Arc::clone(self),
        }
    }

    #[must_use]
    pub fn role(&self) -> MemoryRole {
        self.role
    }

    #[must_use]
    pub fn memory(&self) -> &Memory {
        &self.memory
    }

    /// Whether the next admitted turn of a root session starts a fresh
    /// call: every turn does, except the delivery of mid-run steering into
    /// the call whose run was cut at a tool boundary for it.
    #[must_use]
    pub fn next_turn_is_fresh(&self) -> bool {
        match self.role {
            MemoryRole::Subagent => false,
            MemoryRole::Root => *lock(&self.call) != Call::CutForSteering,
        }
    }

    /// A fresh call begins: its view is rendered on its first request.
    pub fn begin_fresh_call(&self) {
        *lock(&self.view) = None;
        *lock(&self.call) = Call::Running;
    }

    /// The call cut for mid-run steering goes on with it.
    pub fn continue_call(&self) {
        *lock(&self.call) = Call::Running;
    }

    /// The loop's call boundary ([`NextCall`]): after the model's call
    /// ended, a root session's next messages start a fresh call (the lease
    /// goes back to the owner first, so another window's waiting turn runs
    /// in between); a subagent carries its conversation.
    #[must_use]
    pub fn begin_next_call(self: &Arc<Self>) -> BeginNextCallFn {
        let this = Arc::clone(self);
        Arc::new(move || {
            let this = Arc::clone(&this);
            Box::pin(async move {
                match this.role {
                    MemoryRole::Subagent => Ok(NextCall::Carry),
                    MemoryRole::Root => {
                        this.release_lease().await?;
                        this.begin_fresh_call();
                        Ok(NextCall::Fresh)
                    }
                }
            })
        })
    }

    /// Wrap the queued-steering probe that stops a run at a tool boundary:
    /// when it stops a running call, that call is the one the steering
    /// continues.
    #[must_use]
    pub fn steering_probe(
        self: &Arc<Self>,
        probe: ShouldStopBeforeTurnFn,
    ) -> ShouldStopBeforeTurnFn {
        let this = Arc::clone(self);
        Arc::new(move || {
            let stop = probe();
            if stop {
                let mut call = lock(&this.call);
                if *call == Call::Running {
                    *call = Call::CutForSteering;
                }
            }
            stop
        })
    }

    /// The `transform_context` hook: the call's messages behind its view,
    /// the view and the call's leading user texts as ONE user message (§7).
    #[must_use]
    pub fn transform(self: &Arc<Self>) -> TransformContextFn {
        let this = Arc::clone(self);
        Arc::new(move |messages, _signal| {
            let this = Arc::clone(&this);
            // The loop races this future against the turn's abort signal:
            // an aborted wait (for the lease or the view) drops it, and the
            // run's end logs the deferred messages unanswered.
            Box::pin(async move {
                let view = this.call_view().await?;
                Ok(request_messages(view, messages))
            })
        })
    }

    /// The view message for a side question: the current call's view when
    /// a call has rendered one, else a fresh render (after the view
    /// settles; no lease, nothing logged, nothing kept).
    ///
    /// # Errors
    ///
    /// Returns an error when the view cannot settle or render.
    pub async fn view_message(&self) -> anyhow::Result<AgentMessage> {
        let current = lock(&self.view).clone();
        let view = match current {
            Some(view) => view,
            None => render(&self.memory).await?,
        };
        Ok(AgentMessage::Standard(Message::User(UserMessage {
            content: UserContent::Parts(view.parts),
            timestamp: view.timestamp,
        })))
    }

    /// The current call's view. A root call first waits for the chat's
    /// turn lease (a wait behind another window's turn is reported to the
    /// [`TurnWaitSink`]), then for the view to settle, and renders it
    /// BEFORE the call's own messages are logged (§6, §7).
    async fn call_view(&self) -> anyhow::Result<View> {
        if self.role == MemoryRole::Root && lock(&self.lease).is_none() {
            let acquire = self.memory.acquire_turn();
            tokio::pin!(acquire);
            let lease = match tokio::time::timeout(WAIT_SHOWN_AFTER, &mut acquire).await {
                Ok(lease) => lease?,
                Err(_still_waiting) => {
                    let sink = lock(&self.wait_sink).clone();
                    let _shown = sink.map(|sink| {
                        sink(TurnWait::Waiting);
                        ShownWait { sink }
                    });
                    acquire.await?
                }
            };
            *lock(&self.lease) = Some(lease);
        }
        let current = lock(&self.view).clone();
        if let Some(view) = current {
            return Ok(view);
        }
        let view = render(&self.memory).await?;
        if self.role == MemoryRole::Root {
            self.flush_deferred().await?;
        }
        *lock(&self.view) = Some(view.clone());
        Ok(view)
    }

    /// Root: log what the loop just finished, as it happens (§7), and end
    /// the call when its run ends.
    ///
    /// # Errors
    ///
    /// Returns an error when a message cannot be written to the chat: the
    /// memory is the session's history, so a lost line stops the turn.
    pub async fn on_event(&self, event: &AgentEvent, signal: &AbortSignal) -> anyhow::Result<()> {
        if self.role != MemoryRole::Root {
            return Ok(());
        }
        match event {
            AgentEvent::MessageEnd { message } => {
                if let AgentMessage::Standard(Message::Assistant(assistant)) = message {
                    let ended = matches!(
                        assistant.stop_reason,
                        StopReason::Error | StopReason::Aborted
                    ) || !assistant
                        .content
                        .iter()
                        .any(|block| matches!(block, AssistantContent::ToolCall(_)));
                    if ended {
                        *lock(&self.call) = Call::Ended;
                    }
                }
                let entries = log_entries(message);
                if entries.is_empty() {
                    return Ok(());
                }
                if lock(&self.view).is_none() {
                    lock(&self.deferred).extend(entries);
                    return Ok(());
                }
                for (kind, text) in entries {
                    self.memory.append(kind, &text).await?;
                }
                Ok(())
            }
            AgentEvent::AgentEnd { .. } => {
                // A turn stopped before its view rendered (a cancelled
                // wait) leaves its messages in the log, unanswered: now
                // when it holds the chat's turn, else once the turn it
                // waited for has ended, so no other window's turn has them
                // in its middle.
                let flushed = if lock(&self.lease).is_some() {
                    self.flush_deferred().await
                } else {
                    let entries = std::mem::take(&mut *lock(&self.deferred));
                    if !entries.is_empty() {
                        tokio::spawn(log_unanswered(self.memory.clone(), entries));
                    }
                    Ok(())
                };
                // Persist after each turn; the owner reports git failures.
                let persisted = self.memory.persist().await;
                // Every run end but a cut for steering ends the call; the
                // turn goes back unless a host still holds it (a retry may
                // re-issue the run).
                let ends = {
                    let mut call = lock(&self.call);
                    if signal.is_aborted() || *call != Call::CutForSteering {
                        *call = Call::Ended;
                    }
                    *call == Call::Ended
                };
                let released = if ends && *lock(&self.holds) == 0 {
                    self.release_lease().await
                } else {
                    Ok(())
                };
                flushed?;
                persisted?;
                released
            }
            AgentEvent::AgentStart
            | AgentEvent::TurnStart
            | AgentEvent::TurnEnd { .. }
            | AgentEvent::MessageStart { .. }
            | AgentEvent::MessageUpdate { .. }
            | AgentEvent::ToolExecutionStart { .. }
            | AgentEvent::ToolExecutionUpdate { .. }
            | AgentEvent::ToolExecutionEnd { .. } => Ok(()),
        }
    }

    async fn release_lease(&self) -> anyhow::Result<()> {
        let lease = lock(&self.lease).take();
        match lease {
            Some(lease) => lease.release().await,
            None => Ok(()),
        }
    }

    async fn flush_deferred(&self) -> anyhow::Result<()> {
        let entries = std::mem::take(&mut *lock(&self.deferred));
        for (kind, text) in entries {
            self.memory.append(kind, &text).await?;
        }
        Ok(())
    }
}

/// Log the messages of a turn whose wait for the chat's turn was cancelled,
/// as soon as the chat's turn is free, in one turn of their own.
#[tracing::instrument(name = "chat_memory.log_unanswered", skip_all)]
async fn log_unanswered(memory: Memory, entries: Vec<(Kind, String)>) {
    let logged = async {
        let lease = memory.acquire_turn().await?;
        for (kind, text) in entries {
            memory.append(kind, &text).await?;
        }
        memory.persist().await?;
        lease.release().await
    };
    if let Err(error) = logged.await {
        tracing::warn!(
            target: "chat_memory",
            "cannot log the unanswered messages: {error:#}"
        );
    }
}

/// Render the view once every line of it is a summary (§6): its pieces,
/// each but the last cache-marked (§8).
async fn render(memory: &Memory) -> anyhow::Result<View> {
    let rendered = memory.settled_render().await?;
    let pieces = rendered.pieces();
    let marked = pieces.len() - 1;
    let parts = pieces
        .into_iter()
        .enumerate()
        .map(|(at, text)| {
            UserPart::Text(TextContent {
                text,
                text_signature: None,
                cache_breakpoint: (at < marked).then_some(CacheBreakpoint::Ephemeral),
            })
        })
        .collect();
    Ok(View {
        parts,
        timestamp: now_millis(),
    })
}

/// The request of a call (§7, §8): ONE first user message holding the view
/// pieces, then ONE text block with the call's leading user texts (the
/// user's words, reports, nudges) joined by a blank line, their images
/// after it; then any harness state among those leading rows; then the
/// rest of the call.
fn request_messages(view: View, mut messages: Vec<AgentMessage>) -> Vec<AgentMessage> {
    let lead = messages
        .iter()
        .take_while(|message| {
            matches!(
                message,
                AgentMessage::Standard(Message::User(_)) | AgentMessage::Custom(_)
            )
        })
        .count();
    let rest = messages.split_off(lead);
    let (text_rows, state_rows): (Vec<AgentMessage>, Vec<AgentMessage>) =
        messages.into_iter().partition(joins_user_texts);
    let mut parts = view.parts;
    let mut texts: Vec<String> = Vec::new();
    let mut images = Vec::new();
    let mut after: Vec<AgentMessage> = Vec::new();
    for message in super::messages::loop_convert_to_llm(text_rows) {
        let Message::User(user) = message else {
            after.push(AgentMessage::Standard(message));
            continue;
        };
        match user.content {
            UserContent::Text(text) => texts.push(text),
            UserContent::Parts(user_parts) => {
                let mut text = String::new();
                for part in user_parts {
                    match part {
                        UserPart::Text(block) => {
                            if !text.is_empty() {
                                text.push('\n');
                            }
                            text.push_str(&block.text);
                        }
                        UserPart::Image(image) => images.push(UserPart::Image(image)),
                    }
                }
                texts.push(text);
            }
        }
    }
    texts.retain(|text| !text.is_empty());
    if !texts.is_empty() {
        parts.push(UserPart::Text(TextContent {
            text: texts.join("\n\n"),
            text_signature: None,
            cache_breakpoint: None,
        }));
    }
    parts.extend(images);
    let mut out = Vec::with_capacity(1 + after.len() + state_rows.len() + rest.len());
    out.push(AgentMessage::Standard(Message::User(UserMessage {
        content: UserContent::Parts(parts),
        timestamp: view.timestamp,
    })));
    out.extend(after);
    out.extend(state_rows);
    out.extend(rest);
    out
}

/// Cap every tool result at [`CAP`] characters, head and tail kept: results
/// are resent on every later step of the call and land in the permanent log.
#[must_use]
pub fn cap_tool_results() -> AfterToolCallFn {
    Arc::new(|context, _signal| {
        Box::pin(async move {
            let text: String = context
                .result
                .content
                .iter()
                .filter_map(|block| match block {
                    ToolResultContent::Text(text) => Some(text.text.as_str()),
                    ToolResultContent::Image(_) => None,
                })
                .collect::<Vec<_>>()
                .join("\n");
            if text.chars().count() <= CAP {
                return Ok(None);
            }
            let mut content = vec![ToolResultContent::text(cap_text(&text))];
            content.extend(
                context
                    .result
                    .content
                    .into_iter()
                    .filter(|block| matches!(block, ToolResultContent::Image(_))),
            );
            Ok(Some(AfterToolCallResult {
                content: Some(content),
                details: None,
                is_error: None,
                terminate: None,
            }))
        })
    })
}

/// The `zoom` and `date` tools (§7.1) over `memory`.
#[must_use]
pub fn memory_tools(memory: &Memory) -> Vec<ToolDefinition> {
    let zoom_memory = memory.clone();
    let zoom: ExecuteFn = Arc::new(move |_call_id, params, _signal, _on_update| {
        let memory = zoom_memory.clone();
        Box::pin(async move {
            let id = integer_argument(&params, "id")?;
            let count = integer_argument(&params, "n")?;
            Ok(ToolExecutionResult::text(memory.zoom(id, count).await?))
        })
    });
    let date_memory = memory.clone();
    let date: ExecuteFn = Arc::new(move |_call_id, params, _signal, _on_update| {
        let memory = date_memory.clone();
        Box::pin(async move {
            let id = integer_argument(&params, "id")?;
            Ok(ToolExecutionResult::text(memory.date(id).await?))
        })
    });
    vec![
        ToolDefinition {
            name: "zoom".to_string(),
            label: "zoom".to_string(),
            description: crate::memory::ZOOM_TOOL_DESCRIPTION.to_string(),
            prompt_snippet: String::new(),
            parameters: serde_json::json!({
                "type": "object",
                "properties": {
                    "id": { "type": "integer", "minimum": 0 },
                    "n": { "type": "integer", "minimum": 1 }
                },
                "required": ["id", "n"],
                "additionalProperties": false
            }),
            execution_mode: None,
            prepare_arguments: None,
            execute: zoom,
        },
        ToolDefinition {
            name: "date".to_string(),
            label: "date".to_string(),
            description: crate::memory::DATE_TOOL_DESCRIPTION.to_string(),
            prompt_snippet: String::new(),
            parameters: serde_json::json!({
                "type": "object",
                "properties": {
                    "id": { "type": "integer", "minimum": 0 }
                },
                "required": ["id"],
                "additionalProperties": false
            }),
            execution_mode: None,
            prepare_arguments: None,
            execute: date,
        },
    ]
}

fn integer_argument(params: &serde_json::Value, name: &str) -> anyhow::Result<u64> {
    params
        .get(name)
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| anyhow::anyhow!("`{name}` must be a non-negative integer"))
}

/// What one finished loop message adds to the chat log. The user's words,
/// the agent's replies and tool calls, and tool results are logged; reports
/// and background events that reach the model are logged as `user`
/// messages starting with one `[id] ` (§9); harness nudges (autonomous and
/// goal continuations: not the user's words) and harness state the next
/// turn re-derives (kernel notices, bookkeeping rows) are not. Thinking is
/// never logged (§2).
fn log_entries(message: &AgentMessage) -> Vec<(Kind, String)> {
    match message {
        AgentMessage::Standard(Message::User(user)) => {
            let text = user_text(&user.content);
            if text.trim().is_empty() || crate::autonomous::is_autonomous_continuation(&text) {
                Vec::new()
            } else {
                vec![(Kind::User, text)]
            }
        }
        AgentMessage::Standard(Message::Assistant(assistant)) => {
            let mut entries = Vec::new();
            let mut talk = String::new();
            for block in &assistant.content {
                match block {
                    AssistantContent::Text(text) => {
                        if !talk.is_empty() && !text.text.is_empty() {
                            talk.push('\n');
                        }
                        talk.push_str(&text.text);
                    }
                    AssistantContent::ToolCall(call) => {
                        if !talk.trim().is_empty() {
                            entries.push((Kind::Talk, std::mem::take(&mut talk)));
                        }
                        talk.clear();
                        entries.push((Kind::Tool, format!("{} {}", call.name, call.arguments)));
                    }
                    AssistantContent::Thinking(_) => {}
                }
            }
            if !talk.trim().is_empty() {
                entries.push((Kind::Talk, talk));
            }
            entries
        }
        AgentMessage::Standard(Message::ToolResult(result)) => {
            let text = result
                .content
                .iter()
                .map(|block| match block {
                    ToolResultContent::Text(text) => text.text.clone(),
                    ToolResultContent::Image(image) => format!("[image: {}]", image.mime_type),
                })
                .collect::<Vec<_>>()
                .join("\n");
            vec![(Kind::Echo, cap_text(&text))]
        }
        AgentMessage::Custom(custom) => custom_entries(&custom.role, &custom.payload),
    }
}

/// Session-only rows: what reaches the model as a report or a background
/// event is logged; harness nudges and state are not.
fn custom_entries(role: &str, payload: &serde_json::Value) -> Vec<(Kind, String)> {
    match role {
        // The user's own `!command`: what it ran and printed.
        "bashExecution" => {
            if payload
                .get("excludeFromContext")
                .and_then(serde_json::Value::as_bool)
                .unwrap_or(false)
            {
                return Vec::new();
            }
            let command = payload
                .get("command")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("");
            let output = payload
                .get("output")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("");
            vec![(Kind::User, cap_text(&format!("Ran `{command}`\n{output}")))]
        }
        "custom" => {
            let custom_type = payload
                .get("customType")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("");
            let text = match payload.get("content") {
                Some(serde_json::Value::String(text)) => text.clone(),
                Some(content) => serde_json::from_value::<UserContent>(content.clone())
                    .map(|content| user_text(&content))
                    .unwrap_or_default(),
                None => String::new(),
            };
            if text.trim().is_empty() {
                return Vec::new();
            }
            match classify_custom(custom_type) {
                CustomRow::Report => vec![(Kind::User, report_line(custom_type, &text))],
                CustomRow::Nudge | CustomRow::State => Vec::new(),
            }
        }
        // Compaction and branch summaries are the harness's own rewrites
        // of history already in the log.
        _ => Vec::new(),
    }
}

/// What a session `custom` row is to the chat.
enum CustomRow {
    /// A report or a background event: logged as `[id] ...` and delivered
    /// with the user's texts.
    Report,
    /// A harness nudge (a goal continuation): delivered with the user's
    /// texts, never logged (not the user's words).
    Nudge,
    /// Harness state and bookkeeping: re-derived every turn, or never
    /// model context; never logged, never among the user's texts.
    State,
}

fn classify_custom(custom_type: &str) -> CustomRow {
    match custom_type {
        "goal_context" | "autonomous_status" => CustomRow::Nudge,
        "harness_digest"
        | "ipython_state"
        | "ipython_state_restored"
        | "python_skills_unavailable"
        | "thread_goal_state"
        | "refinement_notice"
        | "refinement_outcome"
        | "compaction_outcome"
        | "provider_retry_outcome"
        | "model_prompt_error"
        | "session_slash_command"
        | "session_slash_command_result"
        | "anthropic_subscription_warning_shown" => CustomRow::State,
        _ => CustomRow::Report,
    }
}

/// A report's log line: ONE leading `[id] `, then the report (§9), so the
/// compactor and the view tag it `work`. The delivered row keeps its own
/// header (`[agent-message from child:x]\n\nbody` and the like); the log
/// holds `[child:x] body`.
fn report_line(custom_type: &str, text: &str) -> String {
    let bracketed = text.strip_prefix('[').and_then(|rest| {
        let end = rest.find(']')?;
        Some((&rest[..end], rest[end + 1..].trim_start_matches('\n')))
    });
    // `[id] headline`, the body on its own line after a headline.
    let line = |id: &str, headline: &str, body: &str| {
        let mut line = format!("[{id}] {headline}");
        if !body.is_empty() {
            if !headline.is_empty() {
                line.push('\n');
            }
            line.push_str(body);
        }
        line
    };
    let normalized = match (custom_type, bracketed) {
        ("agent_message", Some((header, body))) => header
            .strip_prefix("agent-message from ")
            .map(|sender| line(sender, "", body)),
        ("rlm_child_terminal_notice", Some((header, body))) => header
            .strip_prefix("child-exited: ")
            .and_then(|rest| rest.split_once(' '))
            .map(|(how, child)| line(child, &format!("exited ({how})"), body)),
        ("rlm_child_failure", Some((header, body))) => header
            .strip_prefix("child-failed ")
            .map(|child| line(child, "failed", body)),
        ("heartbeat_prompt", Some((header, body))) => header
            .strip_prefix("heartbeat: ")
            .map(|run| line("heartbeat", run, body)),
        ("async_bash_completion", Some((header, body))) => header
            .strip_prefix("bash-")
            .map(|done| line("bash", done, body)),
        _ => None,
    };
    normalized.unwrap_or_else(|| format!("[{custom_type}] {text}"))
}

/// Whether a leading message of a call joins the user's texts in the
/// call's first message (§7); harness state rides right after it.
fn joins_user_texts(message: &AgentMessage) -> bool {
    match message {
        AgentMessage::Standard(Message::User(_)) => true,
        AgentMessage::Standard(Message::Assistant(_) | Message::ToolResult(_)) => false,
        AgentMessage::Custom(custom) => match custom.role.as_str() {
            "bashExecution" => true,
            "custom" => {
                let custom_type = custom
                    .payload
                    .get("customType")
                    .and_then(serde_json::Value::as_str)
                    .unwrap_or("");
                match classify_custom(custom_type) {
                    CustomRow::Report | CustomRow::Nudge => true,
                    CustomRow::State => false,
                }
            }
            _ => false,
        },
    }
}

fn user_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Parts(parts) => parts
            .iter()
            .map(|part| match part {
                UserPart::Text(text) => text.text.clone(),
                UserPart::Image(image) => format!("[image: {}]", image.mime_type),
            })
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

fn now_millis() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |duration| duration.as_millis() as i64)
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod wait_status_tests;
