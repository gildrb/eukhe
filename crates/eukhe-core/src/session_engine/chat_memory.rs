//! The chat memory in a session (`OptChat` spec §6-§9). A root session
//! logs everything it says and does to the endless chat and starts every
//! fresh turn from the view; a subagent starts from the view at its spawn
//! and logs nothing. The view rides in front of the loop's messages at the
//! LLM boundary (`transform_context`), so it is never persisted, displayed,
//! or compacted away, and it is rendered only after every line of it is a
//! summary.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_agent::agent_loop::{AfterToolCallFn, TransformContextFn};
use eukhe_agent::types::{
    AfterToolCallResult, AgentEvent, AgentMessage, AssistantContent, CacheBreakpoint, Message,
    TextContent, ToolResultContent, UserContent, UserMessage, UserPart,
};

use crate::memory::{cap_text, Kind, Memory, MemoryRole, CAP};
use crate::tools::tool_definition::{ExecuteFn, ToolDefinition, ToolExecutionResult};

/// One session's view of the chat memory.
pub struct ChatMemory {
    memory: Memory,
    role: MemoryRole,
    /// The view message of the current call: rendered on the call's first
    /// request, then byte-identical on every later step (the cache prefix).
    prefix: Mutex<Option<AgentMessage>>,
    /// Root: the fresh turn's own messages, logged only after the view is
    /// rendered (the view covers everything before them).
    deferred: Mutex<Vec<(Kind, String)>>,
}

impl ChatMemory {
    #[must_use]
    pub fn new(memory: Memory, role: MemoryRole) -> Arc<ChatMemory> {
        Arc::new(ChatMemory {
            memory,
            role,
            prefix: Mutex::new(None),
            deferred: Mutex::new(Vec::new()),
        })
    }

    #[must_use]
    pub fn role(&self) -> MemoryRole {
        self.role
    }

    #[must_use]
    pub fn memory(&self) -> &Memory {
        &self.memory
    }

    /// Whether the next admitted turn of a root session starts a fresh call:
    /// every turn does, except one that continues a call cut at a tool
    /// boundary (the loop's last message is a tool result the model has not
    /// answered yet: a mid-run message delivered between tool calls).
    #[must_use]
    pub fn next_turn_is_fresh(&self, last: Option<&AgentMessage>) -> bool {
        match self.role {
            MemoryRole::Subagent => false,
            MemoryRole::Root => {
                !matches!(last, Some(AgentMessage::Standard(Message::ToolResult(_))))
            }
        }
    }

    /// A fresh call begins: its view is rendered on its first request.
    pub fn begin_fresh_call(&self) {
        *lock(&self.prefix) = None;
    }

    /// The `transform_context` hook: the view message in front of the
    /// loop's messages.
    #[must_use]
    pub fn transform(self: &Arc<Self>) -> TransformContextFn {
        let this = Arc::clone(self);
        Arc::new(move |messages, _signal| {
            let this = Arc::clone(&this);
            // The loop races this future against the turn's abort signal:
            // an aborted wait drops it, and the run's end logs the
            // deferred messages unanswered.
            Box::pin(async move {
                let prefix = this.prefix().await?;
                let mut out = Vec::with_capacity(messages.len() + 1);
                out.push(prefix);
                out.extend(messages);
                Ok(out)
            })
        })
    }

    /// The view message of the current call, rendered (after the view
    /// settles) when no call has rendered one yet: side questions read the
    /// main thread's context through it.
    ///
    /// # Errors
    ///
    /// Returns an error when the view cannot settle or render.
    pub async fn view_message(&self) -> anyhow::Result<AgentMessage> {
        self.prefix().await
    }

    async fn prefix(&self) -> anyhow::Result<AgentMessage> {
        if let Some(prefix) = lock(&self.prefix).clone() {
            return Ok(prefix);
        }
        // Wait until every line of the view is a summary (§6), then render
        // it BEFORE the turn's own messages are logged (§7).
        self.memory.settle().await?;
        let view = self.memory.render().await?;
        let pieces = view.pieces();
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
        let message = AgentMessage::Standard(Message::User(UserMessage {
            content: UserContent::Parts(parts),
            timestamp: now_millis(),
        }));
        if self.role == MemoryRole::Root {
            self.flush_deferred().await?;
        }
        *lock(&self.prefix) = Some(message.clone());
        Ok(message)
    }

    /// Root: log what the loop just finished, as it happens (§7).
    ///
    /// # Errors
    ///
    /// Returns an error when a message cannot be written to the chat: the
    /// memory is the session's history, so a lost line stops the turn.
    pub async fn on_event(&self, event: &AgentEvent) -> anyhow::Result<()> {
        if self.role != MemoryRole::Root {
            return Ok(());
        }
        match event {
            AgentEvent::MessageEnd { message } => {
                let entries = log_entries(message);
                if entries.is_empty() {
                    return Ok(());
                }
                if lock(&self.prefix).is_none() {
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
                // wait) leaves its messages in the log, unanswered.
                self.flush_deferred().await?;
                // Persist after each turn; the owner reports git failures.
                self.memory.persist().await
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

    async fn flush_deferred(&self) -> anyhow::Result<()> {
        let entries = std::mem::take(&mut *lock(&self.deferred));
        for (kind, text) in entries {
            self.memory.append(kind, &text).await?;
        }
        Ok(())
    }
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
/// messages starting with `[`; harness state the next turn re-derives (the
/// harness digest, kernel notices, bookkeeping rows) is not. Thinking is
/// never logged (§2).
fn log_entries(message: &AgentMessage) -> Vec<(Kind, String)> {
    match message {
        AgentMessage::Standard(Message::User(user)) => {
            let text = user_text(&user.content);
            if text.trim().is_empty() {
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
/// event is logged; harness state is not.
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
            match custom_type {
                // Already addressed: `[agent-message from ...]`,
                // `[child-exited: ...]`, `[child-failed ...]`.
                "agent_message" | "rlm_child_terminal_notice" | "rlm_child_failure" => {
                    vec![(Kind::User, text)]
                }
                "goal_context" => vec![(Kind::User, format!("[goal] {text}"))],
                "heartbeat_prompt" => vec![(Kind::User, format!("[heartbeat] {text}"))],
                "async_bash_completion" => vec![(Kind::User, format!("[background] {text}"))],
                "autonomous_status" => vec![(Kind::User, format!("[autonomous] {text}"))],
                // Harness state and bookkeeping: re-derived every turn, or
                // never model context.
                "harness_digest"
                | "ipython_state"
                | "ipython_state_restored"
                | "python_skills_unavailable"
                | "thread_goal_state"
                | "refinement_notice"
                | "refinement_outcome"
                | "compaction_outcome"
                | "provider_retry_outcome"
                | "session_slash_command"
                | "session_slash_command_result"
                | "anthropic_subscription_warning_shown" => Vec::new(),
                other => vec![(Kind::User, format!("[{other}] {text}"))],
            }
        }
        // Compaction and branch summaries are the harness's own rewrites
        // of history already in the log.
        _ => Vec::new(),
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
