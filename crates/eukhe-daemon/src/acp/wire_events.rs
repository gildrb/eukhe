//! Daemon session-event mapping: the TS `acpUpdatesForSessionEvent` port
//! for the wire shapes a daemon worker streams (`message_start/update/end`,
//! `tool_execution_*`, `bash_*`, `compaction_end`, `loop_update`,
//! `acceptance_update`, `session_info_changed`, ...): the ACP frames the
//! daemon worker's session events produce.
//!
//! Events with no ACP counterpart (`turn_end`, `auto_retry_*`,
//! `agent_begin/end`, `session_action_update`) map to nothing, exactly like
//! the TS switch's default arm.

use std::collections::HashMap;

use eukhe_types::acceptance::{AcceptanceCheck, AcceptanceState, CheckSpec, CheckVerdict};
use eukhe_types::budget::BudgetReport;
use serde::Deserialize as _;
use serde_json::{json, Value};

use super::meta::{eukhe_meta, EukheCompactionMeta, EukheSessionMeta};
use super::types::{
    AcpSessionUpdate, AcpToolKind, AcpToolStatus, PlanEntry, PlanPriority, PlanStatus, TextBlock,
    ToolCallContent, ToolCallLocation, ToolCallStart,
};

/// The model-facing Python REPL tool.
const PYTHON_TOOL_NAME: &str = "python";

/// Correlates streamed chunks with their owning assistant message (the
/// daemon stream carries the delta on `assistantMessageEvent`) and bash
/// output chunks with the run that produced them.
#[derive(Debug, Default)]
pub struct WireMappingState {
    /// The session's cwd: a tool's relative path becomes absolute in it.
    cwd: std::path::PathBuf,
    next_assistant_message_sequence: u64,
    active_assistant_message_id: Option<String>,
    /// The active assistant message's text and thinking already published
    /// as chunks, each concatenated across its blocks.
    published: PublishedChunks,
    active_bash_run_id: Option<String>,
    /// The output each running tool call reported so far: an aborted call
    /// keeps it in front of its abort note.
    partial_outputs: HashMap<String, String>,
    /// Whether the session's checks were last published as a non-empty plan.
    plan: PlanShown,
}

/// What the client holds of the checks' plan.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
enum PlanShown {
    #[default]
    Nothing,
    Entries,
}

/// What one assistant message has published so far.
#[derive(Debug, Default)]
struct PublishedChunks {
    text: String,
    thinking: String,
}

impl WireMappingState {
    /// The mapping of a session that runs in `cwd`.
    pub fn in_cwd(cwd: std::path::PathBuf) -> Self {
        WireMappingState {
            cwd,
            ..WireMappingState::default()
        }
    }

    fn start_assistant_message(&mut self) -> String {
        self.next_assistant_message_sequence += 1;
        let id = format!("eukhe-assistant-{}", self.next_assistant_message_sequence);
        self.active_assistant_message_id = Some(id.clone());
        self.published = PublishedChunks::default();
        id
    }

    fn message_started(&mut self) -> String {
        self.active_assistant_message_id
            .clone()
            .unwrap_or_else(|| self.start_assistant_message())
    }

    /// The chunks for the text and thinking `message` carries beyond what
    /// its deltas published, in content-block order. The durable Harness
    /// commits the in-flight partial at most every 100 ms, so a fast
    /// answer can arrive whole on its `message_start`/`message_end` with no
    /// delta at all; the client still sees every word exactly once. A
    /// message whose published run is not a prefix of its content (a
    /// replaced partial) publishes nothing more.
    fn unpublished_chunks(&mut self, message: &Value) -> Vec<AcpSessionUpdate> {
        let Some(blocks) = message.get("content").and_then(Value::as_array) else {
            return Vec::new();
        };
        let mut text = String::new();
        let mut thinking = String::new();
        let mut pieces = Vec::new();
        for block in blocks {
            let (run, published, is_text) = match block.get("type").and_then(Value::as_str) {
                Some("text") => (&mut text, self.published.text.len(), true),
                Some("thinking") => (&mut thinking, self.published.thinking.len(), false),
                _ => continue,
            };
            let field = if is_text { "text" } else { "thinking" };
            let Some(content) = block.get(field).and_then(Value::as_str) else {
                continue;
            };
            let start = published.max(run.len());
            run.push_str(content);
            if run.len() > start && run.is_char_boundary(start) {
                pieces.push((is_text, run[start..].to_owned()));
            }
        }
        if pieces.is_empty()
            || !text.starts_with(self.published.text.as_str())
            || !thinking.starts_with(self.published.thinking.as_str())
        {
            return Vec::new();
        }
        self.published = PublishedChunks { text, thinking };
        let message_id = self.message_started();
        pieces
            .into_iter()
            .map(|(is_text, delta)| {
                let message_id = message_id.clone();
                let content = TextBlock::new(delta);
                if is_text {
                    AcpSessionUpdate::AgentMessageChunk {
                        message_id,
                        content,
                    }
                } else {
                    AcpSessionUpdate::AgentThoughtChunk {
                        message_id,
                        content,
                    }
                }
            })
            .collect()
    }
}

/// Whether `event` carries an assistant message.
fn is_assistant(event: &Value) -> bool {
    event
        .get("message")
        .and_then(|message| message.get("role"))
        .and_then(Value::as_str)
        == Some("assistant")
}

/// The assistant stop reason carried by one `message_end` event: the
/// transport keeps the newest one and reads it after the turn for the
/// stop-reason response.
pub struct AssistantStop {
    pub stop_reason: Option<eukhe_types::ai::StopReason>,
}

/// Extract the assistant stop reason from one wire event, when the event
/// settles an assistant message.
pub fn assistant_stop(event: &Value) -> Option<AssistantStop> {
    if event.get("type").and_then(Value::as_str) != Some("message_end") {
        return None;
    }
    let message = event.get("message")?;
    if message.get("role").and_then(Value::as_str) != Some("assistant") {
        return None;
    }
    Some(AssistantStop {
        stop_reason: message
            .get("stopReason")
            .and_then(|value| eukhe_types::ai::StopReason::deserialize(value).ok()),
    })
}

/// Map one daemon session event to zero or more ACP updates.
pub fn wire_updates(event: &Value, state: &mut WireMappingState) -> Vec<AcpSessionUpdate> {
    let event_type = event
        .get("type")
        .and_then(Value::as_str)
        .unwrap_or_default();
    match event_type {
        "message_start" => {
            if !is_assistant(event) {
                return Vec::new();
            }
            state.start_assistant_message();
            event
                .get("message")
                .map(|message| state.unpublished_chunks(message))
                .unwrap_or_default()
        }
        "message_update" => {
            if !is_assistant(event) {
                return Vec::new();
            }
            let stream = event.get("assistantMessageEvent");
            let delta = stream
                .and_then(|stream| stream.get("delta"))
                .and_then(Value::as_str)
                .unwrap_or_default();
            if delta.is_empty() {
                // A delta-less update (a block end, a replaced message) may
                // still carry text no delta published.
                return event
                    .get("message")
                    .map(|message| state.unpublished_chunks(message))
                    .unwrap_or_default();
            }
            let message_id = state.message_started();
            match stream
                .and_then(|stream| stream.get("type"))
                .and_then(Value::as_str)
            {
                Some("thinking_delta") => {
                    state.published.thinking.push_str(delta);
                    vec![AcpSessionUpdate::AgentThoughtChunk {
                        message_id,
                        content: TextBlock::new(delta),
                    }]
                }
                Some("text_delta") => {
                    state.published.text.push_str(delta);
                    vec![AcpSessionUpdate::AgentMessageChunk {
                        message_id,
                        content: TextBlock::new(delta),
                    }]
                }
                _ => Vec::new(),
            }
        }
        "message_end" => {
            if !is_assistant(event) {
                return Vec::new();
            }
            let chunks = event
                .get("message")
                .map(|message| state.unpublished_chunks(message))
                .unwrap_or_default();
            state.active_assistant_message_id = None;
            chunks
        }
        "tool_execution_start" => {
            let tool_call_id = string_field(event, "toolCallId");
            let tool_name = string_field(event, "toolName");
            let args = event.get("args").cloned().unwrap_or(Value::Null);
            vec![AcpSessionUpdate::ToolCall(tool_call_start(
                tool_call_id,
                &tool_name,
                args,
                &state.cwd,
            ))]
        }
        "tool_execution_update" => {
            let tool_call_id = string_field(event, "toolCallId");
            let Some(text) = tool_result_text(event.get("partialResult")) else {
                return Vec::new();
            };
            state
                .partial_outputs
                .insert(tool_call_id.clone(), text.clone());
            vec![AcpSessionUpdate::ToolCallUpdate {
                tool_call_id,
                status: Some(AcpToolStatus::InProgress),
                content: Some(vec![ToolCallContent::new(text)]),
                meta: None,
            }]
        }
        "tool_execution_end" => {
            let tool_call_id = string_field(event, "toolCallId");
            let is_error = event
                .get("isError")
                .and_then(Value::as_bool)
                .unwrap_or(false);
            let partial = state.partial_outputs.remove(&tool_call_id);
            let text = final_output(
                partial,
                tool_result_text(event.get("result")),
                ToolEnd::of(is_error),
            );
            let rich = python_rich_output(event.get("result"));
            let update = AcpSessionUpdate::ToolCallUpdate {
                tool_call_id,
                status: Some(if is_error {
                    AcpToolStatus::Failed
                } else {
                    AcpToolStatus::Completed
                }),
                content: text.map(|text| vec![ToolCallContent::new(text)]),
                meta: rich.map(|rich| {
                    eukhe_meta(&EukheSessionMeta {
                        python: Some(rich),
                        ..Default::default()
                    })
                }),
            };
            vec![update]
        }
        // User-level bash runs outside the tool-call lifecycle: a synthetic
        // tool call keyed by run id keeps the streamed chunks addressable.
        "bash_start" => {
            let command = event
                .get("command")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            let run_id = event
                .get("runId")
                .and_then(Value::as_str)
                .map(str::to_string);
            state.active_bash_run_id.clone_from(&run_id);
            vec![AcpSessionUpdate::ToolCall(ToolCallStart {
                tool_call_id: bash_tool_call_id(run_id),
                title: format!("Run `{command}`"),
                name: "bash".to_string(),
                kind: AcpToolKind::Execute,
                status: AcpToolStatus::InProgress,
                raw_input: json!({ "command": command }),
                locations: Vec::new(),
                content: Vec::new(),
            })]
        }
        "bash_output" => {
            let chunk = event
                .get("chunk")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string();
            vec![AcpSessionUpdate::ToolCallUpdate {
                tool_call_id: bash_tool_call_id(state.active_bash_run_id.clone()),
                status: Some(AcpToolStatus::InProgress),
                content: Some(vec![super::types::ToolCallContent::new(chunk)]),
                meta: None,
            }]
        }
        "bash_end" => {
            let run_id = event
                .get("runId")
                .and_then(Value::as_str)
                .map(str::to_string);
            if state.active_bash_run_id == run_id {
                state.active_bash_run_id = None;
            }
            let completed = event.get("exitCode").and_then(Value::as_i64) == Some(0)
                && !event
                    .get("cancelled")
                    .and_then(Value::as_bool)
                    .unwrap_or(false);
            vec![AcpSessionUpdate::ToolCallUpdate {
                tool_call_id: bash_tool_call_id(run_id),
                status: Some(if completed {
                    AcpToolStatus::Completed
                } else {
                    AcpToolStatus::Failed
                }),
                content: None,
                meta: None,
            }]
        }
        // The session's budget rides the namespaced meta; a
        // session without a budget (`budget: null`) has nothing to show.
        "budget_update" => {
            let report = event
                .get("budget")
                .filter(|budget| !budget.is_null())
                .and_then(|budget| BudgetReport::deserialize(budget).ok());
            report
                .map(|budget| AcpSessionUpdate::SessionInfoUpdate {
                    meta: eukhe_meta(&EukheSessionMeta {
                        budget: Some(budget),
                        ..Default::default()
                    }),
                })
                .into_iter()
                .collect()
        }
        "loop_update" => {
            // The whole status rides the meta; an event without a readable
            // one has nothing to publish.
            let status = event
                .get("loop")
                .and_then(|status| eukhe_types::loop_mode::LoopStatus::deserialize(status).ok());
            match status {
                Some(status) => vec![AcpSessionUpdate::SessionInfoUpdate {
                    meta: eukhe_meta(&EukheSessionMeta {
                        r#loop: Some(status),
                        ..Default::default()
                    }),
                }],
                None => Vec::new(),
            }
        }
        "compaction_end" => {
            let result = event.get("result");
            vec![AcpSessionUpdate::SessionInfoUpdate {
                meta: eukhe_meta(&EukheSessionMeta {
                    compaction: Some(EukheCompactionMeta {
                        tokens_before: result
                            .and_then(|result| result.get("tokensBefore"))
                            .and_then(Value::as_u64),
                        summary: result
                            .and_then(|result| result.get("summary"))
                            .and_then(Value::as_str)
                            .map(str::to_string),
                    }),
                    ..Default::default()
                }),
            }]
        }
        "rlm_child_update" => {
            let child = event.get("child");
            vec![AcpSessionUpdate::SessionInfoUpdate {
                meta: eukhe_meta(&EukheSessionMeta {
                    subagents: Some(vec![super::meta::EukheSubagentMeta {
                        id: child
                            .and_then(|child| child.get("id"))
                            .and_then(Value::as_str)
                            .unwrap_or_default()
                            .to_string(),
                        session_name: child
                            .and_then(|child| child.get("sessionName"))
                            .and_then(Value::as_str)
                            .map(str::to_string),
                        status: child
                            .and_then(|child| child.get("status"))
                            .and_then(Value::as_str)
                            .unwrap_or_default()
                            .to_string(),
                        model: child
                            .and_then(|child| child.get("model"))
                            .and_then(Value::as_str)
                            .map(str::to_string),
                        depth: None,
                        token_count: child
                            .and_then(|child| child.get("tokenCount"))
                            .and_then(Value::as_u64),
                        error: child
                            .and_then(|child| child.get("error"))
                            .and_then(Value::as_str)
                            .map(str::to_string),
                    }]),
                    ..Default::default()
                }),
            }]
        }
        "refine_complete" => {
            let result = event.get("result");
            let changes = result
                .and_then(|result| result.get("appliedEdits"))
                .and_then(Value::as_array)
                .map(|edits| {
                    edits
                        .iter()
                        .filter(|edit| edit.get("applied") == Some(&json!(true)))
                        .filter_map(|edit| {
                            let action = edit.get("action").and_then(Value::as_str)?;
                            let kind = edit.get("kind").and_then(Value::as_str)?;
                            let id = edit.get("id").and_then(Value::as_str)?;
                            Some(format!("{action} {kind}:{id}"))
                        })
                        .collect::<Vec<String>>()
                });
            vec![AcpSessionUpdate::SessionInfoUpdate {
                meta: eukhe_meta(&EukheSessionMeta {
                    refinement: Some(super::meta::EukheRefinementMeta {
                        status: "complete".to_string(),
                        summary: result
                            .and_then(|result| result.get("summary"))
                            .and_then(Value::as_str)
                            .map(str::to_string),
                        changes,
                        error: None,
                    }),
                    ..Default::default()
                }),
            }]
        }
        "refine_failed" => {
            vec![AcpSessionUpdate::SessionInfoUpdate {
                meta: eukhe_meta(&EukheSessionMeta {
                    refinement: Some(super::meta::EukheRefinementMeta {
                        status: "failed".to_string(),
                        summary: None,
                        changes: None,
                        error: event
                            .get("error")
                            .and_then(Value::as_str)
                            .map(str::to_string),
                    }),
                    ..Default::default()
                }),
            }]
        }
        "python_sent_agent_message" => {
            let message = event.get("message");
            vec![AcpSessionUpdate::SessionInfoUpdate {
                meta: eukhe_meta(&EukheSessionMeta {
                    agent_message: Some(super::meta::EukheAgentMessageMeta {
                        tool_call_id: event
                            .get("toolCallId")
                            .and_then(Value::as_str)
                            .unwrap_or_default()
                            .to_string(),
                        target: message
                            .and_then(|message| message.get("target"))
                            .and_then(|target| {
                                target
                                    .get("sessionName")
                                    .or_else(|| target.get("sessionId"))
                            })
                            .and_then(Value::as_str)
                            .map(str::to_string),
                        delivery_status: message
                            .and_then(|message| message.get("deliveryStatus"))
                            .and_then(Value::as_str)
                            .map(str::to_string),
                    }),
                    ..Default::default()
                }),
            }]
        }
        "session_info_changed" => vec![AcpSessionUpdate::TitleUpdate {
            title: event
                .get("name")
                .and_then(Value::as_str)
                .map(str::to_string),
        }],
        "acceptance_update" => {
            let Some(acceptance) = event
                .get("acceptance")
                .and_then(|acceptance| AcceptanceState::deserialize(acceptance).ok())
            else {
                return Vec::new();
            };
            let entries: Vec<PlanEntry> = acceptance.checks.iter().map(plan_entry).collect();
            let (shown, updates) = plan_updates(state.plan, entries);
            state.plan = shown;
            updates
        }
        _ => Vec::new(),
    }
}

/// A string field of an event, empty when absent.
fn string_field(event: &Value, key: &str) -> String {
    event
        .get(key)
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_string()
}

/// The `tool_call` of one tool execution: a title for people, the tool's
/// name, its input (a shell step's `command` beside its `script`), and the
/// file it names, absolute in `cwd`.
pub(super) fn tool_call_start(
    tool_call_id: String,
    tool_name: &str,
    args: Value,
    cwd: &std::path::Path,
) -> ToolCallStart {
    let locations = args
        .get("path")
        .and_then(Value::as_str)
        .map(|path| {
            vec![ToolCallLocation {
                path: cwd.join(path).display().to_string(),
            }]
        })
        .unwrap_or_default();
    ToolCallStart {
        tool_call_id,
        title: tool_title(tool_name, &args),
        name: tool_name.to_string(),
        kind: AcpToolKind::of_tool(tool_name),
        status: AcpToolStatus::InProgress,
        raw_input: tool_raw_input(tool_name, args),
        locations,
        content: Vec::new(),
    }
}

/// The call's own intent (`i`), else what it runs or touches.
fn tool_title(tool_name: &str, args: &Value) -> String {
    let text = |key: &str| {
        args.get(key)
            .and_then(Value::as_str)
            .map(str::trim)
            .filter(|text| !text.is_empty())
    };
    if let Some(intent) = text("i") {
        return intent.to_string();
    }
    match (tool_name, text("script"), text("path")) {
        (PYTHON_TOOL_NAME, _, _) => "Python cell".to_string(),
        (_, Some(script), _) => format!("Run `{}`", script.lines().next().unwrap_or(script)),
        (_, None, Some(path)) => format!("{tool_name} {path}"),
        (_, None, None) => tool_name.to_string(),
    }
}

/// The `rawInput` of a call: a Python cell's code; a shell step's args
/// with its script also as `command`; any other tool's args.
fn tool_raw_input(tool_name: &str, args: Value) -> Value {
    if tool_name == PYTHON_TOOL_NAME {
        return match args.get("code").and_then(Value::as_str) {
            Some(code) => json!({ "code": code }),
            None => args,
        };
    }
    match (args, tool_name) {
        (Value::Object(mut fields), "bash") => {
            if let Some(script) = fields.get("script").cloned() {
                fields.entry("command").or_insert(script);
            }
            Value::Object(fields)
        }
        (args, _) => args,
    }
}

/// How a tool call ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ToolEnd {
    Completed,
    Failed,
}

impl ToolEnd {
    fn of(is_error: bool) -> ToolEnd {
        if is_error {
            ToolEnd::Failed
        } else {
            ToolEnd::Completed
        }
    }
}

/// A call's last content: its result; a failed (aborted) call keeps the
/// output it reported before its error.
fn final_output(partial: Option<String>, result: Option<String>, end: ToolEnd) -> Option<String> {
    match (end, partial, result) {
        (ToolEnd::Failed, Some(partial), Some(result)) if !result.contains(&partial) => {
            Some(format!("{partial}\n{result}"))
        }
        (ToolEnd::Failed, Some(partial), None) => Some(partial),
        (ToolEnd::Failed | ToolEnd::Completed, _, result) => result,
    }
}

/// What one acceptance check asks, for people.
pub(super) fn check_text(spec: &CheckSpec) -> String {
    match spec {
        CheckSpec::Command { command, .. } => format!("`{command}` passes"),
        CheckSpec::Judge { condition, .. } => condition.clone(),
        CheckSpec::Until { command, .. } => format!("Until `{command}` passes"),
        CheckSpec::Intent { .. } => "The result meets the task's intent".to_string(),
    }
}

/// One check as a plan entry: done once confirmed, in progress while its
/// last verdict is any other.
fn plan_entry(check: &AcceptanceCheck) -> PlanEntry {
    PlanEntry {
        content: check_text(&check.spec),
        priority: PlanPriority::High,
        status: match check.result.as_ref().map(|result| result.verdict) {
            None => PlanStatus::Pending,
            Some(CheckVerdict::Confirmed) => PlanStatus::Completed,
            Some(CheckVerdict::Refuted | CheckVerdict::Broken | CheckVerdict::Unjudged) => {
                PlanStatus::InProgress
            }
        },
    }
}

/// The `plan` updates for the checks now: their entries, an empty plan
/// once the checks are gone, nothing while there were and are none.
fn plan_updates(shown: PlanShown, entries: Vec<PlanEntry>) -> (PlanShown, Vec<AcpSessionUpdate>) {
    match (shown, entries.is_empty()) {
        (PlanShown::Nothing, true) => (PlanShown::Nothing, Vec::new()),
        (PlanShown::Entries, true) => (
            PlanShown::Nothing,
            vec![AcpSessionUpdate::Plan {
                entries: Vec::new(),
            }],
        ),
        (PlanShown::Nothing | PlanShown::Entries, false) => {
            (PlanShown::Entries, vec![AcpSessionUpdate::Plan { entries }])
        }
    }
}

/// The text of an assistant message that `message_end` settles: the
/// turn's latest answer.
pub fn assistant_answer(event: &Value) -> Option<String> {
    if event.get("type").and_then(Value::as_str) != Some("message_end") || !is_assistant(event) {
        return None;
    }
    let text = event
        .get("message")?
        .get("content")?
        .as_array()?
        .iter()
        .filter(|block| block.get("type").and_then(Value::as_str) == Some("text"))
        .filter_map(|block| block.get("text").and_then(Value::as_str))
        .collect::<String>();
    (!text.trim().is_empty()).then_some(text)
}

/// The synthetic tool-call id of a user-level bash run:
/// `eukhe-bash-<runId>`; a run without an id keys the bare prefix
/// (TS `bashToolCallId`).
fn bash_tool_call_id(run_id: Option<String>) -> String {
    match run_id {
        Some(run_id) => format!("eukhe-bash-{run_id}"),
        None => "eukhe-bash".to_string(),
    }
}

/// TS `toolResultText`: the text of a tool result, wherever the engine
/// carries it. Empty text blocks drop out before the join and an empty
/// text yields `None`, so no update carries empty content (the TS call
/// site's `text ? { content } : {}`).
pub(super) fn tool_result_text(result: Option<&Value>) -> Option<String> {
    let result = result?;
    if let Some(text) = result.as_str() {
        return (!text.is_empty()).then(|| text.to_string());
    }
    if let Some(output) = result.get("output").and_then(Value::as_str) {
        return (!output.is_empty()).then(|| output.to_string());
    }
    let content = result.get("content")?.as_array()?;
    let parts: Vec<String> = content
        .iter()
        .filter_map(|block| {
            (block.get("type").and_then(Value::as_str) == Some("text"))
                .then(|| {
                    block
                        .get("text")
                        .and_then(Value::as_str)
                        .map(str::to_string)
                })
                .flatten()
        })
        .filter(|text| !text.is_empty())
        .collect();
    (!parts.is_empty()).then(|| parts.join("\n"))
}

/// Decoded byte length of a base64 payload, without materializing it.
fn base64_byte_length(data: &str) -> u64 {
    let padding = if data.ends_with("==") {
        2
    } else {
        u64::from(data.ends_with('='))
    };
    (data.len() as u64 * 3 / 4).saturating_sub(padding)
}

/// TS `ipythonRichOutput`: media rides the namespaced meta.
fn python_rich_output(result: Option<&Value>) -> Option<Value> {
    let details = result?.get("details")?;
    let attachments = details
        .get("attachments")
        .and_then(Value::as_array)
        .map(|attachments| {
            attachments
                .iter()
                .map(|attachment| {
                    let mut row = serde_json::Map::new();
                    if let Some(mime_type) = attachment.get("mimeType").and_then(Value::as_str) {
                        row.insert("mimeType".to_string(), json!(mime_type));
                    }
                    if let Some(path) = attachment.get("path").and_then(Value::as_str) {
                        row.insert("path".to_string(), json!(path));
                    }
                    if let Some(bytes) = attachment
                        .get("data")
                        .and_then(Value::as_str)
                        .map(base64_byte_length)
                    {
                        row.insert("bytes".to_string(), json!(bytes));
                    }
                    Value::Object(row)
                })
                .collect::<Vec<_>>()
        })
        .filter(|attachments| !attachments.is_empty())?;
    let mut meta = serde_json::Map::new();
    meta.insert("attachments".to_string(), Value::Array(attachments));
    Some(Value::Object(meta))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assistant_deltas_map_to_chunks() {
        let mut state = WireMappingState::default();
        let updates = wire_updates(
            &json!({
                "type": "message_update",
                "message": { "role": "assistant" },
                "assistantMessageEvent": { "type": "thinking_delta", "delta": "think" },
            }),
            &mut state,
        );
        assert_eq!(updates.len(), 1);
        assert_eq!(
            serde_json::to_value(&updates[0]).unwrap()["sessionUpdate"],
            "agent_thought_chunk"
        );
        let updates = wire_updates(
            &json!({
                "type": "message_update",
                "message": { "role": "assistant" },
                "assistantMessageEvent": { "type": "text_delta", "delta": "answer" },
            }),
            &mut state,
        );
        assert_eq!(updates.len(), 1);
        assert_eq!(
            serde_json::to_value(&updates[0]).unwrap()["sessionUpdate"],
            "agent_message_chunk"
        );
    }

    /// The durable Harness throttles partial commits, so an answer may
    /// arrive whole on `message_start`/`message_end`: the text no delta
    /// published goes out as chunks, once, in block order.
    #[test]
    fn unstreamed_assistant_text_maps_to_chunks_once() {
        let mut state = WireMappingState::default();
        let chunk = |update: &AcpSessionUpdate| {
            let value = serde_json::to_value(update).unwrap();
            (
                value["sessionUpdate"].as_str().unwrap().to_owned(),
                value["content"]["text"].as_str().unwrap().to_owned(),
                value["messageId"].as_str().unwrap().to_owned(),
            )
        };
        let message = |thinking: &str, text: &str| {
            json!({
                "role": "assistant",
                "content": [
                    { "type": "thinking", "thinking": thinking },
                    { "type": "text", "text": text },
                ],
            })
        };
        let owned =
            |kind: &str, text: &str, id: &str| (kind.to_owned(), text.to_owned(), id.to_owned());
        let start = wire_updates(
            &json!({ "type": "message_start", "message": message("pl", "AC") }),
            &mut state,
        );
        assert_eq!(
            start.iter().map(chunk).collect::<Vec<_>>(),
            [
                owned("agent_thought_chunk", "pl", "eukhe-assistant-1"),
                owned("agent_message_chunk", "AC", "eukhe-assistant-1"),
            ]
        );
        let update = wire_updates(
            &json!({
                "type": "message_update",
                "message": message("pl", "ACP"),
                "assistantMessageEvent": { "type": "text_delta", "delta": "P" },
            }),
            &mut state,
        );
        assert_eq!(update.len(), 1);
        let end = wire_updates(
            &json!({ "type": "message_end", "message": message("pl", "ACP-OK") }),
            &mut state,
        );
        assert_eq!(
            end.iter().map(chunk).collect::<Vec<_>>(),
            [owned("agent_message_chunk", "-OK", "eukhe-assistant-1")]
        );
        // A fully published message adds nothing and takes no message id.
        let end = wire_updates(
            &json!({ "type": "message_end", "message": message("pl", "ACP-OK") }),
            &mut state,
        );
        assert!(end.is_empty());
        let next = wire_updates(
            &json!({ "type": "message_start", "message": message("", "B") }),
            &mut state,
        );
        assert_eq!(chunk(&next[0]).2, "eukhe-assistant-2");
    }

    #[test]
    fn budget_update_maps_to_the_namespaced_budget_meta() {
        // The whole report rides `_meta.com.eukhe.budget`; a session
        // without a budget maps to nothing.
        let report = json!({
            "sessionId": "s1",
            "agentSessionId": "s1",
            "limits": { "tokens": 200_000, "timeMs": 600_000 },
            "free": { "costMicros": 0, "tokens": 198_500, "timeMs": 240_000, "toolCalls": 0, "requests": 0 },
            "held": { "costMicros": 0, "tokens": 0, "timeMs": 0, "toolCalls": 0, "requests": 0 },
            "spent": { "costMicros": 0, "tokens": 1_500, "timeMs": 0, "toolCalls": 0, "requests": 0 },
            "lent": { "costMicros": 0, "tokens": 0, "timeMs": 0, "toolCalls": 0, "requests": 0 },
            "over": { "costMicros": 0, "tokens": 0, "timeMs": 0, "toolCalls": 0, "requests": 0 },
            "phase": "wrap_up",
            "short": "time",
            "deadlineMs": 1_800_000_000_000_u64,
        });
        let mut state = WireMappingState::default();
        let updates: Vec<Value> = [report.clone(), Value::Null]
            .into_iter()
            .flat_map(|budget| {
                wire_updates(
                    &json!({ "type": "budget_update", "budget": budget }),
                    &mut state,
                )
            })
            .map(|update| serde_json::to_value(&update).unwrap())
            .collect();
        assert_eq!(
            updates,
            [json!({
                "sessionUpdate": "session_info_update",
                "_meta": { "com.eukhe": { "budget": report } },
            })]
        );
    }

    /// A `loop_update` publishes the whole loop status under the
    /// namespaced `loop` meta.
    #[test]
    fn loop_update_maps_to_the_namespaced_loop_meta() {
        let mut state = WireMappingState::default();
        let status = json!({
            "phase": { "state": "judging" },
            "iteration": 2,
            "remaining": 8,
            "condition": { "command": "test -f done", "until": true },
            "prompt": "fix it",
            "failures": 0,
            "lastCheck": { "iteration": 1, "evidence": { "kind": "exited", "code": 1 } },
            "limit": { "kind": "iterations", "iterations": 10 },
            "startedAtMs": 5,
            "verdict": 1,
        });
        let updates = wire_updates(
            &json!({ "type": "loop_update", "loop": status }),
            &mut state,
        );
        let frames: Vec<Value> = updates
            .iter()
            .map(|update| serde_json::to_value(update).unwrap())
            .collect();
        assert_eq!(
            frames,
            [json!({
                "sessionUpdate": "session_info_update",
                "_meta": { "com.eukhe": { "loop": status } },
            })]
        );
    }

    #[test]
    fn user_messages_and_lifecycle_events_map_to_nothing() {
        let mut state = WireMappingState::default();
        for event_type in [
            "message_start",
            "message_end",
            "turn_end",
            "agent_begin",
            "session_action_update",
            "auto_retry_start",
        ] {
            let updates = wire_updates(
                &json!({ "type": event_type, "message": { "role": "user" } }),
                &mut state,
            );
            assert!(updates.is_empty(), "{event_type} maps to nothing");
        }
    }

    #[test]
    fn tool_calls_and_completions_map_like_the_ts_adapter() {
        let mut state = WireMappingState::default();
        let updates = wire_updates(
            &json!({
                "type": "tool_execution_start",
                "toolCallId": "call-1",
                "toolName": "python",
                "args": { "code": "print(1)" },
            }),
            &mut state,
        );
        let value = serde_json::to_value(&updates[0]).unwrap();
        assert_eq!(value["sessionUpdate"], "tool_call");
        assert_eq!(value["title"], "Python cell");
        assert_eq!(value["rawInput"], json!({ "code": "print(1)" }));
        let updates = wire_updates(
            &json!({
                "type": "tool_execution_end",
                "toolCallId": "call-1",
                "result": { "output": "1\n" },
                "isError": false,
            }),
            &mut state,
        );
        let value = serde_json::to_value(&updates[0]).unwrap();
        assert_eq!(value["sessionUpdate"], "tool_call_update");
        assert_eq!(value["status"], "completed");
        assert_eq!(value["content"][0]["content"]["text"], "1\n");
    }

    /// A shell step's call: its intent as the title, the tool's name, the
    /// script also as `command`, the file it names made absolute; its
    /// output streams and stays in front of the abort note.
    #[test]
    fn a_shell_call_streams_its_output_and_keeps_it_on_abort() {
        let mut state = WireMappingState::in_cwd("/work".into());
        let args = json!({ "i": "Listing files", "script": "ls", "path": "src" });
        let frames: Vec<Value> = [
            json!({ "type": "tool_execution_start", "toolCallId": "c1", "toolName": "bash", "args": args }),
            json!({ "type": "tool_execution_update", "toolCallId": "c1", "toolName": "bash", "args": args,
                "partialResult": { "content": [{ "type": "text", "text": "a.rs" }] } }),
            json!({ "type": "tool_execution_end", "toolCallId": "c1", "toolName": "bash",
                "result": { "content": [{ "type": "text", "text": "[error] Tool bash was aborted" }] }, "isError": true }),
        ]
        .iter()
        .flat_map(|event| wire_updates(event, &mut state))
        .map(|update| update.to_bare_value())
        .collect();
        assert_eq!(
            frames,
            [
                json!({
                    "sessionUpdate": "tool_call", "toolCallId": "c1", "title": "Listing files",
                    "name": "bash", "kind": "execute", "status": "in_progress",
                    "rawInput": { "i": "Listing files", "script": "ls", "path": "src", "command": "ls" },
                    "locations": [{ "path": "/work/src" }],
                }),
                json!({
                    "sessionUpdate": "tool_call_update", "toolCallId": "c1", "status": "in_progress",
                    "content": [{ "type": "content", "content": { "type": "text", "text": "a.rs" } }],
                }),
                json!({
                    "sessionUpdate": "tool_call_update", "toolCallId": "c1", "status": "failed",
                    "content": [{ "type": "content", "content": { "type": "text",
                        "text": "a.rs\n[error] Tool bash was aborted" } }],
                }),
            ]
        );
    }

    /// The checks are a plan: each change republishes every entry, and the
    /// checks' removal empties it once. The session name is the title.
    #[test]
    fn checks_map_to_the_plan_and_the_name_to_the_title() {
        let mut state = WireMappingState::default();
        let acceptance = |checks: Value| {
            json!({ "type": "acceptance_update", "acceptance": {
                "label": "unverified", "state": 1, "revision": 1, "checks": checks,
                "claimed": false, "tries": 0, "maxReturns": 3,
            }})
        };
        let frames: Vec<Value> = [
            acceptance(json!([
                { "spec": { "kind": "command", "command": "cargo test" } },
                { "spec": { "kind": "intent" }, "result": {
                    "verdict": "confirmed", "at": 1, "summary": "met", "evidence": "", "judgedAt": 2 } },
            ])),
            acceptance(json!([])),
            acceptance(json!([])),
            json!({ "type": "session_info_changed", "name": "Fix the parser" }),
        ]
        .iter()
        .flat_map(|event| wire_updates(event, &mut state))
        .map(|update| update.to_bare_value())
        .collect();
        assert_eq!(
            frames,
            [
                json!({ "sessionUpdate": "plan", "entries": [
                    { "content": "`cargo test` passes", "priority": "high", "status": "pending" },
                    { "content": "The result meets the task's intent", "priority": "high", "status": "completed" },
                ]}),
                json!({ "sessionUpdate": "plan", "entries": [] }),
                json!({ "sessionUpdate": "session_info_update", "title": "Fix the parser" }),
            ]
        );
    }

    #[test]
    fn compaction_end_publishes_the_meta_payload() {
        let mut state = WireMappingState::default();
        let updates = wire_updates(
            &json!({
                "type": "compaction_end",
                "result": { "tokensBefore": 4200, "summary": "a summary" },
            }),
            &mut state,
        );
        let value = serde_json::to_value(&updates[0]).unwrap();
        assert_eq!(value["sessionUpdate"], "session_info_update");
        assert_eq!(
            value["_meta"]["com.eukhe"]["compaction"],
            json!({ "tokensBefore": 4200, "summary": "a summary" })
        );
    }

    #[test]
    fn assistant_stop_reason_is_captured_from_message_end() {
        let stop = assistant_stop(&json!({
            "type": "message_end",
            "message": { "role": "assistant", "stopReason": "length" },
        }))
        .expect("assistant message_end");
        assert_eq!(stop.stop_reason, Some(eukhe_types::ai::StopReason::Length));
        assert!(assistant_stop(&json!({
            "type": "message_end",
            "message": { "role": "user" },
        }))
        .is_none());
    }

    #[test]
    fn empty_tool_results_carry_no_content() {
        let mut state = WireMappingState::default();
        let updates = wire_updates(
            &json!({
                "type": "tool_execution_end",
                "toolCallId": "t1",
                "result": { "output": "" },
                "isError": false,
            }),
            &mut state,
        );
        let value = serde_json::to_value(&updates[0]).unwrap();
        assert_eq!(value["sessionUpdate"], "tool_call_update");
        assert_eq!(value["status"], "completed");
        assert!(value.get("content").is_none(), "no empty content: {value}");
    }

    #[test]
    fn empty_text_blocks_drop_out_of_the_joined_result() {
        let mut state = WireMappingState::default();
        let updates = wire_updates(
            &json!({
                "type": "tool_execution_end",
                "toolCallId": "t1",
                "result": { "content": [
                    { "type": "text", "text": "" },
                    { "type": "text", "text": "a" },
                ] },
                "isError": false,
            }),
            &mut state,
        );
        let value = serde_json::to_value(&updates[0]).unwrap();
        assert_eq!(value["content"][0]["content"]["text"], "a");
    }

    fn namespaced(update: &AcpSessionUpdate) -> Value {
        update.to_bare_value()["_meta"][super::super::meta::EUKHE_META_NAMESPACE].clone()
    }

    #[test]
    fn rlm_child_update_maps_to_the_subagents_meta() {
        let mut state = WireMappingState::default();
        let updates = wire_updates(
            &json!({
                "type": "rlm_child_update",
                "child": {
                    "id": "child-1",
                    "parentId": "node-1",
                    "activeSessionId": "child-live",
                    "sessionName": "worker-a",
                    "model": "z-ai/glm-5.3-flash",
                    "label": "run the lane task",
                    "status": "running",
                    "durationMs": 500,
                    "sessionDir": "/sessions/child-1",
                },
            }),
            &mut state,
        );
        let value = updates[0].to_bare_value();
        assert_eq!(value["sessionUpdate"], "session_info_update");
        assert_eq!(
            namespaced(&updates[0])["subagents"],
            json!([{
                "id": "child-1",
                "sessionName": "worker-a",
                "status": "running",
                "model": "z-ai/glm-5.3-flash",
            }])
        );
        let updates = wire_updates(
            &json!({
                "type": "rlm_child_update",
                "child": {
                    "id": "child-2",
                    "status": "cancelled",
                    "error": "Deleted by parent orchestrator",
                },
            }),
            &mut state,
        );
        assert_eq!(
            namespaced(&updates[0])["subagents"],
            json!([{
                "id": "child-2",
                "status": "cancelled",
                "error": "Deleted by parent orchestrator",
            }])
        );
    }

    #[test]
    fn refine_complete_maps_the_applied_edits_changes() {
        let mut state = WireMappingState::default();
        let updates = wire_updates(
            &json!({
                "type": "refine_complete",
                "result": {
                    "id": "ref-1",
                    "summary": "applied 2 edits",
                    "appliedEdits": [
                        { "action": "create", "kind": "memory", "id": "x", "applied": true },
                        { "action": "update", "kind": "skill", "id": "y", "applied": true },
                        { "action": "delete", "kind": "prompt", "id": "z", "applied": false },
                    ],
                },
            }),
            &mut state,
        );
        assert_eq!(
            namespaced(&updates[0])["refinement"],
            json!({
                "status": "complete",
                "summary": "applied 2 edits",
                "changes": ["create memory:x", "update skill:y"],
            })
        );
        let updates = wire_updates(
            &json!({
                "type": "refine_complete",
                "result": { "id": "ref-2", "summary": "no edits" },
            }),
            &mut state,
        );
        assert_eq!(
            namespaced(&updates[0])["refinement"],
            json!({ "status": "complete", "summary": "no edits" })
        );
    }

    #[test]
    fn refine_failed_maps_the_error_meta() {
        let mut state = WireMappingState::default();
        let updates = wire_updates(
            &json!({ "type": "refine_failed", "error": "Summarization failed: no responses" }),
            &mut state,
        );
        assert_eq!(
            namespaced(&updates[0])["refinement"],
            json!({ "status": "failed", "error": "Summarization failed: no responses" })
        );
    }

    #[test]
    fn python_sent_agent_message_maps_the_target_fallback() {
        let mut state = WireMappingState::default();
        let updates = wire_updates(
            &json!({
                "type": "python_sent_agent_message",
                "toolCallId": "t7",
                "message": {
                    "id": "agentmsg_1",
                    "message": "Ping.",
                    "deliveryStatus": "delivered",
                    "target": {
                        "activeSessionId": "peer-live",
                        "sessionId": "peer-session",
                        "sessionName": "Worker",
                    },
                },
            }),
            &mut state,
        );
        assert_eq!(
            namespaced(&updates[0])["agentMessage"],
            json!({
                "toolCallId": "t7",
                "target": "Worker",
                "deliveryStatus": "delivered",
            })
        );
        let updates = wire_updates(
            &json!({
                "type": "python_sent_agent_message",
                "toolCallId": "t8",
                "message": {
                    "id": "agentmsg_2",
                    "message": "Ping.",
                    "deliveryStatus": "queued",
                    "target": {
                        "activeSessionId": "peer-live",
                        "sessionId": "peer-session",
                    },
                },
            }),
            &mut state,
        );
        assert_eq!(
            namespaced(&updates[0])["agentMessage"],
            json!({
                "toolCallId": "t8",
                "target": "peer-session",
                "deliveryStatus": "queued",
            })
        );
    }
}
