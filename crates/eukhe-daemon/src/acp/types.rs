//! ACP wire types: the method surface, `session/update` payload shapes,
//! and prompt-block parsing.
//!
//! The served surface: `initialize`, `authenticate`, `session/new`,
//! `session/load`, `session/resume`, `session/list`, `session/delete`,
//! `session/prompt`, `session/close`, `session/set_config_option`
//! (requests), `session/cancel` (notification), the outgoing
//! `session/update` notification, the outgoing `session/request_permission`
//! request (the editor's say on an irreversible effect, `permission.rs`),
//! and the `_eukhe/` extensions (`extensions.rs`, `run_report.rs`).

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// The `initialize` result payload.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct InitializeResult {
    pub protocol_version: u64,
    pub agent_capabilities: AgentCapabilities,
    pub auth_methods: Value,
    pub agent_info: AgentInfo,
    #[serde(rename = "_meta")]
    pub meta: Value,
}

/// What the agent can do, advertised in `initialize`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentCapabilities {
    pub load_session: bool,
    pub prompt_capabilities: PromptCapabilities,
    pub mcp_capabilities: McpCapabilities,
    pub session_capabilities: SessionCapabilities,
    /// `{"eukhe": {"version", "features"}}`: the `_eukhe/` extensions.
    #[serde(rename = "_meta")]
    pub meta: Value,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PromptCapabilities {
    pub image: bool,
    pub audio: bool,
    pub embedded_context: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct McpCapabilities {
    pub http: bool,
    pub sse: bool,
}

/// Each `{}` member: that session method is served.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SessionCapabilities {
    pub close: ServedMethod,
    pub list: ServedMethod,
    pub resume: ServedMethod,
    pub delete: ServedMethod,
}

/// `{}`: present means the method is served.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Default)]
pub struct ServedMethod {}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentInfo {
    pub name: String,
    pub title: String,
    pub version: String,
}

/// The agent-facing classification of a tool call (`kind` field).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AcpToolKind {
    #[serde(rename = "read")]
    Read,
    #[serde(rename = "edit")]
    Edit,
    #[serde(rename = "delete")]
    Delete,
    #[serde(rename = "move")]
    Move,
    #[serde(rename = "search")]
    Search,
    #[serde(rename = "execute")]
    Execute,
    #[serde(rename = "think")]
    Think,
    #[serde(rename = "fetch")]
    Fetch,
    #[serde(rename = "other")]
    Other,
}

impl AcpToolKind {
    /// The TS kind map: the model-facing tool is the Python REPL; bash is the
    /// secondary escape hatch. `ipython` is the REPL's name in sessions
    /// stored before it became `python`.
    pub fn of_tool(tool_name: &str) -> AcpToolKind {
        match tool_name {
            "python" | "ipython" | "bash" => AcpToolKind::Execute,
            "read" => AcpToolKind::Read,
            "edit" | "write" => AcpToolKind::Edit,
            "grep" | "glob" => AcpToolKind::Search,
            _ => AcpToolKind::Other,
        }
    }
}

/// The lifecycle status of a tool call.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AcpToolStatus {
    Pending,
    InProgress,
    Completed,
    Failed,
}

/// The terminal stop reason of a `session/prompt` request.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AcpStopReason {
    #[serde(rename = "end_turn")]
    EndTurn,
    #[serde(rename = "max_tokens")]
    MaxTokens,
    #[serde(rename = "max_turn_requests")]
    MaxTurnRequests,
    #[serde(rename = "refusal")]
    Refusal,
    #[serde(rename = "cancelled")]
    Cancelled,
}

/// The `session/prompt` result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct AcpStopReasonResponse {
    #[serde(rename = "stopReason")]
    pub stop_reason: AcpStopReason,
}

/// The `session/update` payload body (the `update` object).
///
/// Every variant carries its `sessionUpdate` tag; fields are the exact
/// wire names ACP clients read.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "sessionUpdate")]
pub enum AcpSessionUpdate {
    /// A user message of the history `session/load` replays.
    #[serde(rename = "user_message_chunk")]
    UserMessageChunk { content: TextBlock },
    /// A streaming chunk of the assistant's visible answer.
    #[serde(rename = "agent_message_chunk")]
    AgentMessageChunk {
        #[serde(rename = "messageId")]
        message_id: String,
        content: TextBlock,
    },
    /// A streaming chunk of the assistant's reasoning.
    #[serde(rename = "agent_thought_chunk")]
    AgentThoughtChunk {
        #[serde(rename = "messageId")]
        message_id: String,
        content: TextBlock,
    },
    /// A tool call started executing (or, replayed, ran).
    #[serde(rename = "tool_call")]
    ToolCall(ToolCallStart),
    /// A tool call progressed or finished.
    #[serde(rename = "tool_call_update")]
    ToolCallUpdate {
        #[serde(rename = "toolCallId")]
        tool_call_id: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        status: Option<AcpToolStatus>,
        #[serde(skip_serializing_if = "Option::is_none")]
        content: Option<Vec<ToolCallContent>>,
        #[serde(rename = "_meta", skip_serializing_if = "Option::is_none")]
        meta: Option<Value>,
    },
    /// The session's acceptance checks as a checklist: every entry, each
    /// time one changes.
    #[serde(rename = "plan")]
    Plan { entries: Vec<PlanEntry> },
    /// The session's name changed (`null`: cleared).
    #[serde(rename = "session_info_update")]
    TitleUpdate { title: Option<String> },
    /// Eukhe-only state (budget, compaction, quiescence, ...): published
    /// as `_eukhe/session_info`, never as `session/update`.
    #[serde(rename = "session_info_update")]
    SessionInfoUpdate {
        #[serde(rename = "_meta")]
        meta: Value,
    },
    /// The context window in use and the session's cost so far.
    #[serde(rename = "usage_update")]
    UsageUpdate {
        used: u64,
        size: u64,
        #[serde(skip_serializing_if = "Option::is_none")]
        cost: Option<UsageCost>,
    },
    /// The commands a prompt may start with (`/compact`, templates, skills).
    #[serde(rename = "available_commands_update")]
    AvailableCommandsUpdate {
        #[serde(rename = "availableCommands")]
        available_commands: Vec<AvailableCommand>,
    },
    /// The session's configuration options changed (TS #2455): the full
    /// set with current values, connection-scoped like the TS publish.
    #[serde(rename = "config_option_update")]
    ConfigOptionUpdate {
        #[serde(rename = "configOptions")]
        config_options: Vec<super::config_options::SessionConfigOption>,
    },
}

/// The notification an update rides.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UpdateMethod {
    /// `session/update`: an ACP update every client reads.
    SessionUpdate,
    /// `_eukhe/session_info`: eukhe-only state a plain client never sees.
    EukheSessionInfo,
}

impl UpdateMethod {
    pub fn name(self) -> &'static str {
        match self {
            UpdateMethod::SessionUpdate => "session/update",
            UpdateMethod::EukheSessionInfo => "_eukhe/session_info",
        }
    }
}

impl AcpSessionUpdate {
    /// Serialize to the wire value. `ToolCallUpdate::meta` carries a
    /// namespaced `_meta` payload (see [`meta::eukhe_meta`]); the
    /// producer merges its correlation fields into that payload afterwards.
    pub fn to_bare_value(&self) -> Value {
        serde_json::to_value(self).expect("session updates serialize")
    }

    /// The notification this update rides.
    pub fn method(&self) -> UpdateMethod {
        match self {
            AcpSessionUpdate::SessionInfoUpdate { .. } => UpdateMethod::EukheSessionInfo,
            AcpSessionUpdate::UserMessageChunk { .. }
            | AcpSessionUpdate::AgentMessageChunk { .. }
            | AcpSessionUpdate::AgentThoughtChunk { .. }
            | AcpSessionUpdate::ToolCall(_)
            | AcpSessionUpdate::ToolCallUpdate { .. }
            | AcpSessionUpdate::Plan { .. }
            | AcpSessionUpdate::TitleUpdate { .. }
            | AcpSessionUpdate::UsageUpdate { .. }
            | AcpSessionUpdate::AvailableCommandsUpdate { .. }
            | AcpSessionUpdate::ConfigOptionUpdate { .. } => UpdateMethod::SessionUpdate,
        }
    }
}

/// The `tool_call` body.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ToolCallStart {
    pub tool_call_id: String,
    /// What the call does, for people.
    pub title: String,
    /// The tool's own name.
    pub name: String,
    pub kind: AcpToolKind,
    pub status: AcpToolStatus,
    pub raw_input: Value,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub locations: Vec<ToolCallLocation>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub content: Vec<ToolCallContent>,
}

/// A file a tool call reads or changes.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ToolCallLocation {
    pub path: String,
}

/// One checklist entry of a `plan` update.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct PlanEntry {
    pub content: String,
    pub priority: PlanPriority,
    pub status: PlanStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum PlanPriority {
    High,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum PlanStatus {
    Pending,
    InProgress,
    Completed,
}

/// A `usage_update` cost.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct UsageCost {
    pub amount: f64,
    pub currency: &'static str,
}

/// One `available_commands_update` entry.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct AvailableCommand {
    pub name: String,
    pub description: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub input: Option<CommandInput>,
}

/// The text a command takes after its name.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CommandInput {
    pub hint: String,
}

/// `{ "type": "text", "text": ... }`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TextBlock {
    #[serde(rename = "type")]
    pub kind: String,
    pub text: String,
}

impl TextBlock {
    pub fn new(text: impl Into<String>) -> Self {
        TextBlock {
            kind: "text".to_string(),
            text: text.into(),
        }
    }
}

/// `{ "type": "content", "content": { ... } }` — the tool-call update shape.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ToolCallContent {
    #[serde(rename = "type")]
    pub kind: String,
    pub content: TextBlock,
}

impl ToolCallContent {
    pub fn new(text: impl Into<String>) -> Self {
        ToolCallContent {
            kind: "content".to_string(),
            content: TextBlock::new(text),
        }
    }
}

/// A prompt whose blocks could not be admitted.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum PromptBlockError {
    #[error("image block requires base64 `data` and `mimeType` strings")]
    InvalidImage,
}

/// Split ACP prompt blocks into the text and images the agent accepts.
///
/// Image, embedded-resource, and resource-link blocks are advertised in
/// `initialize`, so they must actually reach the model: dropping them
/// silently would let a client believe a pasted screenshot was accepted.
/// Embedded text resources become context the model can read.
pub fn parse_prompt_blocks(
    prompt: &[Value],
) -> Result<(String, Vec<ImageBlock>), PromptBlockError> {
    let mut texts: Vec<String> = Vec::new();
    let mut images: Vec<ImageBlock> = Vec::new();
    for block in prompt {
        let Some(object) = block.as_object() else {
            continue;
        };
        let kind = object.get("type").and_then(Value::as_str);
        match kind {
            Some("text") => {
                if let Some(text) = object.get("text").and_then(Value::as_str) {
                    texts.push(text.to_string());
                }
            }
            Some("image") => {
                let data = object.get("data").and_then(Value::as_str);
                let mime_type = object.get("mimeType").and_then(Value::as_str);
                match (data, mime_type) {
                    (Some(data), Some(mime_type)) => images.push(ImageBlock {
                        data: data.to_string(),
                        mime_type: mime_type.to_string(),
                    }),
                    _ => return Err(PromptBlockError::InvalidImage),
                }
            }
            Some("resource") => {
                let resource = object.get("resource");
                let text = resource.and_then(|r| r.get("text")).and_then(Value::as_str);
                let uri = resource.and_then(|r| r.get("uri")).and_then(Value::as_str);
                if let Some(text) = text {
                    let uri = uri.map(|uri| format!("{uri}\n")).unwrap_or_default();
                    texts.push(format!("{uri}{text}"));
                }
            }
            Some("resource_link") => {
                if let Some(uri) = object.get("uri").and_then(Value::as_str) {
                    texts.push(uri.to_string());
                }
            }
            _ => {}
        }
    }
    Ok((texts.join("\n"), images))
}

/// An image block admitted into a prompt.
#[derive(Debug, Clone, PartialEq)]
pub struct ImageBlock {
    pub data: String,
    pub mime_type: String,
}

/// The prompt content admitted into a turn.
#[derive(Debug, Clone, PartialEq)]
pub struct AdmittedPrompt {
    pub text: String,
    pub images: Vec<ImageBlock>,
}

impl AdmittedPrompt {
    pub fn parse(prompt: &[Value]) -> Result<AdmittedPrompt, PromptBlockError> {
        let (text, images) = parse_prompt_blocks(prompt)?;
        Ok(AdmittedPrompt { text, images })
    }
}

/// The `session/new`, `session/load` and `session/resume` request params
/// (`sessionId` only on the last two).
#[derive(Debug, Clone, PartialEq)]
pub struct NewSessionParams {
    pub session_id: Option<String>,
    pub cwd: Option<String>,
    pub mcp_servers: Vec<Value>,
}

impl NewSessionParams {
    /// Parse the session-start params. Unknown fields are ignored, matching
    /// the SDK's tolerance of forward-compatible params.
    pub fn parse(params: &Value) -> NewSessionParams {
        NewSessionParams {
            session_id: params
                .get("sessionId")
                .and_then(Value::as_str)
                .map(String::from),
            cwd: params.get("cwd").and_then(Value::as_str).map(String::from),
            mcp_servers: params
                .get("mcpServers")
                .and_then(Value::as_array)
                .cloned()
                .unwrap_or_default(),
        }
    }
}

/// The `session/prompt` request params.
#[derive(Debug, Clone, PartialEq)]
pub struct PromptParams {
    pub session_id: String,
    pub prompt: Vec<Value>,
}

impl PromptParams {
    pub fn parse(params: &Value) -> PromptParams {
        PromptParams {
            session_id: params
                .get("sessionId")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string(),
            prompt: params
                .get("prompt")
                .and_then(Value::as_array)
                .cloned()
                .unwrap_or_default(),
        }
    }
}

/// The `session/set_config_option` request params.
#[derive(Debug, Clone, PartialEq)]
pub struct SetConfigOptionParams {
    pub session_id: String,
    pub config_id: String,
    pub value: Value,
}

impl SetConfigOptionParams {
    /// Parse `session/set_config_option` params. The value stays raw: the
    /// handler treats a non-string value as an invalid option (the TS
    /// handler's `typeof value === "string"` gate).
    pub fn parse(params: &Value) -> SetConfigOptionParams {
        SetConfigOptionParams {
            session_id: params
                .get("sessionId")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string(),
            config_id: params
                .get("configId")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string(),
            value: params.get("value").cloned().unwrap_or(Value::Null),
        }
    }
}

/// The `_eukhe/` extension features `initialize` advertises.
pub const EUKHE_FEATURES: [&str; 7] = [
    "run_report",
    "session_info",
    "budget",
    "acceptance",
    "undo",
    "diff",
    "effects",
];

/// The version of the `_eukhe/` surface: a minor only adds.
pub const EUKHE_EXTENSIONS_VERSION: &str = "1.0";

/// The initialize result with the served capability set.
pub fn initialize_result(product_version: &str, auth_methods: Value) -> InitializeResult {
    InitializeResult {
        protocol_version: 1,
        agent_capabilities: AgentCapabilities {
            load_session: true,
            prompt_capabilities: PromptCapabilities {
                image: true,
                audio: false,
                embedded_context: true,
            },
            mcp_capabilities: McpCapabilities {
                http: true,
                sse: false,
            },
            session_capabilities: SessionCapabilities {
                close: ServedMethod::default(),
                list: ServedMethod::default(),
                resume: ServedMethod::default(),
                delete: ServedMethod::default(),
            },
            meta: serde_json::json!({ "eukhe": {
                "version": EUKHE_EXTENSIONS_VERSION,
                "features": EUKHE_FEATURES,
            }}),
        },
        auth_methods,
        agent_info: AgentInfo {
            name: "eukhe".to_string(),
            title: "Eukhe".to_string(),
            version: product_version.to_string(),
        },
        meta: super::meta::eukhe_meta(&super::meta::EukheSessionMeta::default()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn initialize_result_matches_the_served_surface() {
        let value =
            serde_json::to_value(initialize_result("9.9.9", json!([{ "id": "m" }]))).unwrap();
        assert_eq!(
            value,
            json!({
                "protocolVersion": 1,
                "agentCapabilities": {
                    "loadSession": true,
                    "promptCapabilities": { "image": true, "audio": false, "embeddedContext": true },
                    "mcpCapabilities": { "http": true, "sse": false },
                    "sessionCapabilities": { "close": {}, "list": {}, "resume": {}, "delete": {} },
                    "_meta": { "eukhe": {
                        "version": "1.0",
                        "features": ["run_report", "session_info", "budget", "acceptance", "undo", "diff", "effects"],
                    }},
                },
                "authMethods": [{ "id": "m" }],
                "agentInfo": { "name": "eukhe", "title": "Eukhe", "version": "9.9.9" },
                "_meta": { "com.eukhe": {} },
            })
        );
    }

    #[test]
    fn tool_kind_map_matches_the_ts_map() {
        assert_eq!(AcpToolKind::of_tool("python"), AcpToolKind::Execute);
        assert_eq!(AcpToolKind::of_tool("ipython"), AcpToolKind::Execute);
        assert_eq!(AcpToolKind::of_tool("bash"), AcpToolKind::Execute);
        assert_eq!(AcpToolKind::of_tool("read"), AcpToolKind::Read);
        assert_eq!(AcpToolKind::of_tool("edit"), AcpToolKind::Edit);
        assert_eq!(AcpToolKind::of_tool("write"), AcpToolKind::Edit);
        assert_eq!(AcpToolKind::of_tool("fetch"), AcpToolKind::Other);
    }

    #[test]
    fn prompt_blocks_split_text_and_images() {
        let prompt = json!([
            { "type": "text", "text": "hello" },
            { "type": "image", "data": "AAAA", "mimeType": "image/png" },
            { "type": "resource", "resource": { "uri": "file:///x", "text": "body" } },
            { "type": "resource_link", "uri": "https://example" },
            { "type": "unknown", "nonsense": true },
        ]);
        let (text, images) = parse_prompt_blocks(prompt.as_array().unwrap()).unwrap();
        assert_eq!(text, "hello\nfile:///x\nbody\nhttps://example");
        assert_eq!(
            images,
            vec![ImageBlock {
                data: "AAAA".into(),
                mime_type: "image/png".into()
            }]
        );
    }

    #[test]
    fn malformed_image_block_is_rejected() {
        let prompt = json!([{ "type": "image", "data": "AAAA" }]);
        let error = parse_prompt_blocks(prompt.as_array().unwrap()).unwrap_err();
        assert_eq!(error, PromptBlockError::InvalidImage);
    }

    #[test]
    fn config_option_update_carries_the_ts_tag_and_payload() {
        let update = AcpSessionUpdate::ConfigOptionUpdate {
            config_options: vec![super::super::config_options::SessionConfigOption {
                id: "model".to_string(),
                name: "Model".to_string(),
                kind: "select",
                category: "model".to_string(),
                current_value: r#"["faux","faux-1"]"#.to_string(),
                options: vec![super::super::config_options::SessionConfigSelectOption {
                    value: r#"["faux","faux-1"]"#.to_string(),
                    name: "Faux Model (faux)".to_string(),
                }],
            }],
        };
        let value = update.to_bare_value();
        assert_eq!(value["sessionUpdate"], "config_option_update");
        assert_eq!(value["configOptions"][0]["id"], "model");
        assert_eq!(value["configOptions"][0]["type"], "select");
        assert_eq!(
            value["configOptions"][0]["currentValue"],
            r#"["faux","faux-1"]"#
        );
        assert_eq!(
            value["configOptions"][0]["options"][0]["value"],
            r#"["faux","faux-1"]"#
        );
    }

    #[test]
    fn update_variants_carry_the_ts_tags() {
        let chunk = AcpSessionUpdate::AgentMessageChunk {
            message_id: "m1".into(),
            content: TextBlock::new("hi"),
        };
        assert_eq!(
            chunk.to_bare_value()["sessionUpdate"],
            "agent_message_chunk"
        );
        let call = AcpSessionUpdate::ToolCall(ToolCallStart {
            tool_call_id: "t1".into(),
            title: "Python cell".into(),
            name: "python".into(),
            kind: AcpToolKind::Execute,
            status: AcpToolStatus::InProgress,
            raw_input: json!({ "code": "1+1" }),
            locations: Vec::new(),
            content: Vec::new(),
        });
        assert_eq!(
            call.to_bare_value(),
            json!({
                "sessionUpdate": "tool_call",
                "toolCallId": "t1",
                "title": "Python cell",
                "name": "python",
                "kind": "execute",
                "status": "in_progress",
                "rawInput": { "code": "1+1" },
            })
        );
        assert_eq!(
            [
                AcpSessionUpdate::TitleUpdate { title: None }.method(),
                AcpSessionUpdate::SessionInfoUpdate { meta: json!({}) }.method(),
            ],
            [UpdateMethod::SessionUpdate, UpdateMethod::EukheSessionInfo]
        );
        let update = AcpSessionUpdate::ToolCallUpdate {
            tool_call_id: "t1".into(),
            status: Some(AcpToolStatus::Completed),
            content: Some(vec![ToolCallContent::new("42")]),
            meta: None,
        };
        let value = update.to_bare_value();
        assert_eq!(value["sessionUpdate"], "tool_call_update");
        assert_eq!(value["status"], "completed");
        assert_eq!(value["content"][0]["type"], "content");
        assert_eq!(value["content"][0]["content"]["text"], "42");
    }
}
