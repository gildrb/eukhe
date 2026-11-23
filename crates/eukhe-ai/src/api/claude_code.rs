//! The `claude-code` wire API: a request runs the user's own `claude` CLI
//! (`claude -p`, stream-json in and out) under the CLI's own sign-in; eukhe
//! hands it no credential. The transcript goes in as replayed frames; the
//! system prompt and eukhe's tools go through the CLI's control protocol,
//! the tools as an in-process MCP server whose calls never run, with the
//! CLI's own tools off. A tool call ends the response: eukhe runs the tool,
//! and the next request replays its result.

use std::io::ErrorKind;
use std::path::PathBuf;
use std::process::Stdio;
use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, JsonValue, Message, Model,
    ThinkingContent, ThinkingLevel, Tool, TranscriptContext, UserContent, UserContentBlock,
};
use serde_json::json;
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader, Lines};
use tokio::process::{ChildStderr, ChildStdin, ChildStdout, Command};
use tokio::sync::mpsc::{unbounded_channel, UnboundedReceiver, UnboundedSender};

use super::anthropic_messages::params::normalize_tool_call_id;
use super::anthropic_messages::{empty_output, settle, EventFold, StreamFailure};
use super::tool_result_content::sent_blocks;
use super::transform_messages::transform_messages;
use super::ProviderStreams;
use crate::types::{ProviderStreamOptions, SimpleStreamOptions, StreamOptions};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::provider_env::get_provider_env_value;
use crate::utils::transcript::{get_current_system_prompt, get_current_tools};

/// The environment variable naming the `claude` binary; unset: `claude`
/// on `PATH`.
pub const CLAUDE_BIN_ENV: &str = "EUKHE_CLAUDE_BIN";

const MCP_SERVER: &str = "eukhe";
/// The name prefix the CLI gives the tools of [`MCP_SERVER`].
const TOOL_PREFIX: &str = "mcp__eukhe__";
const INIT_REQUEST: &str = "eukhe-init";
const MCP_PROTOCOL_VERSION: &str = "2024-11-05";

const MISSING: &str = "`claude` not found on PATH or at EUKHE_CLAUDE_BIN: install it with \
                       `npm install -g @anthropic-ai/claude-code`, then sign in with `claude auth login`";
const SIGNED_OUT: &str = "`claude` is signed out: run `claude auth login`";

/// The CLI's own context (memory files, auto-memory, compaction, deferred
/// tool loading) stays out of a transcript eukhe already owns.
const CHILD_ENV: [(&str, &str); 6] = [
    ("CLAUDE_CODE_DISABLE_CLAUDE_MDS", "1"),
    ("CLAUDE_CODE_DISABLE_AUTO_MEMORY", "1"),
    ("DISABLE_AUTO_COMPACT", "1"),
    ("ENABLE_TOOL_SEARCH", "false"),
    ("DISABLE_AUTOUPDATER", "1"),
    ("CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC", "1"),
];

/// Anthropic keys of eukhe's environment stay out of the child: the CLI
/// answers on its own sign-in.
const DROPPED_ENV: [&str; 2] = ["ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN"];

/// The `claude` binary: `explicit` ([`CLAUDE_BIN_ENV`]) when set, else the
/// first `claude` on `path`; `None` when that file does not exist.
pub(crate) fn find_claude(explicit: Option<&str>, path: Option<&str>) -> Option<PathBuf> {
    match explicit {
        Some(binary) => Some(PathBuf::from(binary)).filter(|binary| binary.is_file()),
        None => std::env::split_paths(path?)
            .map(|dir| dir.join("claude"))
            .find(|candidate| candidate.is_file()),
    }
}

/// One request's input to the CLI: its arguments, the initialize request,
/// the transcript frames (one JSON line each) and eukhe's tools as MCP
/// tool entries.
struct Turn {
    args: Vec<String>,
    initialize: String,
    frames: Vec<String>,
    tools: Vec<JsonValue>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    User,
    Assistant,
}

/// Whether a user frame only joins the history or asks for the response.
#[derive(Clone, Copy)]
enum Replay {
    History,
    Query,
}

/// What one line of the CLI's output asks of the request.
enum Incoming {
    /// The CLI took the initialize request: the transcript goes next.
    Ready,
    /// A control request, answered with this line.
    Answer(String),
    /// A wire event of the response.
    Event(JsonValue),
    /// The response failed.
    Failed(Failure),
    /// Status lines, replay acknowledgements, rate-limit notes.
    Skip,
}

enum Failure {
    SignedOut,
    Cli(String),
}

/// How the CLI's output ended.
enum Completion {
    /// The response's last event arrived.
    Answered,
    /// The output closed first.
    Exited,
}

fn prepare(
    model: &Model,
    context: &TranscriptContext,
    effort: Option<&'static str>,
) -> Result<Turn, StreamFailure> {
    let messages = context.messages();
    Ok(Turn {
        args: args(&model.id, effort),
        initialize: initialize_request(&get_current_system_prompt(messages)),
        frames: frames(&conversation(model, messages))?,
        tools: get_current_tools(messages).iter().map(mcp_tool).collect(),
    })
}

fn args(model_id: &str, effort: Option<&str>) -> Vec<String> {
    let fixed = [
        "-p",
        "--input-format",
        "stream-json",
        "--output-format",
        "stream-json",
        "--verbose",
        "--include-partial-messages",
        "--tools",
        "",
        "--setting-sources",
        "",
        "--strict-mcp-config",
        "--disable-slash-commands",
        "--max-turns",
        "1",
        "--permission-mode",
        "dontAsk",
        "--no-session-persistence",
        "--model",
        model_id,
    ];
    fixed
        .into_iter()
        .chain(effort.into_iter().flat_map(|effort| ["--effort", effort]))
        .map(str::to_owned)
        .collect()
}

/// The CLI's effort level of a thinking level; `None` for a model without
/// reasoning.
fn cli_effort(model: &Model, level: ThinkingLevel) -> Option<&'static str> {
    model.reasoning.then_some(match level {
        ThinkingLevel::Minimal | ThinkingLevel::Low => "low",
        ThinkingLevel::Medium => "medium",
        ThinkingLevel::High => "high",
        ThinkingLevel::Xhigh => "xhigh",
        ThinkingLevel::Max => "max",
    })
}

fn initialize_request(system: &str) -> String {
    let mut request = json!({ "subtype": "initialize", "sdkMcpServers": [MCP_SERVER] });
    if !system.is_empty() {
        request["systemPrompt"] = json!([system]);
    }
    json!({ "type": "control_request", "request_id": INIT_REQUEST, "request": request }).to_string()
}

fn mcp_tool(tool: &Tool) -> JsonValue {
    json!({ "name": tool.name, "description": tool.description, "inputSchema": tool.parameters.json() })
}

/// The transcript without its system messages (the prompt carries them),
/// normalized for replay.
fn conversation(model: &Model, messages: &[Message]) -> Vec<Message> {
    let normalize = |id: &str, _: &Model, _: &AssistantMessage| normalize_tool_call_id(id);
    let rest: Vec<Message> = messages
        .iter()
        .filter(|message| !matches!(message, Message::System(_)))
        .cloned()
        .collect();
    transform_messages(&rest, model, Some(&normalize))
}

/// The frames of `messages`: consecutive messages of one role join one
/// frame; every user frame but the last only joins the history.
fn frames(messages: &[Message]) -> Result<Vec<String>, StreamFailure> {
    let turns = messages.iter().filter_map(blocks).fold(Vec::new(), merge);
    let last = match turns.last() {
        Some((Role::User, _)) => turns.len() - 1,
        Some((Role::Assistant, _)) | None => {
            return Err(StreamFailure::message(
                "the transcript must end with a user message or a tool result",
            ));
        }
    };
    Ok(turns
        .into_iter()
        .enumerate()
        .map(|(index, (role, content))| {
            let replay = if index == last {
                Replay::Query
            } else {
                Replay::History
            };
            frame(role, &content, replay)
        })
        .collect())
}

fn merge(
    mut turns: Vec<(Role, Vec<JsonValue>)>,
    (role, content): (Role, Vec<JsonValue>),
) -> Vec<(Role, Vec<JsonValue>)> {
    match turns.last_mut() {
        Some((last, blocks)) if *last == role => blocks.extend(content),
        Some(_) | None => turns.push((role, content)),
    }
    turns
}

fn blocks(message: &Message) -> Option<(Role, Vec<JsonValue>)> {
    let (role, content) = match message {
        Message::System(_) => return None,
        Message::User(user) => (Role::User, user_blocks(&user.content)),
        Message::Assistant(assistant) => (
            Role::Assistant,
            assistant
                .content
                .iter()
                .filter_map(assistant_block)
                .collect(),
        ),
        Message::ToolResult(result) => {
            let content: Vec<JsonValue> = sent_blocks(&result.content, result.is_error)
                .iter()
                .filter_map(|block| content_block(block))
                .collect();
            (
                Role::User,
                vec![json!({
                    "type": "tool_result",
                    "tool_use_id": result.tool_call_id,
                    "content": content,
                    "is_error": result.is_error,
                })],
            )
        }
    };
    (!content.is_empty()).then_some((role, content))
}

fn user_blocks(content: &UserContent) -> Vec<JsonValue> {
    match content {
        UserContent::Text(text) => text_block(text).into_iter().collect(),
        UserContent::Blocks(blocks) => blocks.iter().filter_map(content_block).collect(),
    }
}

fn text_block(text: &str) -> Option<JsonValue> {
    (!text.trim().is_empty()).then(|| json!({ "type": "text", "text": text }))
}

fn content_block(block: &UserContentBlock) -> Option<JsonValue> {
    match block {
        UserContentBlock::Text(text) => text_block(&text.text),
        UserContentBlock::Image(image) => Some(json!({
            "type": "image",
            "source": { "type": "base64", "media_type": image.mime_type, "data": image.data },
        })),
    }
}

fn assistant_block(block: &AssistantContentBlock) -> Option<JsonValue> {
    match block {
        AssistantContentBlock::Text(text) => text_block(&text.text),
        AssistantContentBlock::Thinking(thinking) => thinking_block(thinking),
        AssistantContentBlock::ToolCall(call) => Some(json!({
            "type": "tool_use",
            "id": call.id,
            "name": format!("{TOOL_PREFIX}{}", call.name),
            "input": call.arguments,
        })),
    }
}

/// Signed thinking replays as thinking; unsigned thinking (another
/// provider's) as text.
fn thinking_block(thinking: &ThinkingContent) -> Option<JsonValue> {
    let signature = thinking
        .thinking_signature
        .as_deref()
        .filter(|signature| !signature.trim().is_empty());
    match (thinking.redacted, signature) {
        (Some(true), Some(data)) => Some(json!({ "type": "redacted_thinking", "data": data })),
        (Some(true), None) => None,
        (Some(false) | None, Some(signature)) => Some(json!({
            "type": "thinking", "thinking": thinking.thinking, "signature": signature,
        })),
        (Some(false) | None, None) => text_block(&thinking.thinking),
    }
}

fn frame(role: Role, content: &[JsonValue], replay: Replay) -> String {
    match (role, replay) {
        (Role::User, Replay::Query) => json!({
            "type": "user",
            "message": { "role": "user", "content": content },
            "parent_tool_use_id": null,
        }),
        (Role::User, Replay::History) => json!({
            "type": "user",
            "message": { "role": "user", "content": content },
            "parent_tool_use_id": null,
            "shouldQuery": false,
        }),
        (Role::Assistant, Replay::History | Replay::Query) => json!({
            "type": "assistant",
            "message": { "role": "assistant", "content": content },
            "parent_tool_use_id": null,
        }),
    }
    .to_string()
}

fn classify(line: &str, tools: &[JsonValue]) -> Incoming {
    let Ok(value) = serde_json::from_str::<JsonValue>(line) else {
        return Incoming::Failed(Failure::Cli(format!("unexpected output: {line}")));
    };
    match value["type"].as_str() {
        Some("control_response") => initialized(&value["response"]),
        Some("control_request") => Incoming::Answer(answer(&value, tools)),
        Some("stream_event") => Incoming::Event(without_tool_prefix(value["event"].clone())),
        Some("assistant") => assistant_error(&value),
        Some("result") => result_outcome(&value),
        _ => Incoming::Skip,
    }
}

fn initialized(response: &JsonValue) -> Incoming {
    match (
        response["request_id"].as_str(),
        response["subtype"].as_str(),
    ) {
        (Some(INIT_REQUEST), Some("success")) => Incoming::Ready,
        (Some(INIT_REQUEST), _) => Incoming::Failed(Failure::Cli(format!(
            "initialize refused: {}",
            response["error"]
        ))),
        _ => Incoming::Skip,
    }
}

fn answer(request: &JsonValue, tools: &[JsonValue]) -> String {
    let id = &request["request_id"];
    let body = &request["request"];
    let response = match body["subtype"].as_str() {
        Some("mcp_message") => json!({
            "subtype": "success",
            "request_id": id,
            "response": { "mcp_response": mcp_response(&body["message"], tools) },
        }),
        _ => json!({
            "subtype": "error",
            "request_id": id,
            "error": format!("eukhe does not handle control request {}", body["subtype"]),
        }),
    };
    json!({ "type": "control_response", "response": response }).to_string()
}

/// The MCP server's answer to `message`. A tool call never runs here: the
/// response ends at the call, and eukhe runs it.
fn mcp_response(message: &JsonValue, tools: &[JsonValue]) -> JsonValue {
    let id = &message["id"];
    if id.is_null() {
        // A notification: the CLI takes an empty acknowledgement.
        return json!({ "jsonrpc": "2.0", "id": 0, "result": {} });
    }
    match message["method"].as_str() {
        Some("initialize") => json!({ "jsonrpc": "2.0", "id": id, "result": {
            "protocolVersion": message["params"]["protocolVersion"]
                .as_str()
                .unwrap_or(MCP_PROTOCOL_VERSION),
            "capabilities": { "tools": {} },
            "serverInfo": { "name": MCP_SERVER, "version": env!("CARGO_PKG_VERSION") },
        } }),
        Some("tools/list") => json!({ "jsonrpc": "2.0", "id": id, "result": { "tools": tools } }),
        Some("tools/call") => json!({ "jsonrpc": "2.0", "id": id, "result": {
            "isError": true,
            "content": [{ "type": "text", "text": "eukhe runs this tool itself" }],
        } }),
        _ => {
            json!({ "jsonrpc": "2.0", "id": id, "error": { "code": -32601, "message": "Method not found" } })
        }
    }
}

/// `event` with eukhe's tool names as eukhe knows them.
fn without_tool_prefix(mut event: JsonValue) -> JsonValue {
    if let Some(name) = event.pointer_mut("/content_block/name") {
        if let Some(stripped) = name
            .as_str()
            .and_then(|name| name.strip_prefix(TOOL_PREFIX))
        {
            *name = JsonValue::String(stripped.to_owned());
        }
    }
    event
}

fn assistant_error(value: &JsonValue) -> Incoming {
    match value["error"].as_str() {
        None => Incoming::Skip,
        Some("authentication_failed") => Incoming::Failed(Failure::SignedOut),
        Some(kind) => Incoming::Failed(Failure::Cli(
            message_text(&value["message"]["content"]).unwrap_or_else(|| kind.to_owned()),
        )),
    }
}

fn message_text(content: &JsonValue) -> Option<String> {
    let text: Vec<&str> = content
        .as_array()?
        .iter()
        .filter_map(|block| block["text"].as_str())
        .collect();
    (!text.is_empty()).then(|| text.join("\n"))
}

fn result_outcome(value: &JsonValue) -> Incoming {
    match (value["is_error"].as_bool(), value["num_turns"].as_u64()) {
        (Some(true), _) => Incoming::Failed(Failure::Cli(
            value["result"]
                .as_str()
                .filter(|text| !text.is_empty())
                .or_else(|| value["subtype"].as_str())
                .unwrap_or("the request failed")
                .to_owned(),
        )),
        // The acknowledgement of a frame that only joined the history.
        (Some(false) | None, Some(0)) => Incoming::Skip,
        (Some(false) | None, Some(_) | None) => Incoming::Failed(Failure::Cli(
            "the response ended before its last event".to_owned(),
        )),
    }
}

fn spawn_failure(error: &std::io::Error) -> StreamFailure {
    match error.kind() {
        ErrorKind::NotFound => StreamFailure::message(MISSING),
        _ => StreamFailure::message(format!("starting `claude` failed: {error}")),
    }
}

async fn aborted(signal: Option<&AbortSignal>) {
    match signal {
        Some(signal) => {
            signal.cancelled().await;
        }
        None => std::future::pending().await,
    }
}

async fn write_lines(mut stdin: ChildStdin, mut lines: UnboundedReceiver<String>) {
    while let Some(line) = lines.recv().await {
        let written = async {
            stdin.write_all(line.as_bytes()).await?;
            stdin.write_all(b"\n").await?;
            stdin.flush().await
        }
        .await;
        if let Err(error) = written {
            // The reader sees the CLI's exit and reports it.
            tracing::debug!(%error, "writing to claude failed");
            return;
        }
    }
}

async fn stderr_text(mut stderr: ChildStderr) -> String {
    let mut bytes = Vec::new();
    match stderr.read_to_end(&mut bytes).await {
        Ok(_) => String::from_utf8_lossy(&bytes).trim().to_owned(),
        Err(error) => format!("(stderr unreadable: {error})"),
    }
}

fn send(to_cli: &UnboundedSender<String>, line: String) -> Result<(), StreamFailure> {
    to_cli
        .send(line)
        .map_err(|_| StreamFailure::message("`claude` stopped reading its input"))
}

/// Runs the protocol over the CLI's pipes until the response ends.
async fn converse(
    model: &Model,
    turn: &Turn,
    signal: Option<&AbortSignal>,
    mut lines: Lines<BufReader<ChildStdout>>,
    to_cli: &UnboundedSender<String>,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
) -> Result<Completion, StreamFailure> {
    send(to_cli, turn.initialize.clone())?;
    stream.push_partial(output, |partial| AssistantMessageEvent::Start { partial });
    let mut fold = EventFold::new(model, output);
    loop {
        let line = tokio::select! {
            () = aborted(signal) => return Err(StreamFailure::message("Request was aborted")),
            line = lines.next_line() => line.map_err(|error| {
                StreamFailure::message(format!("reading `claude` output failed: {error}"))
            })?,
        };
        let Some(line) = line else {
            return Ok(Completion::Exited);
        };
        match classify(&line, &turn.tools) {
            Incoming::Ready => {
                for frame in &turn.frames {
                    send(to_cli, frame.clone())?;
                }
            }
            Incoming::Answer(reply) => send(to_cli, reply)?,
            Incoming::Event(event) => {
                fold.push(&event, stream)?;
                if event["type"] == "message_stop" {
                    fold.finish(None)?;
                    return Ok(Completion::Answered);
                }
            }
            Incoming::Failed(Failure::SignedOut) => {
                return Err(StreamFailure::message(SIGNED_OUT));
            }
            Incoming::Failed(Failure::Cli(text)) => {
                return Err(StreamFailure::message(format!("claude: {text}")));
            }
            Incoming::Skip => {}
        }
    }
}

async fn run(
    model: &Model,
    turn: Turn,
    options: &StreamOptions,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
) -> Result<(), StreamFailure> {
    let env = options.request.env.as_ref();
    let binary = find_claude(
        get_provider_env_value(CLAUDE_BIN_ENV, env).as_deref(),
        get_provider_env_value("PATH", env).as_deref(),
    )
    .ok_or_else(|| StreamFailure::message(MISSING))?;
    let mut command = Command::new(&binary);
    command
        .args(&turn.args)
        .envs(CHILD_ENV)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true);
    for name in DROPPED_ENV {
        command.env_remove(name);
    }
    let mut child = command.spawn().map_err(|error| spawn_failure(&error))?;
    let (Some(stdin), Some(stdout), Some(stderr)) =
        (child.stdin.take(), child.stdout.take(), child.stderr.take())
    else {
        return Err(StreamFailure::message("`claude` started without its pipes"));
    };
    let stderr = tokio::spawn(stderr_text(stderr));
    let (to_cli, from_eukhe) = unbounded_channel();
    tokio::spawn(write_lines(stdin, from_eukhe));
    let completion = converse(
        model,
        &turn,
        options.request.signal.as_ref(),
        BufReader::new(stdout).lines(),
        &to_cli,
        output,
        stream,
    )
    .await;
    drop(to_cli);
    // The response is over: whatever the CLI would do next is not wanted.
    child
        .kill()
        .await
        .map_err(|error| StreamFailure::message(format!("stopping `claude` failed: {error}")))?;
    match completion? {
        Completion::Answered => Ok(()),
        Completion::Exited => {
            let detail = stderr
                .await
                .unwrap_or_else(|error| format!("(stderr reader failed: {error})"));
            Err(StreamFailure::message(format!(
                "`claude` exited before the response ended: {detail}"
            )))
        }
    }
}

fn stream_turn(
    model: &Model,
    context: &TranscriptContext,
    options: StreamOptions,
    effort: Option<&'static str>,
) -> AssistantMessageEventStream {
    let stream = AssistantMessageEventStream::new();
    let target = stream.clone();
    let turn = prepare(model, context, effort);
    let model = model.clone();
    tokio::spawn(async move {
        let mut output = empty_output(&model);
        let result = match turn {
            Ok(turn) => run(&model, turn, &options, &mut output, &target).await,
            Err(failure) => Err(failure),
        };
        settle(
            &model,
            output,
            result,
            options.request.signal.as_ref(),
            &target,
        );
    });
    stream
}

/// TS-contract `stream`: the CLI's default effort.
#[must_use]
pub fn stream(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    stream_turn(model, context, options.stream, None)
}

/// TS-contract `streamSimple`: the thinking level as the CLI's effort.
#[must_use]
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    let effort = options.reasoning.and_then(|level| cli_effort(model, level));
    stream_turn(model, context, options.stream, effort)
}

/// The `claude-code` module (no deferred responses).
#[must_use]
pub fn streams() -> ProviderStreams {
    ProviderStreams {
        stream: Arc::new(stream),
        stream_simple: Arc::new(stream_simple),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}
