//! The turn loop on the chat memory (`OptChat` §7): every delivery path
//! admits a fresh call (the view plus the queued texts as ONE user
//! message), except mid-run steering into the call cut for it; and what
//! the chat log keeps of reports and harness nudges (§9).

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use eukhe_agent::scripted::ScriptedProvider;
use eukhe_agent::types::{Message, UserContent, UserPart};
use serde_json::json;

use super::{cap_tool_results, custom_entries, log_entries};
use crate::memory::{cap_text, Kind, Memory, MemoryRole, Summarizer, SummarizerFuture, CAP};
use crate::session_engine::engine::{create_session, SessionEngine, SessionEngineConfig};
use crate::session_engine::tool_bridge::bridge_tool;
use crate::session_engine::{PromptOptions, StreamingBehavior, TrailingAssistantFilter};
use crate::tools::tool_definition::{ExecutionMode, ToolDefinition, ToolExecutionResult};

/// A compactor that answers at once (short messages never reach it).
struct InstantSummarizer;

impl Summarizer for InstantSummarizer {
    fn complete(&self, _context: eukhe_types::ai::Context) -> SummarizerFuture {
        Box::pin(async {
            Ok(serde_json::from_value(json!({
                "content": [{ "type": "text", "text": "a summary" }],
                "api": "test",
                "provider": "test",
                "model": "m",
                "usage": eukhe_types::ai::Usage::default(),
                "stopReason": "stop",
                "timestamp": 0
            }))?)
        })
    }
}

fn model() -> eukhe_agent::types::Model {
    eukhe_agent::types::Model {
        id: "m".into(),
        name: "m".into(),
        api: "test".into(),
        provider: "test".into(),
        base_url: "http://localhost".into(),
        reasoning: false,
        cost: eukhe_agent::types::UsageCost::default(),
        context_window: 100_000,
        max_tokens: 100,
    }
}

/// A tool that signals its start, then runs until `release` (or the
/// turn's abort).
fn gate_tool(
    started: Arc<tokio::sync::Notify>,
    release: Arc<tokio::sync::Notify>,
) -> ToolDefinition {
    ToolDefinition {
        name: "wait".to_string(),
        label: "Wait".to_string(),
        description: "Waits".to_string(),
        prompt_snippet: String::new(),
        parameters: json!({ "type": "object", "properties": {} }),
        execution_mode: Some(ExecutionMode::Sequential),
        prepare_arguments: None,
        execute: Arc::new(move |_id, _params, signal, _on_update| {
            let started = Arc::clone(&started);
            let release = Arc::clone(&release);
            Box::pin(async move {
                started.notify_one();
                match signal {
                    Some(signal) => tokio::select! {
                        () = signal.cancelled() => {}
                        () = release.notified() => {}
                    },
                    None => release.notified().await,
                }
                Ok(ToolExecutionResult::text("waited"))
            })
        }),
    }
}

struct Chat {
    engine: Arc<SessionEngine>,
    memory: Memory,
    provider: Arc<ScriptedProvider>,
    _tmp: tempfile::TempDir,
}

async fn chat(
    tools: Vec<ToolDefinition>,
    queued_steering_probe: Option<Arc<dyn Fn() -> bool + Send + Sync>>,
) -> Chat {
    chat_as(MemoryRole::Root, tools, queued_steering_probe).await
}

/// A session on a fresh chat: the root, or a subagent of it.
async fn chat_as(
    role: MemoryRole,
    tools: Vec<ToolDefinition>,
    queued_steering_probe: Option<Arc<dyn Fn() -> bool + Send + Sync>>,
) -> Chat {
    let provider = Arc::new(ScriptedProvider::new(model()));
    let tmp = tempfile::tempdir().unwrap();
    let cwd = tmp.path().join("project");
    let agent_dir = tmp.path().join("agent");
    std::fs::create_dir_all(&cwd).unwrap();
    let memory = Memory::open(agent_dir.join("chat"), Arc::new(InstantSummarizer))
        .await
        .unwrap();
    let engine = create_session(SessionEngineConfig {
        memory: Some(memory.clone()),
        queued_steering_probe,
        cwd,
        agent_dir,
        model: Some(model()),
        stream_fn: Some(provider.stream_fn()),
        tools: tools.into_iter().map(bridge_tool).collect(),
        conversation_log_path: Some(tmp.path().join("sessions").join("root.jsonl")),
        rlm_depth: match role {
            MemoryRole::Root => None,
            MemoryRole::Subagent => Some(1),
        },
        ..Default::default()
    })
    .await
    .unwrap();
    Chat {
        engine: Arc::new(engine),
        memory,
        provider,
        _tmp: tmp,
    }
}

/// The request's messages as (role, texts): the view pieces collapse to
/// `<view>` so the shape reads at a glance.
fn shape(messages: &[Message]) -> Vec<(&'static str, Vec<String>)> {
    messages
        .iter()
        .map(|message| match message {
            Message::User(user) => (
                "user",
                match &user.content {
                    UserContent::Text(text) => vec![text.clone()],
                    UserContent::Parts(parts) => parts
                        .iter()
                        .map(|part| match part {
                            UserPart::Text(text) if text.text.starts_with("<chat>") => {
                                "<view>".to_string()
                            }
                            UserPart::Text(text) => text.text.clone(),
                            UserPart::Image(_) => "<image>".to_string(),
                        })
                        .collect(),
                },
            ),
            Message::Assistant(_) => ("assistant", Vec::new()),
            Message::ToolResult(_) => ("toolResult", Vec::new()),
        })
        .collect()
}

fn last_request(chat: &Chat) -> Vec<(&'static str, Vec<String>)> {
    shape(&chat.provider.calls().last().expect("a request").messages)
}

/// Every message of the chat log, as `kind: text`.
async fn chat_log(memory: &Memory) -> Vec<String> {
    let count = memory.status().await.unwrap().messages;
    let mut log = Vec::new();
    for id in 0..count {
        let line = memory.zoom(id, 1).await.unwrap();
        let (_, entry) = line.split_once('|').expect("id+0|kind: text");
        log.push(entry.to_string());
    }
    log
}

fn fresh_request(text: &str) -> Vec<(&'static str, Vec<String>)> {
    vec![("user", vec!["<view>".to_string(), text.to_string()])]
}

/// The user stops the agent during a tool (Esc): the call ended, so the
/// next message is a fresh call with the view and the new text only.
#[tokio::test(flavor = "multi_thread")]
async fn a_message_after_an_abort_during_a_tool_starts_a_fresh_call() {
    let started = Arc::new(tokio::sync::Notify::new());
    let release = Arc::new(tokio::sync::Notify::new());
    let chat = chat(
        vec![gate_tool(Arc::clone(&started), Arc::clone(&release))],
        None,
    )
    .await;
    chat.provider
        .push_tool_call_turn(None, vec![("call-1", "wait", json!({}))]);
    chat.provider.push_text_turn("second answer");

    let engine = Arc::clone(&chat.engine);
    let run = tokio::spawn(async move {
        engine
            .prompt("first", PromptOptions::default())
            .await
            .unwrap();
    });
    started.notified().await;
    chat.engine.session.agent().abort();
    run.await.unwrap();
    chat.engine.session.agent().wait_for_idle().await;

    chat.engine
        .prompt("second", PromptOptions::default())
        .await
        .unwrap();
    chat.engine.session.agent().wait_for_idle().await;
    assert_eq!(last_request(&chat), fresh_request("second"));
}

/// A run that ended in an error (here: its failed reply already dropped,
/// as a retry re-issue does before the user gives up on it) leaves no
/// call to continue: the next message is a fresh call.
#[tokio::test(flavor = "multi_thread")]
async fn a_message_after_an_error_ended_run_starts_a_fresh_call() {
    let started = Arc::new(tokio::sync::Notify::new());
    let release = Arc::new(tokio::sync::Notify::new());
    let chat = chat(
        vec![gate_tool(Arc::clone(&started), Arc::clone(&release))],
        None,
    )
    .await;
    chat.provider
        .push_tool_call_turn(None, vec![("call-1", "wait", json!({}))]);
    chat.provider.push_stream_failure_turn("", "overloaded");
    chat.provider.push_text_turn("second answer");

    let engine = Arc::clone(&chat.engine);
    let run = tokio::spawn(async move {
        engine
            .prompt("first", PromptOptions::default())
            .await
            .unwrap();
    });
    started.notified().await;
    release.notify_one();
    run.await.unwrap();
    chat.engine.session.agent().wait_for_idle().await;
    chat.engine
        .session
        .drop_trailing_assistant(TrailingAssistantFilter::Any)
        .await;

    chat.engine
        .prompt("second", PromptOptions::default())
        .await
        .unwrap();
    chat.engine.session.agent().wait_for_idle().await;
    assert_eq!(last_request(&chat), fresh_request("second"));
}

/// Follow-ups queued while the agent works are taken all at once when its
/// call ends: ONE fresh call whose user message is the view, then the
/// texts joined by a blank line; each text is logged as the user's.
#[tokio::test(flavor = "multi_thread")]
async fn queued_follow_ups_start_one_fresh_call_together() {
    let started = Arc::new(tokio::sync::Notify::new());
    let release = Arc::new(tokio::sync::Notify::new());
    let chat = chat(
        vec![gate_tool(Arc::clone(&started), Arc::clone(&release))],
        None,
    )
    .await;
    chat.provider
        .push_tool_call_turn(None, vec![("call-1", "wait", json!({}))]);
    chat.provider.push_text_turn("first answer");
    chat.provider.push_text_turn("answer to both");

    let engine = Arc::clone(&chat.engine);
    let run = tokio::spawn(async move {
        engine
            .prompt("first", PromptOptions::default())
            .await
            .unwrap();
    });
    started.notified().await;
    for text in ["a", "b"] {
        let follow_up = PromptOptions {
            streaming_behavior: Some(StreamingBehavior::FollowUp),
            ..Default::default()
        };
        chat.engine.prompt(text, follow_up).await.unwrap();
    }
    release.notify_one();
    run.await.unwrap();
    chat.engine.session.agent().wait_for_idle().await;

    assert_eq!(chat.provider.calls().len(), 3);
    assert_eq!(last_request(&chat), fresh_request("a\n\nb"));
    let log = chat_log(&chat.memory).await;
    let users: Vec<&str> = log
        .iter()
        .filter_map(|entry| entry.strip_prefix("user: "))
        .collect();
    assert_eq!(users, ["first", "a", "b"]);
}

/// The host queue pumps (the RPC `kick_queue_pump`) deliver a message
/// queued while idle through the same admission: a fresh call.
#[tokio::test(flavor = "multi_thread")]
async fn a_queued_message_delivered_at_idle_starts_a_fresh_call() {
    let chat = chat(Vec::new(), None).await;
    chat.provider.push_text_turn("first answer");
    chat.provider.push_text_turn("queued answer");
    chat.engine
        .prompt("first", PromptOptions::default())
        .await
        .unwrap();
    chat.engine.session.agent().wait_for_idle().await;

    chat.engine
        .session
        .agent()
        .follow_up(crate::session_engine::user_prompt_message("queued", &[]));
    chat.engine.session.deliver_queued().await.unwrap();
    chat.engine.session.agent().wait_for_idle().await;
    assert_eq!(last_request(&chat), fresh_request("queued"));
}

/// The one call that goes on across runs: the run the queued-steering
/// probe cut at a tool boundary continues with the steering it stopped
/// for, on the same view.
#[tokio::test(flavor = "multi_thread")]
async fn steering_continues_the_call_cut_for_it() {
    let started = Arc::new(tokio::sync::Notify::new());
    let release = Arc::new(tokio::sync::Notify::new());
    let steering_queued = Arc::new(AtomicBool::new(false));
    let probe = {
        let steering_queued = Arc::clone(&steering_queued);
        Arc::new(move || steering_queued.load(Ordering::SeqCst))
            as Arc<dyn Fn() -> bool + Send + Sync>
    };
    let chat = chat(
        vec![gate_tool(Arc::clone(&started), Arc::clone(&release))],
        Some(probe),
    )
    .await;
    chat.provider
        .push_tool_call_turn(None, vec![("call-1", "wait", json!({}))]);
    chat.provider.push_text_turn("steered answer");

    let engine = Arc::clone(&chat.engine);
    let run = tokio::spawn(async move {
        engine
            .prompt("first", PromptOptions::default())
            .await
            .unwrap();
    });
    started.notified().await;
    steering_queued.store(true, Ordering::SeqCst);
    release.notify_one();
    run.await.unwrap();
    chat.engine.session.agent().wait_for_idle().await;
    assert_eq!(chat.provider.calls().len(), 1, "the probe cut the run");
    steering_queued.store(false, Ordering::SeqCst);

    chat.engine
        .prompt("steer", PromptOptions::default())
        .await
        .unwrap();
    chat.engine.session.agent().wait_for_idle().await;
    assert_eq!(
        last_request(&chat),
        vec![
            ("user", vec!["<view>".to_string(), "first".to_string()]),
            ("assistant", Vec::new()),
            ("toolResult", Vec::new()),
            ("user", vec!["steer".to_string()]),
        ]
    );
}

/// A host turn that may re-issue a failed run (auto-retry, overflow
/// compact-and-retry) keeps the chat's turn: another window waiting for it
/// gets it only when the host's turn is over, never between the failed run
/// and its retry.
#[tokio::test(flavor = "multi_thread")]
async fn a_host_turn_keeps_the_chat_turn_across_a_failed_run() {
    let chat = chat(Vec::new(), None).await;
    chat.provider.push_stream_failure_turn("", "overloaded");
    let hold = chat
        .engine
        .session
        .chat_memory()
        .expect("a chat-memory session")
        .hold_turn();
    chat.engine
        .prompt("first", PromptOptions::default())
        .await
        .unwrap();
    chat.engine.session.agent().wait_for_idle().await;

    let other_window = chat.memory.clone();
    let mut waiting = tokio::spawn(async move { other_window.acquire_turn().await });
    // The absence of a grant can only be observed over a window of time.
    assert!(
        tokio::time::timeout(std::time::Duration::from_millis(500), &mut waiting)
            .await
            .is_err(),
        "the failed run's end kept the turn for its retry"
    );
    drop(hold);
    let lease = waiting.await.unwrap().unwrap();
    lease.release().await.unwrap();
}

/// `/compact` between calls has nothing to compact: the next turn starts
/// fresh from the view, so the request is refused, not summarized.
#[tokio::test(flavor = "multi_thread")]
async fn compact_between_calls_is_refused() {
    let chat = chat(Vec::new(), None).await;
    chat.provider.push_text_turn("first answer");
    chat.engine
        .prompt("first", PromptOptions::default())
        .await
        .unwrap();
    chat.engine.session.agent().wait_for_idle().await;
    let model: eukhe_types::ai::Model = serde_json::from_value(json!({
        "id": "m", "name": "m", "api": "test", "provider": "test",
        "baseUrl": "http://localhost", "reasoning": false, "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 100_000, "maxTokens": 100
    }))
    .unwrap();
    let outcome = chat
        .engine
        .session
        .compact_on_request(None, &model, None, None)
        .await
        .unwrap();
    assert_eq!(
        outcome,
        crate::session_engine::compact_session::CompactOutcome::Skipped(
            crate::session_engine::compact_session::CompactSkip::ChatMemory.user_message()
        )
    );
    assert_eq!(chat.provider.calls().len(), 1, "no summarizer call");
}

/// Reports reach the chat as ONE leading `[id] ` and the report (§9): the
/// child's delivered header becomes `[child:NAME]`, background events
/// get their own short ids.
#[test]
fn reports_are_logged_with_one_leading_id() {
    let logged = |custom_type: &str, content: &str| {
        custom_entries(
            "custom",
            &json!({ "customType": custom_type, "content": content }),
        )
    };
    assert_eq!(
        [
            logged("agent_message", "[agent-message from child:x]\n\nthe body"),
            logged("rlm_child_failure", "[child-failed child:x]\n\nboom"),
            logged(
                "rlm_child_terminal_notice",
                "[child-exited: no-reply child:x]\n\nLast assistant text: done"
            ),
            logged("heartbeat_prompt", "[heartbeat: daily run#3]\n\ncheck mail"),
            logged(
                "async_bash_completion",
                "[bash-done pid:7 exit:0]\n\nCommand: \"make\""
            ),
            logged("something_new", "plain words"),
        ],
        [
            vec![(Kind::User, "[child:x] the body".to_string())],
            vec![(Kind::User, "[child:x] failed\nboom".to_string())],
            vec![(
                Kind::User,
                "[child:x] exited (no-reply)\nLast assistant text: done".to_string()
            )],
            vec![(
                Kind::User,
                "[heartbeat] daily run#3\ncheck mail".to_string()
            )],
            vec![(
                Kind::User,
                "[bash] done pid:7 exit:0\nCommand: \"make\"".to_string()
            )],
            vec![(Kind::User, "[something_new] plain words".to_string())],
        ]
    );
}

/// Harness nudges are not the user's words: autonomous and goal
/// continuations reach the model but never the chat log.
#[test]
fn harness_nudges_are_not_logged() {
    let autonomous = crate::autonomous::autonomous_continuation_loop_row(
        "[autonomous-continuation]\n\nKeep going.",
        0,
    );
    let goal = custom_entries(
        "custom",
        &json!({
            "customType": "goal_context",
            "content": "[goal: continuation]\n\nContinue the goal."
        }),
    );
    assert_eq!((log_entries(&autonomous), goal), (Vec::new(), Vec::new()));
}

/// A tool that echoes its `text`.
fn echo_tool() -> ToolDefinition {
    ToolDefinition {
        name: "echo".to_string(),
        label: "Echo".to_string(),
        description: "Echoes its input".to_string(),
        prompt_snippet: String::new(),
        parameters: json!({
            "type": "object",
            "properties": { "text": { "type": "string" } },
            "required": ["text"]
        }),
        execution_mode: Some(ExecutionMode::Sequential),
        prepare_arguments: None,
        execute: Arc::new(|_id, params, _signal, _on_update| {
            let text = params
                .get("text")
                .and_then(serde_json::Value::as_str)
                .unwrap_or_default()
                .to_string();
            Box::pin(async move { Ok(ToolExecutionResult::text(format!("echo: {text}"))) })
        }),
    }
}

/// The view a request starts with: the first message's parts up to the one
/// that closes `</chat>`, joined.
fn view_text(messages: &[Message]) -> String {
    let Some(Message::User(user)) = messages.first() else {
        panic!("a request starts with the user message holding the view");
    };
    let UserContent::Parts(parts) = &user.content else {
        panic!("the view is cut into parts");
    };
    let mut view = String::new();
    for part in parts {
        let UserPart::Text(text) = part else {
            panic!("the view holds text only");
        };
        view.push_str(&text.text);
        if text.text.ends_with("</chat>") {
            return view;
        }
    }
    panic!("the view never closed: {view}");
}

/// Every call starts from the view; a call's later steps resend it byte
/// for byte; a fresh call's view summarizes everything before it; and
/// everything the agent says and does is logged as it happens.
#[tokio::test(flavor = "multi_thread")]
async fn root_calls_start_from_the_view_and_log_everything() {
    let chat = chat(vec![echo_tool()], None).await;
    chat.provider
        .push_tool_call_turn(None, vec![("call-1", "echo", json!({ "text": "hi" }))]);
    chat.provider.push_text_turn("done one");
    chat.provider.push_text_turn("done two");
    for text in ["first", "second"] {
        chat.engine
            .prompt(text, PromptOptions::default())
            .await
            .unwrap();
        chat.engine.session.agent().wait_for_idle().await;
    }

    let calls = chat.provider.calls();
    assert_eq!(calls.len(), 3);
    let memory_tools: Vec<&str> = calls[0]
        .tools
        .iter()
        .map(|tool| tool.name.as_str())
        .filter(|name| ["zoom", "date"].contains(name))
        .collect();
    assert_eq!(memory_tools, ["zoom", "date"]);
    assert_eq!(view_text(&calls[0].messages), "<chat>\n</chat>");
    assert_eq!(calls[1].messages[0], calls[0].messages[0]);
    assert_eq!(
        shape(&calls[1].messages),
        [
            ("user", vec!["<view>".to_string(), "first".to_string()]),
            ("assistant", Vec::new()),
            ("toolResult", Vec::new()),
        ]
    );
    assert_eq!(
        (view_text(&calls[2].messages), shape(&calls[2].messages)),
        (
            "<chat>\n0+1|user: first\n1+1|tool: echo {\"text\":\"hi\"}\n2+1|echo: echo: hi\n3+1|talk: done one\n</chat>".to_string(),
            fresh_request("second")
        )
    );
    assert_eq!(
        chat_log(&chat.memory).await,
        [
            "user: first",
            "tool: echo {\"text\":\"hi\"}",
            "echo: echo: hi",
            "talk: done one",
            "user: second",
            "talk: done two",
        ]
    );
}

/// A message delivered at a tool boundary into the running call is logged
/// as the user's, between the call's steps.
#[tokio::test(flavor = "multi_thread")]
async fn steering_is_logged_between_the_steps_of_its_call() {
    let started = Arc::new(tokio::sync::Notify::new());
    let release = Arc::new(tokio::sync::Notify::new());
    let steering_queued = Arc::new(AtomicBool::new(false));
    let probe = {
        let steering_queued = Arc::clone(&steering_queued);
        Arc::new(move || steering_queued.load(Ordering::SeqCst))
            as Arc<dyn Fn() -> bool + Send + Sync>
    };
    let chat = chat(
        vec![gate_tool(Arc::clone(&started), Arc::clone(&release))],
        Some(probe),
    )
    .await;
    chat.provider
        .push_tool_call_turn(None, vec![("call-1", "wait", json!({}))]);
    chat.provider.push_text_turn("steered answer");

    let engine = Arc::clone(&chat.engine);
    let run = tokio::spawn(async move {
        engine
            .prompt("first", PromptOptions::default())
            .await
            .unwrap();
    });
    started.notified().await;
    steering_queued.store(true, Ordering::SeqCst);
    release.notify_one();
    run.await.unwrap();
    chat.engine.session.agent().wait_for_idle().await;
    steering_queued.store(false, Ordering::SeqCst);
    chat.engine
        .prompt("steer", PromptOptions::default())
        .await
        .unwrap();
    chat.engine.session.agent().wait_for_idle().await;

    assert_eq!(
        chat_log(&chat.memory).await,
        [
            "user: first",
            "tool: wait {}",
            "echo: waited",
            "user: steer",
            "talk: steered answer",
        ]
    );
}

/// A subagent starts from the view at its spawn, keeps its conversation
/// under that same view, and logs nothing to the chat (§9).
#[tokio::test(flavor = "multi_thread")]
async fn a_subagent_keeps_its_first_view_and_logs_nothing() {
    let chat = chat_as(MemoryRole::Subagent, Vec::new(), None).await;
    chat.memory
        .append(Kind::User, "root context")
        .await
        .unwrap();
    chat.provider.push_text_turn("one");
    chat.provider.push_text_turn("two");
    chat.engine
        .prompt("task", PromptOptions::default())
        .await
        .unwrap();
    chat.engine.session.agent().wait_for_idle().await;
    chat.memory
        .append(Kind::User, "later root message")
        .await
        .unwrap();
    chat.engine
        .prompt("more", PromptOptions::default())
        .await
        .unwrap();
    chat.engine.session.agent().wait_for_idle().await;

    let calls = chat.provider.calls();
    assert_eq!(
        view_text(&calls[0].messages),
        "<chat>\n0+1|user: root context\n</chat>"
    );
    assert_eq!(calls[1].messages[0], calls[0].messages[0]);
    assert_eq!(
        shape(&calls[1].messages),
        [
            ("user", vec!["<view>".to_string(), "task".to_string()]),
            ("assistant", Vec::new()),
            ("user", vec!["more".to_string()]),
        ]
    );
    assert_eq!(
        chat_log(&chat.memory).await,
        ["user: root context", "user: later root message"]
    );
}

fn assistant_message() -> eukhe_agent::types::AssistantMessage {
    serde_json::from_value(json!({
        "content": [],
        "usage": eukhe_agent::types::Usage::zero(),
        "stopReason": "stop"
    }))
    .unwrap()
}

/// The agent's replies are `talk`, its tool calls `tool` (name and JSON
/// input), tool results `echo` (capped); thinking is never logged (§2).
#[test]
fn log_entries_follow_the_message_kinds() {
    let assistant = eukhe_agent::types::AgentMessage::Standard(Message::Assistant(
        eukhe_agent::types::AssistantMessage {
            content: vec![
                eukhe_agent::types::AssistantContent::Thinking(
                    eukhe_agent::types::ThinkingContent {
                        thinking: "secret".into(),
                        thinking_signature: None,
                        redacted: None,
                    },
                ),
                eukhe_agent::types::AssistantContent::Text(eukhe_agent::types::TextContent {
                    text: "let me look".into(),
                    text_signature: None,
                    cache_breakpoint: None,
                }),
                eukhe_agent::types::AssistantContent::ToolCall(eukhe_agent::types::ToolCall {
                    id: "1".into(),
                    name: "ipython".into(),
                    arguments: json!({ "code": "1+1" }),
                    thought_signature: None,
                }),
            ],
            ..assistant_message()
        },
    ));
    let long = "z".repeat(CAP + 10);
    let result = eukhe_agent::types::AgentMessage::Standard(Message::ToolResult(
        eukhe_agent::types::ToolResultMessage {
            tool_call_id: "1".into(),
            tool_name: "ipython".into(),
            content: vec![eukhe_agent::types::ToolResultContent::text(long.clone())],
            details: None,
            is_error: false,
            timestamp: 0,
        },
    ));
    assert_eq!(
        (log_entries(&assistant), log_entries(&result)),
        (
            vec![
                (Kind::Talk, "let me look".to_string()),
                (Kind::Tool, "ipython {\"code\":\"1+1\"}".to_string()),
            ],
            vec![(Kind::Echo, cap_text(&long))]
        )
    );
}

/// Tool results are capped at [`CAP`] characters, head and tail kept,
/// before the call sees them; shorter ones pass unchanged.
#[tokio::test]
async fn long_tool_results_are_capped_head_and_tail() {
    let hook = cap_tool_results();
    let context = |text: String| eukhe_agent::types::AfterToolCallContext {
        assistant_message: assistant_message(),
        tool_call: eukhe_agent::types::ToolCall {
            id: "1".into(),
            name: "ipython".into(),
            arguments: json!({}),
            thought_signature: None,
        },
        args: json!({}),
        result: eukhe_agent::types::AgentToolResult::text(text),
        is_error: false,
        context: eukhe_agent::types::AgentContext::default(),
    };
    let short = hook(
        context("short".into()),
        eukhe_agent::abort::AbortSignal::default(),
    )
    .await
    .unwrap();
    assert!(short.is_none());
    let long = "q".repeat(CAP * 2);
    let capped = hook(
        context(long.clone()),
        eukhe_agent::abort::AbortSignal::default(),
    )
    .await
    .unwrap()
    .expect("a long result is replaced");
    assert_eq!(
        capped.content,
        Some(vec![eukhe_agent::types::ToolResultContent::text(cap_text(
            &long
        ))])
    );
}
