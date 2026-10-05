use std::sync::atomic::{AtomicBool, Ordering};

use pa_agent::scripted::ScriptedProvider;
use pa_agent::types::{CustomAgentMessage, ToolResultMessage};

use super::*;
use crate::memory::compactor::tests::Scripted;
use crate::session_engine::engine::{create_session, SessionEngine, SessionEngineConfig};
use crate::session_engine::tool_bridge::bridge_tool;
use crate::session_engine::PromptOptions;
use crate::tools::tool_definition::{ExecutionMode, ToolDefinition};

fn model() -> pa_agent::types::Model {
    pa_agent::types::Model {
        id: "m".into(),
        name: "m".into(),
        api: "test".into(),
        provider: "test".into(),
        base_url: "http://localhost".into(),
        reasoning: false,
        cost: pa_agent::types::UsageCost::default(),
        context_window: 1_000_000,
        max_tokens: 100,
    }
}

fn echo_definition() -> ToolDefinition {
    ToolDefinition {
        name: "echo".to_string(),
        label: "Echo".to_string(),
        description: "Echoes its input".to_string(),
        prompt_snippet: String::new(),
        parameters: serde_json::json!({
            "type": "object",
            "properties": { "text": { "type": "string" } },
            "required": ["text"]
        }),
        execution_mode: Some(ExecutionMode::Sequential),
        prepare_arguments: None,
        execute: Arc::new(|_id, params, _signal, _on_update| {
            let text = params
                .get("text")
                .and_then(|t| t.as_str())
                .unwrap_or_default()
                .to_string();
            Box::pin(async move { Ok(ToolExecutionResult::text(format!("echo: {text}"))) })
        }),
    }
}

struct Bed {
    _tmp: tempfile::TempDir,
    memory: Memory,
    provider: Arc<ScriptedProvider>,
    engine: SessionEngine,
}

async fn bed(depth: u32, steering_stop: Option<Arc<AtomicBool>>) -> Bed {
    let tmp = tempfile::tempdir().unwrap();
    let cwd = tmp.path().join("project");
    let agent_dir = tmp.path().join("agent");
    std::fs::create_dir_all(&cwd).unwrap();
    std::fs::create_dir_all(&agent_dir).unwrap();
    let memory = Memory::open(
        crate::memory::chat_dir(&agent_dir),
        Scripted::with(Vec::new()),
    )
    .await
    .unwrap();
    let provider = Arc::new(ScriptedProvider::new(model()));
    let probe = steering_stop.map(|flag| {
        Arc::new(move || flag.swap(false, Ordering::SeqCst)) as Arc<dyn Fn() -> bool + Send + Sync>
    });
    let engine = create_session(SessionEngineConfig {
        memory: Some(memory.clone()),
        cwd,
        agent_dir,
        model: Some(model()),
        stream_fn: Some(provider.stream_fn()),
        tools: vec![bridge_tool(echo_definition())],
        rlm_depth: Some(depth),
        queued_steering_probe: probe,
        ..Default::default()
    })
    .await
    .unwrap();
    Bed {
        _tmp: tmp,
        memory,
        provider,
        engine,
    }
}

fn first_text(message: &Message) -> String {
    match message {
        Message::User(user) => user_text(&user.content),
        Message::Assistant(_) | Message::ToolResult(_) => String::new(),
    }
}

fn view_parts(message: &Message) -> Vec<(String, Option<CacheBreakpoint>)> {
    let Message::User(user) = message else {
        panic!("the view is a user message");
    };
    let UserContent::Parts(parts) = &user.content else {
        panic!("the view is cut into parts");
    };
    parts
        .iter()
        .map(|part| match part {
            UserPart::Text(text) => (text.text.clone(), text.cache_breakpoint),
            UserPart::Image(_) => panic!("no images in the view"),
        })
        .collect()
}

async fn log(memory: &Memory) -> Vec<String> {
    let total = memory.status().await.unwrap().messages;
    let mut lines = Vec::new();
    for id in 0..total {
        lines.push(memory.zoom(id, 1).await.unwrap());
    }
    lines
}

#[tokio::test]
async fn root_turns_start_fresh_from_the_view_and_log_everything() {
    let bed = bed(0, None).await;
    assert!(bed
        .engine
        .system_prompt
        .contains("You are Eukhe, an AI agent"));
    assert!(bed
        .engine
        .system_prompt
        .contains("zoom(id, n) opens line id+n"));
    assert!(!bed.engine.system_prompt.contains("Current date:"));
    bed.provider.push_tool_call_turn(
        None,
        vec![("call-1", "echo", serde_json::json!({ "text": "hi" }))],
    );
    bed.provider.push_text_turn("done one");
    bed.provider.push_text_turn("done two");
    bed.engine
        .prompt("first", PromptOptions::default())
        .await
        .unwrap();
    bed.engine
        .prompt("second", PromptOptions::default())
        .await
        .unwrap();

    let calls = bed.provider.calls();
    assert_eq!(calls.len(), 3);
    let names: Vec<&str> = calls[0]
        .tools
        .iter()
        .map(|tool| tool.name.as_str())
        .collect();
    assert_eq!(names, vec!["echo", "ipython", "zoom", "date"]);
    // Turn one: an empty view, then the message; the view is
    // byte-identical on the call's second step.
    assert_eq!(
        view_parts(&calls[0].messages[0]),
        vec![("<chat>\n</chat>".to_string(), None)]
    );
    // The harness digest rides after the view on every fresh call.
    assert!(first_text(&calls[0].messages[1]).starts_with("[harness-digest]"));
    assert_eq!(first_text(&calls[0].messages[2]), "first");
    assert_eq!(calls[1].messages[0], calls[0].messages[0]);
    assert_eq!(calls[1].messages.len(), 5);
    // Turn two: fresh. The view summarizes turn one; nothing else carried.
    assert_eq!(
        view_parts(&calls[2].messages[0]),
        vec![(
            "<chat>\n0+1|user: first\n1+1|tool: echo {\"text\":\"hi\"}\n2+1|echo: echo: hi\n3+1|talk: done one\n</chat>".to_string(),
            None
        )]
    );
    assert_eq!(calls[2].messages.len(), 3);
    assert!(first_text(&calls[2].messages[1]).starts_with("[harness-digest]"));
    assert_eq!(first_text(&calls[2].messages[2]), "second");
    assert_eq!(
        log(&bed.memory).await,
        vec![
            "0+0|user: first",
            "1+0|tool: echo {\"text\":\"hi\"}",
            "2+0|echo: echo: hi",
            "3+0|talk: done one",
            "4+0|user: second",
            "5+0|talk: done two",
        ]
    );
}

#[tokio::test]
async fn a_message_at_a_tool_boundary_continues_the_call() {
    let stop = Arc::new(AtomicBool::new(true));
    let bed = bed(0, Some(Arc::clone(&stop))).await;
    bed.provider.push_tool_call_turn(
        None,
        vec![("call-1", "echo", serde_json::json!({ "text": "a" }))],
    );
    bed.provider.push_text_turn("answered");
    // The steering probe cuts the run after the tool results.
    bed.engine
        .prompt("work", PromptOptions::default())
        .await
        .unwrap();
    assert!(!bed.engine.session.next_turn_is_fresh().await);
    bed.engine
        .prompt("also this", PromptOptions::default())
        .await
        .unwrap();
    let calls = bed.provider.calls();
    assert_eq!(calls.len(), 2);
    // Same call: the same view, the carried steps, then the new message.
    assert_eq!(calls[1].messages[0], calls[0].messages[0]);
    assert_eq!(calls[1].messages.len(), 6);
    assert_eq!(first_text(&calls[1].messages[5]), "also this");
    assert!(bed.engine.session.next_turn_is_fresh().await);
    assert_eq!(
        log(&bed.memory).await,
        vec![
            "0+0|user: work",
            "1+0|tool: echo {\"text\":\"a\"}",
            "2+0|echo: echo: a",
            "3+0|user: also this",
            "4+0|talk: answered",
        ]
    );
}

#[tokio::test]
async fn a_subagent_keeps_its_first_view_and_logs_nothing() {
    let bed = bed(1, None).await;
    assert!(bed
        .engine
        .system_prompt
        .contains("You are a subagent of Eukhe"));
    bed.memory.append(Kind::User, "root context").await.unwrap();
    bed.provider.push_text_turn("one");
    bed.provider.push_text_turn("two");
    bed.engine
        .prompt("task", PromptOptions::default())
        .await
        .unwrap();
    bed.memory
        .append(Kind::User, "later root message")
        .await
        .unwrap();
    bed.engine
        .prompt("more", PromptOptions::default())
        .await
        .unwrap();
    let calls = bed.provider.calls();
    assert_eq!(
        view_parts(&calls[0].messages[0]),
        vec![("<chat>\n0+1|user: root context\n</chat>".to_string(), None)]
    );
    // The conversation continues under the same view.
    assert_eq!(calls[1].messages[0], calls[0].messages[0]);
    assert_eq!(calls[1].messages.len(), 5);
    assert_eq!(log(&bed.memory).await.len(), 2);
}

fn assistant_message() -> pa_agent::types::AssistantMessage {
    serde_json::from_value(serde_json::json!({
        "content": [],
        "usage": pa_agent::types::Usage::zero(),
        "stopReason": "stop"
    }))
    .unwrap()
}

#[test]
fn log_entries_follow_the_message_kinds() {
    let assistant = AgentMessage::Standard(Message::Assistant(pa_agent::types::AssistantMessage {
        content: vec![
            AssistantContent::Thinking(pa_agent::types::ThinkingContent {
                thinking: "secret".into(),
                thinking_signature: None,
                redacted: None,
            }),
            AssistantContent::Text(TextContent {
                text: "let me look".into(),
                text_signature: None,
                cache_breakpoint: None,
            }),
            AssistantContent::ToolCall(pa_agent::types::ToolCall {
                id: "1".into(),
                name: "ipython".into(),
                arguments: serde_json::json!({ "code": "1+1" }),
                thought_signature: None,
            }),
        ],
        ..assistant_message()
    }));
    assert_eq!(
        log_entries(&assistant),
        vec![
            (Kind::Talk, "let me look".to_string()),
            (Kind::Tool, "ipython {\"code\":\"1+1\"}".to_string()),
        ]
    );
    let long = "z".repeat(CAP + 10);
    let result = AgentMessage::Standard(Message::ToolResult(ToolResultMessage {
        tool_call_id: "1".into(),
        tool_name: "ipython".into(),
        content: vec![ToolResultContent::text(long.clone())],
        details: None,
        is_error: false,
        timestamp: 0,
    }));
    assert_eq!(log_entries(&result), vec![(Kind::Echo, cap_text(&long))]);
    let custom = |custom_type: &str, content: &str| {
        AgentMessage::Custom(CustomAgentMessage {
            role: "custom".into(),
            payload: serde_json::json!({ "customType": custom_type, "content": content, "display": true }),
        })
    };
    assert_eq!(
        log_entries(&custom(
            "agent_message",
            "[agent-message from child:x]\n\ndone"
        )),
        vec![(
            Kind::User,
            "[agent-message from child:x]\n\ndone".to_string()
        )]
    );
    assert_eq!(
        log_entries(&custom("goal_context", "<goal_context>go</goal_context>")),
        vec![(
            Kind::User,
            "[goal] <goal_context>go</goal_context>".to_string()
        )]
    );
    assert!(log_entries(&custom("harness_digest", "[harness-digest] state")).is_empty());
}

#[tokio::test]
async fn long_tool_results_are_capped_head_and_tail() {
    let hook = cap_tool_results();
    let assistant = assistant_message();
    let context = |text: String| pa_agent::types::AfterToolCallContext {
        assistant_message: assistant.clone(),
        tool_call: pa_agent::types::ToolCall {
            id: "1".into(),
            name: "ipython".into(),
            arguments: serde_json::json!({}),
            thought_signature: None,
        },
        args: serde_json::json!({}),
        result: pa_agent::types::AgentToolResult::text(text),
        is_error: false,
        context: pa_agent::types::AgentContext {
            system_prompt: String::new(),
            messages: Vec::new(),
            tools: Vec::new(),
        },
    };
    assert!(hook(
        context("short".into()),
        pa_agent::abort::AbortSignal::default()
    )
    .await
    .unwrap()
    .is_none());
    let long = "q".repeat(CAP * 2);
    let capped = hook(
        context(long.clone()),
        pa_agent::abort::AbortSignal::default(),
    )
    .await
    .unwrap()
    .unwrap();
    assert_eq!(
        capped.content,
        Some(vec![ToolResultContent::text(cap_text(&long))])
    );
}
