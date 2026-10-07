//! Port of `test/anthropic-tool-name-normalization.test.ts`.
//!
//! Tests for Anthropic OAuth tool name normalization. When using Claude Code
//! OAuth, tool names must match CC's canonical casing: names matching a CC
//! tool (case-insensitively) are sent in CC casing and mapped back to the
//! original casing on inbound. This is a case-insensitive lookup, NOT a
//! mapping of different names (the old `find -> Glob` mapping broke the
//! round-trip because no tool named "glob" exists in `context.tools`).
//!
//! The TS suite is skipped without an Anthropic OAuth credential; here every
//! case is `#[ignore]`d and reads it from `PI_TEST_ANTHROPIC_TOKEN`.

mod anthropic_support;

use anthropic_support::resolve_test_api_key;
use eukhe_pi_ai::compat::{get_model, stream};
use eukhe_pi_ai::types::{AssistantMessageEvent, ProviderStreamOptions};
use eukhe_types::pi_ai::{AssistantContentBlock, Context, StopReason};
use futures::StreamExt;
use serde_json::json;

async fn tool_call_name_round_trip(
    tool_name: &str,
    tool_description: &str,
    parameter: (&str, &str),
    system_prompt: &str,
    prompt: &str,
) -> Option<String> {
    let oauth_token = resolve_test_api_key("anthropic").expect("PI_TEST_ANTHROPIC_TOKEN");
    let model = get_model("anthropic", "claude-sonnet-4-6").expect("anthropic/claude-sonnet-4-6");
    let (parameter_name, parameter_description) = parameter;
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": system_prompt,
        "messages": [{ "role": "user", "content": prompt, "timestamp": 1 }],
        "tools": [{
            "name": tool_name,
            "description": tool_description,
            "parameters": {
                "type": "object",
                "properties": { parameter_name: { "description": parameter_description, "type": "string" } },
                "required": [parameter_name],
            },
        }],
    }))
    .expect("context");

    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some(oauth_token);
    let s = stream(&model, context, options).expect("stream");
    let mut tool_call_name = None;
    let mut events = s.events();
    while let Some(event) = events.next().await {
        if let AssistantMessageEvent::ToolCallEnd {
            content_index,
            partial,
            ..
        } = &event
        {
            if let Some(AssistantContentBlock::ToolCall(tool_call)) =
                partial.content.get(*content_index)
            {
                tool_call_name = Some(tool_call.name.clone());
            }
        }
    }

    let response = s.result().await;
    assert_eq!(
        response.stop_reason,
        StopReason::ToolUse,
        "Error: {:?}",
        response.error_message
    );
    tool_call_name
}

#[tokio::test]
#[ignore = "needs PI_TEST_ANTHROPIC_TOKEN (Anthropic OAuth); run with --ignored"]
async fn should_normalize_user_defined_tool_matching_cc_name() {
    // User defines "todowrite"; CC has "TodoWrite": this should round-trip.
    let name = tool_call_name_round_trip(
        "todowrite",
        "Write a todo item",
        ("task", "The task to add"),
        "You are a helpful assistant. Use the todowrite tool when asked to add todos.",
        "Add a todo: buy milk. Use the todowrite tool.",
    )
    .await;
    // The tool call should come back with the ORIGINAL name "todowrite", not "TodoWrite"
    assert_eq!(name.as_deref(), Some("todowrite"));
}

#[tokio::test]
#[ignore = "needs PI_TEST_ANTHROPIC_TOKEN (Anthropic OAuth); run with --ignored"]
async fn should_handle_pis_built_in_tools() {
    // Pi's tools use lowercase names, CC uses PascalCase
    let name = tool_call_name_round_trip(
        "read",
        "Read a file",
        ("path", "File path"),
        "You are a helpful assistant. Use the read tool to read files.",
        "Read the file /tmp/test.txt using the read tool.",
    )
    .await;
    // The tool call should come back with the ORIGINAL name "read", not "Read"
    assert_eq!(name.as_deref(), Some("read"));
}

#[tokio::test]
#[ignore = "needs PI_TEST_ANTHROPIC_TOKEN (Anthropic OAuth); run with --ignored"]
async fn should_not_map_find_to_glob() {
    // Pi has a "find" tool, CC has "Glob": these are DIFFERENT tools.
    let name = tool_call_name_round_trip(
        "find",
        "Find files by pattern",
        ("pattern", "Glob pattern"),
        "You are a helpful assistant. Use the find tool to search for files.",
        "Find all .ts files using the find tool.",
    )
    .await;
    // Sent as "find" (no CC tool named "Find") and received back as "find".
    assert_eq!(name.as_deref(), Some("find"));
}

#[tokio::test]
#[ignore = "needs PI_TEST_ANTHROPIC_TOKEN (Anthropic OAuth); run with --ignored"]
async fn should_handle_custom_tools_that_dont_match_any_cc_tool_names() {
    let name = tool_call_name_round_trip(
        "my_custom_tool",
        "A custom tool",
        ("input", "Input value"),
        "You are a helpful assistant. Use my_custom_tool when asked.",
        "Use my_custom_tool with input 'hello'.",
    )
    .await;
    // Custom tool names should pass through unchanged
    assert_eq!(name.as_deref(), Some("my_custom_tool"));
}
