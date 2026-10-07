//! Differential checks: requests the TS reference (`@earendil-works/pi-ai`
//! 1.0.4 with `@anthropic-ai/sdk` 0.129.0) sends for fixed inputs, captured
//! with a `fetch` spy (the SDK's `x-stainless-*` telemetry headers excluded:
//! the port does not send them).

mod anthropic_support;

use anthropic_support::{collect, mock_fetch, model, requests, MockResponse};
use eukhe_pi_ai::api::anthropic_messages::stream;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::pi_user_agent::get_pi_user_agent;
use serde_json::{json, Value};

fn reference_context() -> eukhe_types::pi_ai::TranscriptContext {
    anthropic_support::context(&json!({
        "systemPrompt": "Be brief.",
        "tools": [{"name": "read", "description": "Read", "parameters": {"type": "object", "properties": {"path": {"type": "string"}}, "required": ["path"]}}],
        "messages": [
            {"role": "user", "content": "hi", "timestamp": 1},
            {"role": "assistant", "api": "anthropic-messages", "provider": "anthropic", "model": "claude-x", "content": [{"type": "thinking", "thinking": "hm", "thinkingSignature": "sig"}, {"type": "text", "text": "ok"}, {"type": "toolCall", "id": "call|1", "name": "read", "arguments": {"path": "a"}}], "usage": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0, "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0}}, "stopReason": "toolUse", "timestamp": 2},
            {"role": "toolResult", "toolCallId": "call|1", "toolName": "read", "content": [{"type": "text", "text": "data"}], "isError": false, "timestamp": 3},
            {"role": "user", "content": [{"type": "text", "text": "next"}, {"type": "image", "data": "AAA", "mimeType": "image/png"}], "timestamp": 4}
        ]
    }))
}

async fn capture(
    provider: &str,
    model_overrides: Value,
    api_key: &str,
    extra: Value,
) -> (Value, String) {
    let mut overrides = json!({
        "id": "claude-x", "name": "x", "provider": provider, "reasoning": true,
        "input": ["text", "image"], "cost": {"input": 1, "output": 1, "cacheRead": 1, "cacheWrite": 1},
        "contextWindow": 100_000, "maxTokens": 1000
    });
    for (key, value) in model_overrides.as_object().cloned().unwrap_or_default() {
        overrides[key] = value;
    }
    let model = model(&overrides);
    let (fetch, captured) = mock_fetch(MockResponse::json(400, r#"{"error":{"message":"stop"}}"#));
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some(api_key.to_owned());
    options.stream.request.fetch = Some(fetch);
    options.stream.session_id = Some("s1".to_owned());
    let mut extra = extra.as_object().cloned().unwrap_or_default();
    for key in ["cacheRetention", "temperature", "metadata"] {
        if let Some(value) = extra.remove(key) {
            match key {
                "cacheRetention" => {
                    options.stream.cache_retention =
                        Some(serde_json::from_value(value).expect("retention"));
                }
                "temperature" => options.stream.temperature = value.as_f64(),
                _ => options.stream.metadata = value.as_object().cloned(),
            }
        }
    }
    options.extra = extra;
    let (_, result) = collect(stream(&model, &reference_context(), options)).await;
    let request = requests(&captured).pop().expect("one request");
    let mut headers = serde_json::Map::new();
    let mut names: Vec<&str> = request
        .headers
        .keys()
        .map(reqwest::header::HeaderName::as_str)
        .collect();
    names.sort_unstable();
    for name in names {
        headers.insert(
            name.to_owned(),
            json!(request.header(name).expect("header")),
        );
    }
    (
        json!({"url": request.url, "headers": headers, "body": request.body}),
        result.error_message.unwrap_or_default(),
    )
}

fn expected(reference: &str) -> Value {
    let mut value: Value = serde_json::from_str(reference).expect("reference");
    // The pi user agent embeds the host OS; compare against this host's.
    if value["headers"]["user-agent"]
        .as_str()
        .is_some_and(|agent| agent.starts_with("pi "))
    {
        value["headers"]["user-agent"] = json!(get_pi_user_agent());
    }
    value
}

#[tokio::test]
async fn api_key_thinking_long_cache_tool_choice() {
    let (actual, error) = capture(
        "anthropic",
        json!({}),
        "sk-test",
        json!({"thinkingEnabled": true, "thinkingBudgetTokens": 500, "cacheRetention": "long", "temperature": 0.5, "toolChoice": "any", "metadata": {"user_id": "u"}}),
    )
    .await;
    // String comparison: key order is part of the wire format.
    assert_eq!(actual.to_string(), expected(r#"{"url":"https://api.anthropic.com/v1/messages?beta=true","headers":{"accept":"application/json","anthropic-beta":"interleaved-thinking-2025-05-14","anthropic-dangerous-direct-browser-access":"true","anthropic-version":"2023-06-01","content-type":"application/json","user-agent":"pi (linux 6.18.50; x64)","x-api-key":"sk-test"},"body":{"model":"claude-x","messages":[{"role":"user","content":"hi"},{"role":"assistant","content":[{"type":"thinking","thinking":"hm","signature":"sig"},{"type":"text","text":"ok"},{"type":"tool_use","id":"call|1","name":"read","input":{"path":"a"}}]},{"role":"user","content":[{"type":"tool_result","tool_use_id":"call|1","content":"data","is_error":false}]},{"role":"user","content":[{"type":"text","text":"next"},{"type":"image","source":{"type":"base64","media_type":"image/png","data":"AAA"},"cache_control":{"type":"ephemeral","ttl":"1h"}}]}],"max_tokens":1000,"stream":true,"system":[{"type":"text","text":"Be brief.","cache_control":{"type":"ephemeral","ttl":"1h"}}],"tools":[{"name":"read","description":"Read","eager_input_streaming":true,"input_schema":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"]},"cache_control":{"type":"ephemeral","ttl":"1h"}}],"thinking":{"type":"enabled","budget_tokens":500,"display":"summarized"},"metadata":{"user_id":"u"},"tool_choice":{"type":"any"}}}"#).to_string());
    assert_eq!(error, r#"400 {"error":{"message":"stop"}}"#);
}

#[tokio::test]
async fn oauth_thinking_disabled() {
    let (actual, error) = capture(
        "anthropic",
        json!({}),
        "sk-ant-oat-x",
        json!({"thinkingEnabled": false}),
    )
    .await;
    // String comparison: key order is part of the wire format.
    assert_eq!(actual.to_string(), expected(r#"{"url":"https://api.anthropic.com/v1/messages?beta=true","headers":{"accept":"application/json","anthropic-beta":"claude-code-20250219,oauth-2025-04-20","anthropic-dangerous-direct-browser-access":"true","anthropic-version":"2023-06-01","authorization":"Bearer sk-ant-oat-x","content-type":"application/json","user-agent":"claude-cli/2.1.280","x-app":"cli"},"body":{"model":"claude-x","messages":[{"role":"user","content":"hi"},{"role":"assistant","content":[{"type":"thinking","thinking":"hm","signature":"sig"},{"type":"text","text":"ok"},{"type":"tool_use","id":"call|1","name":"Read","input":{"path":"a"}}]},{"role":"user","content":[{"type":"tool_result","tool_use_id":"call|1","content":"data","is_error":false}]},{"role":"user","content":[{"type":"text","text":"next"},{"type":"image","source":{"type":"base64","media_type":"image/png","data":"AAA"},"cache_control":{"type":"ephemeral"}}]}],"max_tokens":1000,"stream":true,"system":[{"type":"text","text":"You are Claude Code, Anthropic's official CLI for Claude.","cache_control":{"type":"ephemeral"}},{"type":"text","text":"Be brief.","cache_control":{"type":"ephemeral"}}],"tools":[{"name":"Read","description":"Read","eager_input_streaming":true,"input_schema":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"]},"cache_control":{"type":"ephemeral"}}],"thinking":{"type":"disabled"}}}"#).to_string());
    assert_eq!(error, r#"400 {"error":{"message":"stop"}}"#);
}

#[tokio::test]
async fn mid_convo_effort_with_fallbacks() {
    let (actual, error) = capture(
        "anthropic",
        json!({"compat":{"supportsMidConvoEffort":true,"allowedFallbackModels":[{"provider":"anthropic","model":"claude-y","cost":{"input":1,"output":1,"cacheRead":1,"cacheWrite":1}}]}}),
        "sk-test",
        json!({"effort": "low", "temperature": 0.2}),
    )
    .await;
    // String comparison: key order is part of the wire format.
    assert_eq!(actual.to_string(), expected(r#"{"url":"https://api.anthropic.com/v1/messages?beta=true","headers":{"accept":"application/json","anthropic-beta":"server-side-fallback-2026-07-01,mid-conversation-output-config-2026-07-01,thinking-binding-controls-2026-08-01","anthropic-dangerous-direct-browser-access":"true","anthropic-version":"2023-06-01","content-type":"application/json","user-agent":"pi (linux 6.18.50; x64)","x-api-key":"sk-test"},"body":{"model":"claude-x","messages":[{"role":"user","content":"hi"},{"role":"assistant","content":[{"type":"thinking","thinking":"hm","signature":"sig"},{"type":"text","text":"ok"},{"type":"tool_use","id":"call|1","name":"read","input":{"path":"a"}}]},{"role":"user","content":[{"type":"tool_result","tool_use_id":"call|1","content":"data","is_error":false}]},{"role":"user","content":[{"type":"text","text":"next"},{"type":"image","source":{"type":"base64","media_type":"image/png","data":"AAA"},"cache_control":{"type":"ephemeral"}}]},{"role":"system","content":[],"output_config":{"effort":"low"}}],"max_tokens":1000,"stream":true,"system":[{"type":"text","text":"Be brief.","cache_control":{"type":"ephemeral"}}],"tools":[{"name":"read","description":"Read","eager_input_streaming":true,"input_schema":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"]},"cache_control":{"type":"ephemeral"}}],"thinking":{"type":"adaptive","display":"summarized","block_binding":{"prefix_mismatch_behavior":"drop_block"}},"output_config":{"effort":"high"},"fallbacks":[{"model":"claude-y"}]}}"#).to_string());
    assert_eq!(error, r#"400 {"error":{"message":"stop"}}"#);
}

#[tokio::test]
async fn openrouter_session_affinity() {
    let (actual, error) = capture(
        "openrouter",
        json!({}),
        "sk-test",
        json!({"cacheRetention": "short"}),
    )
    .await;
    // String comparison: key order is part of the wire format.
    assert_eq!(actual.to_string(), expected(r#"{"url":"https://api.anthropic.com/v1/messages?beta=true","headers":{"accept":"application/json","anthropic-dangerous-direct-browser-access":"true","anthropic-version":"2023-06-01","content-type":"application/json","user-agent":"pi (linux 6.18.50; x64)","x-api-key":"sk-test","x-session-id":"s1"},"body":{"model":"claude-x","messages":[{"role":"user","content":"hi"},{"role":"assistant","content":[{"type":"text","text":"hm"},{"type":"text","text":"ok"},{"type":"tool_use","id":"call_1","name":"read","input":{"path":"a"}}]},{"role":"user","content":[{"type":"tool_result","tool_use_id":"call_1","content":"data","is_error":false}]},{"role":"user","content":[{"type":"text","text":"next"},{"type":"image","source":{"type":"base64","media_type":"image/png","data":"AAA"},"cache_control":{"type":"ephemeral"}}]}],"max_tokens":1000,"stream":true,"system":[{"type":"text","text":"Be brief.","cache_control":{"type":"ephemeral"}}],"tools":[{"name":"read","description":"Read","eager_input_streaming":true,"input_schema":{"type":"object","properties":{"path":{"type":"string"}},"required":["path"]},"cache_control":{"type":"ephemeral"}}]}}"#).to_string());
    assert_eq!(error, r#"400 {"error":{"message":"stop"}}"#);
}
