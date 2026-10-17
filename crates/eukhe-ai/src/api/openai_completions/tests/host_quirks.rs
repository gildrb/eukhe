//! eukhe addition: the wire of the quirks rulebook's host settings
//! (docs/inference.md S6.2). A model names one host: the provider's host
//! wins over a host its base URL names, and the two do not combine.

use serde_json::json;

use super::support::{capture_payload, context, model};
use crate::api::openai_completions::OpenAICompletionsOptions;
use crate::types::{JsonValue, Model};

fn chat_model(provider: &str, id: &str, base_url: &str) -> Model {
    model(json!({
        "id": id,
        "name": id,
        "api": "openai-completions",
        "provider": provider,
        "baseUrl": base_url,
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 4096,
    }))
}

/// The payload of a request with a system prompt, one tool, and one user
/// message.
async fn payload(model: &Model) -> JsonValue {
    let ctx = context(json!({
        "systemPrompt": "System prompt",
        "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }],
        "tools": [{
            "name": "read",
            "description": "Read a file",
            "parameters": {
                "type": "object",
                "properties": { "path": { "type": "string" } },
                "required": ["path"],
            },
        }],
    }));
    capture_payload(model, &ctx, OpenAICompletionsOptions::default()).await
}

/// Anthropic-format `cache_control` marks go to `anthropic/` models of the
/// `openrouter` provider only: a custom provider at `openrouter.ai` gets
/// the `OpenRouter` settings of its URL but sends no marks.
#[tokio::test]
async fn a_custom_provider_at_openrouter_ai_sends_no_cache_marks() {
    let model = chat_model(
        "my-router",
        "anthropic/claude-sonnet-4.5",
        "https://openrouter.ai/api/v1",
    );
    assert_eq!(
        payload(&model).await,
        json!({
            "model": "anthropic/claude-sonnet-4.5",
            "messages": [
                { "role": "system", "content": "System prompt" },
                { "role": "user", "content": "Hello" },
            ],
            "stream": true,
            "stream_options": { "include_usage": true },
            "store": false,
            "tools": [{
                "type": "function",
                "function": {
                    "name": "read",
                    "description": "Read a file",
                    "parameters": {
                        "type": "object",
                        "properties": { "path": { "type": "string" } },
                        "required": ["path"],
                    },
                },
            }],
        })
    );
}

/// The `openrouter` provider behind a loopback base URL (a local proxy)
/// keeps the `OpenRouter` host's settings (`store`; the `developer` role
/// for an `openai/` reasoning model; the `OpenRouter` `reasoning` format):
/// the loopback host's settings (no `store`, no `developer` role) do not
/// combine with them.
#[tokio::test]
async fn the_openrouter_provider_at_a_loopback_url_keeps_the_openrouter_settings() {
    let mut model = chat_model("openrouter", "openai/gpt-5", "http://localhost:8080/api/v1");
    model.reasoning = true;
    assert_eq!(
        payload(&model).await,
        json!({
            "model": "openai/gpt-5",
            "messages": [
                { "role": "developer", "content": "System prompt" },
                { "role": "user", "content": "Hello" },
            ],
            "stream": true,
            "stream_options": { "include_usage": true },
            "store": false,
            "tools": [{
                "type": "function",
                "function": {
                    "name": "read",
                    "description": "Read a file",
                    "parameters": {
                        "type": "object",
                        "properties": { "path": { "type": "string" } },
                        "required": ["path"],
                    },
                },
            }],
            "reasoning": { "effort": "none" },
        })
    );
}

/// The capability hosts (scope `capabilities`) change no wire: provider
/// `openai` behind a loopback URL sends what any provider there sends (the
/// loopback host: no `store`, no `developer` role).
#[tokio::test]
async fn the_openai_provider_at_a_loopback_url_keeps_the_loopback_settings() {
    let mut openai = chat_model("openai", "gpt-5", "http://localhost:8080/v1");
    openai.reasoning = true;
    let mut custom = openai.clone();
    custom.provider = "my-local".to_owned();
    let sent = payload(&openai).await;
    assert_eq!(
        (
            sent.get("store").cloned(),
            sent["messages"][0]["role"].clone()
        ),
        (None, json!("system"))
    );
    assert_eq!(sent, payload(&custom).await);
}

/// A llama.cpp provider on a LAN address names no wire host, as before
/// the capability rules: it sends what a provider without a host sends.
#[tokio::test]
async fn a_llama_cpp_provider_on_a_lan_address_sends_the_hostless_wire() {
    let mut llama = chat_model("llama-cpp", "gemma-3-4b", "http://192.168.1.20:8080/v1");
    llama.reasoning = true;
    let mut custom = llama.clone();
    custom.provider = "my-lan".to_owned();
    let sent = payload(&llama).await;
    assert_eq!(
        (
            sent.get("store").cloned(),
            sent["messages"][0]["role"].clone()
        ),
        (Some(json!(false)), json!("developer"))
    );
    assert_eq!(sent, payload(&custom).await);
}
