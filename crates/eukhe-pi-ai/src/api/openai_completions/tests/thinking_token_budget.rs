//! Port of `openai-completions-thinking-token-budget.test.ts`.

use std::sync::PoisonError;

use serde_json::json;

use super::support::{collect, model, payload_recorder, sse_fetch, user_context};
use crate::api::openai_completions::stream_simple;
use crate::types::{
    JsonValue, Model, ProviderRequestOptions, SimpleStreamOptions, StreamOptions, ThinkingBudgets,
    ThinkingLevel,
};

fn vllm_model(compat: &JsonValue) -> Model {
    model(json!({
        "id": "zai-org/glm-5.2",
        "name": "GLM 5.2 (local vLLM)",
        "api": "openai-completions",
        "provider": "local-vllm",
        "baseUrl": "http://localhost:8000/v1",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 262_144,
        "maxTokens": 16384,
        "compat": compat,
    }))
}

/// The TS default compat: `{ thinkingFormat: "zai", supportsThinkingTokenBudget: true }`.
fn default_vllm_model() -> Model {
    vllm_model(&json!({ "thinkingFormat": "zai", "supportsThinkingTokenBudget": true }))
}

#[derive(Default)]
struct CaptureOptions {
    reasoning: Option<ThinkingLevel>,
    thinking_budgets: Option<ThinkingBudgets>,
    max_tokens: Option<u64>,
}

/// The `onPayload` params of one `streamSimple` call.
async fn capture(model: &Model, options: CaptureOptions) -> JsonValue {
    let (fetch, _) = sse_fetch(vec![json!({
        "choices": [{ "delta": {}, "finish_reason": "stop" }],
        "usage": {
            "prompt_tokens": 1,
            "completion_tokens": 1,
            "prompt_tokens_details": { "cached_tokens": 0 },
            "completion_tokens_details": { "reasoning_tokens": 0 },
        },
    })]);
    let (on_payload, seen) = payload_recorder();
    collect(stream_simple(
        model,
        &user_context("Hi"),
        SimpleStreamOptions {
            stream: StreamOptions {
                request: ProviderRequestOptions {
                    api_key: Some("test".to_owned()),
                    fetch: Some(fetch),
                    on_payload: Some(on_payload),
                    ..ProviderRequestOptions::default()
                },
                max_tokens: options.max_tokens,
                ..StreamOptions::default()
            },
            reasoning: options.reasoning,
            thinking_budgets: options.thinking_budgets,
            ..SimpleStreamOptions::default()
        },
    ))
    .await;
    let payloads = seen.lock().unwrap_or_else(PoisonError::into_inner);
    payloads.last().cloned().expect("payload captured")
}

#[tokio::test]
async fn sends_the_configured_budget_for_the_requested_level() {
    let params = capture(
        &default_vllm_model(),
        CaptureOptions {
            reasoning: Some(ThinkingLevel::Medium),
            thinking_budgets: Some(ThinkingBudgets {
                medium: Some(4096),
                ..ThinkingBudgets::default()
            }),
            ..CaptureOptions::default()
        },
    )
    .await;
    assert_eq!(params.get("thinking_token_budget"), Some(&json!(4096)));
}

#[tokio::test]
async fn omits_the_budget_when_neither_the_field_nor_the_alias_is_set() {
    let params = capture(
        &vllm_model(&json!({ "thinkingFormat": "zai" })),
        CaptureOptions {
            reasoning: Some(ThinkingLevel::Medium),
            thinking_budgets: Some(ThinkingBudgets {
                medium: Some(4096),
                ..ThinkingBudgets::default()
            }),
            ..CaptureOptions::default()
        },
    )
    .await;
    assert_eq!(params.get("thinking_token_budget"), None);
    assert_eq!(params.get("thinking_budget"), None);
    assert_eq!(params.get("thinking_budget_tokens"), None);
}

#[tokio::test]
async fn omits_the_budget_when_thinking_is_off() {
    let params = capture(
        &default_vllm_model(),
        CaptureOptions {
            reasoning: None,
            thinking_budgets: Some(ThinkingBudgets {
                high: Some(8192),
                ..ThinkingBudgets::default()
            }),
            ..CaptureOptions::default()
        },
    )
    .await;
    assert_eq!(params.get("thinking_token_budget"), None);
}

#[tokio::test]
async fn clamps_xhigh_and_max_to_the_high_budget() {
    let high_budget = || {
        Some(ThinkingBudgets {
            high: Some(8192),
            ..ThinkingBudgets::default()
        })
    };
    let xhigh = capture(
        &default_vllm_model(),
        CaptureOptions {
            reasoning: Some(ThinkingLevel::Xhigh),
            thinking_budgets: high_budget(),
            ..CaptureOptions::default()
        },
    )
    .await;
    let max = capture(
        &default_vllm_model(),
        CaptureOptions {
            reasoning: Some(ThinkingLevel::Max),
            thinking_budgets: high_budget(),
            ..CaptureOptions::default()
        },
    )
    .await;
    assert_eq!(xhigh.get("thinking_token_budget"), Some(&json!(8192)));
    assert_eq!(max.get("thinking_token_budget"), Some(&json!(8192)));
}

#[tokio::test]
async fn leaves_room_for_the_answer_when_the_budget_meets_the_response_ceiling() {
    let params = capture(
        &default_vllm_model(),
        CaptureOptions {
            reasoning: Some(ThinkingLevel::High),
            ..CaptureOptions::default()
        },
    )
    .await;
    assert_eq!(
        params.get("thinking_token_budget"),
        Some(&json!(16384 - 1024))
    );
}

#[tokio::test]
async fn uses_the_caller_max_tokens_as_the_ceiling_when_it_is_lower_than_the_model_cap() {
    let params = capture(
        &default_vllm_model(),
        CaptureOptions {
            reasoning: Some(ThinkingLevel::High),
            thinking_budgets: Some(ThinkingBudgets {
                high: Some(8192),
                ..ThinkingBudgets::default()
            }),
            max_tokens: Some(4096),
        },
    )
    .await;
    assert_eq!(
        params.get("thinking_token_budget"),
        Some(&json!(4096 - 1024))
    );
}

/// `it.each(["thinking_budget", "thinking_budget_tokens"])`.
async fn sends_field_when_thinking_token_budget_field_is_set(field: &str) {
    let params = capture(
        &vllm_model(&json!({ "thinkingFormat": "qwen", "thinkingTokenBudgetField": field })),
        CaptureOptions {
            reasoning: Some(ThinkingLevel::Medium),
            thinking_budgets: Some(ThinkingBudgets {
                medium: Some(4096),
                ..ThinkingBudgets::default()
            }),
            ..CaptureOptions::default()
        },
    )
    .await;
    assert_eq!(params.get(field), Some(&json!(4096)));
    assert_eq!(params.get("thinking_token_budget"), None);
}

#[tokio::test]
async fn sends_thinking_budget_when_thinking_token_budget_field_is_set() {
    sends_field_when_thinking_token_budget_field_is_set("thinking_budget").await;
}

#[tokio::test]
async fn sends_thinking_budget_tokens_when_thinking_token_budget_field_is_set() {
    sends_field_when_thinking_token_budget_field_is_set("thinking_budget_tokens").await;
}

#[tokio::test]
async fn lets_thinking_token_budget_field_win_over_the_boolean_alias() {
    let params = capture(
        &vllm_model(&json!({
            "thinkingFormat": "zai",
            "supportsThinkingTokenBudget": true,
            "thinkingTokenBudgetField": "thinking_budget",
        })),
        CaptureOptions {
            reasoning: Some(ThinkingLevel::Medium),
            thinking_budgets: Some(ThinkingBudgets {
                medium: Some(4096),
                ..ThinkingBudgets::default()
            }),
            ..CaptureOptions::default()
        },
    )
    .await;
    assert_eq!(params.get("thinking_budget"), Some(&json!(4096)));
    assert_eq!(params.get("thinking_token_budget"), None);
}

fn chat_template_model() -> Model {
    vllm_model(&json!({
        "thinkingFormat": "chat-template",
        "chatTemplateKwargs": {
            "enable_thinking": { "$var": "thinking.enabled" },
            "thinking_budget": { "$var": "thinking.budget" },
        },
    }))
}

#[tokio::test]
async fn puts_the_clamped_budget_in_chat_template_kwargs_when_var_is_thinking_budget() {
    let params = capture(
        &chat_template_model(),
        CaptureOptions {
            reasoning: Some(ThinkingLevel::High),
            ..CaptureOptions::default()
        },
    )
    .await;
    assert_eq!(
        params.get("chat_template_kwargs"),
        Some(&json!({ "enable_thinking": true, "thinking_budget": 16384 - 1024 }))
    );
    assert_eq!(params.get("thinking_token_budget"), None);
}

#[tokio::test]
async fn omits_thinking_budget_from_chat_template_kwargs_when_thinking_is_off() {
    let params = capture(&chat_template_model(), CaptureOptions::default()).await;
    assert_eq!(
        params.get("chat_template_kwargs"),
        Some(&json!({ "enable_thinking": false }))
    );
}
