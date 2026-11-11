//! The output cap of an `openai-completions` request, as omp sends it: the
//! caller's cap, else the model's max, fitted to the window (the compiled
//! `Fx.cap`, `laws/facts.bend` `facts_cap_*`; omp
//! `fitOutputTokensToContextWindow`), then held under the host's ceiling
//! (omp `resolveOpenAIOutputTokenParam`).

use std::sync::PoisonError;

use serde_json::json;

use super::support::{collect, model, payload_recorder, sse_fetch, stop_chunks, user_context};
use crate::api::openai_completions::stream_simple;
use crate::types::{
    JsonValue, Model, ProviderRequestOptions, SimpleStreamOptions, StreamOptions, ThinkingLevel,
    TranscriptContext,
};
use crate::utils::estimate::estimate_context_tokens;

/// The prompt size of a one-message context as omp sizes it
/// (`countPromptTokens`, `packages/agent/src/output-budget.ts:133-144`):
/// the local estimate with a tenth on top and 16 tokens of framing.
fn prompt_tokens(context: &TranscriptContext) -> u64 {
    let estimate = estimate_context_tokens(context.messages()).tokens;
    estimate + estimate.div_ceil(10) + 16
}

/// A reasoning Qwen model of a custom provider at `base_url`, with
/// `overrides` merged on top.
// Test helpers take literal JSON by value, mirroring the TS call shape.
#[allow(clippy::needless_pass_by_value)]
fn custom_model(
    base_url: &str,
    context_window: u64,
    max_tokens: u64,
    overrides: JsonValue,
) -> Model {
    let mut base = json!({
        "id": "qwen3.8-27b",
        "name": "Qwen 3.8 27B",
        "api": "openai-completions",
        "provider": "elpis",
        "baseUrl": base_url,
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": context_window,
        "maxTokens": max_tokens,
    });
    if let (Some(base), Some(overrides)) = (base.as_object_mut(), overrides.as_object()) {
        base.extend(overrides.clone());
    }
    model(base)
}

/// A server on another machine (the user's: a tailnet address).
const REMOTE: &str = "https://server.example.ts.net/v1";
/// A server on this machine.
const LOCAL: &str = "http://localhost:8000/v1";

/// The `onPayload` params of one high-reasoning `streamSimple` call with
/// the caller's cap `max_tokens`.
async fn capture(model: &Model, context: &TranscriptContext, max_tokens: Option<u64>) -> JsonValue {
    let (fetch, _) = sse_fetch(stop_chunks());
    let (on_payload, seen) = payload_recorder();
    collect(stream_simple(
        model,
        context,
        SimpleStreamOptions {
            stream: StreamOptions {
                max_tokens,
                request: ProviderRequestOptions {
                    api_key: Some("test".to_owned()),
                    fetch: Some(fetch),
                    on_payload: Some(on_payload),
                    ..ProviderRequestOptions::default()
                },
                ..StreamOptions::default()
            },
            reasoning: Some(ThinkingLevel::High),
            ..SimpleStreamOptions::default()
        },
    ))
    .await;
    let payloads = seen.lock().unwrap_or_else(PoisonError::into_inner);
    payloads.last().cloned().expect("payload captured")
}

/// Both output cap fields of a payload: `(max_tokens, max_completion_tokens)`.
fn caps(params: &JsonValue) -> (Option<u64>, Option<u64>) {
    let field = |name: &str| params.get(name).and_then(JsonValue::as_u64);
    (field("max_tokens"), field("max_completion_tokens"))
}

/// Regression (user report): the local model `elpis/qwen3.8-27b` sent no
/// output cap, the server cut every reply at its own default (4096) and
/// the model began to write in small pieces. omp sends the model's max on
/// every request (`packages/ai/src/stream.ts:1802`), at most 64000 on a
/// host that is no local backend
/// (`packages/ai/src/providers/openai-shared.ts:711-715`): for the same
/// definition `max_completion_tokens: 64000`, and the configured
/// `maxTokens` when it is lower.
#[tokio::test]
async fn a_custom_model_sends_its_max_as_the_output_cap() {
    let context = user_context("Hi");
    let window_as_max = custom_model(REMOTE, 262_144, 262_144, json!({}));
    let configured = custom_model(REMOTE, 262_144, 32_768, json!({}));
    let max_tokens_field = custom_model(
        REMOTE,
        262_144,
        32_768,
        json!({ "compat": { "maxTokensField": "max_tokens" } }),
    );
    assert_eq!(
        [
            caps(&capture(&window_as_max, &context, None).await),
            caps(&capture(&configured, &context, None).await),
            caps(&capture(&max_tokens_field, &context, None).await),
        ],
        [
            (None, Some(64_000)),
            (None, Some(32_768)),
            (Some(32_768), None)
        ]
    );
}

/// omp `clampOutputToModelMax` (`packages/catalog/src/compat/resolve.ts:605`):
/// a local backend (a base URL on this machine or a private network) and a
/// model whose compat says so take the model's whole max; any other host
/// at most 64000.
#[tokio::test]
async fn only_a_local_backend_takes_a_cap_above_64000() {
    let context = user_context("Hi");
    let mut sent = Vec::new();
    for (base_url, overrides) in [
        (LOCAL, json!({})),
        ("http://192.168.1.20:8000/v1", json!({})),
        (REMOTE, json!({})),
        (
            REMOTE,
            json!({ "compat": { "clampOutputToModelMax": true } }),
        ),
        (
            LOCAL,
            json!({ "compat": { "clampOutputToModelMax": false } }),
        ),
    ] {
        let model = custom_model(base_url, 262_144, 81_920, overrides);
        sent.push(caps(&capture(&model, &context, None).await));
    }
    assert_eq!(
        sent,
        [
            (None, Some(81_920)),
            (None, Some(81_920)),
            (None, Some(64_000)),
            (None, Some(81_920)),
            (None, Some(64_000)),
        ]
    );
}

/// omp `fitOutputTokensToContextWindow`
/// (`packages/agent/src/output-budget.ts:81-96`): a max the window cannot
/// hold beside the prompt is sent as the room the window leaves after the
/// prompt and 64 tokens of headway, never below 1024; a max at the window
/// is such a max on every request.
#[tokio::test]
async fn a_cap_the_window_cannot_hold_shrinks_to_the_room() {
    let short = user_context("Hi");
    let long = user_context(&"word ".repeat(2_000));
    let (short_prompt, long_prompt) = (prompt_tokens(&short), prompt_tokens(&long));
    assert_eq!(
        [
            caps(
                &capture(
                    &custom_model(LOCAL, 262_144, 262_144, json!({})),
                    &short,
                    None
                )
                .await
            ),
            caps(
                &capture(
                    &custom_model(LOCAL, long_prompt + 64 + 3000, 4000, json!({})),
                    &long,
                    None
                )
                .await
            ),
            caps(
                &capture(
                    &custom_model(LOCAL, long_prompt + 64 + 500, 4000, json!({})),
                    &long,
                    None
                )
                .await
            ),
        ],
        [
            (None, Some(262_144 - short_prompt - 64)),
            (None, Some(3000)),
            (None, Some(1024)),
        ],
        "prompts {short_prompt} {long_prompt}"
    );
}

/// omp `resolveOpenAIOutputTokenParam`
/// (`packages/ai/src/providers/openai-shared.ts:706-710`): `OpenRouter`
/// leaves the model's default cap out, so each upstream applies its own
/// max; a caller's cap is sent, and a Kimi model always carries its cap.
#[tokio::test]
async fn openrouter_sends_no_default_cap() {
    let context = user_context("Hi");
    let openrouter = |id: &str| {
        custom_model(
            "https://openrouter.ai/api/v1",
            262_144,
            32_768,
            json!({ "id": id, "provider": "openrouter" }),
        )
    };
    assert_eq!(
        [
            caps(&capture(&openrouter("qwen/qwen3.8-27b"), &context, None).await),
            caps(&capture(&openrouter("qwen/qwen3.8-27b"), &context, Some(2000)).await),
            caps(&capture(&openrouter("moonshotai/kimi-k2.6"), &context, None).await),
        ],
        [(None, None), (None, Some(2000)), (None, Some(32_768))]
    );
}

/// The rulebook's `clamp_output_to_model_max`: Z.AI and `DeepSeek`'s Flash
/// models take their whole max (omp `rules/providers/deepseek.kdl:34-35`;
/// omp's Z.AI requests carry the model's max), `DeepSeek`'s other models at
/// most 64000.
#[tokio::test]
async fn a_host_rule_lifts_the_64000_ceiling() {
    let context = user_context("Hi");
    let hosted = |provider: &str, base_url: &str, id: &str, max_tokens: u64| {
        custom_model(
            base_url,
            1_000_000,
            max_tokens,
            json!({ "id": id, "provider": provider }),
        )
    };
    let zai = hosted(
        "zai",
        "https://api.z.ai/api/coding/paas/v4",
        "glm-5.3",
        131_072,
    );
    let flash = hosted(
        "deepseek",
        "https://api.deepseek.com",
        "deepseek-flash",
        384_000,
    );
    let pro = hosted(
        "deepseek",
        "https://api.deepseek.com",
        "deepseek-v4-pro",
        384_000,
    );
    assert_eq!(
        [
            caps(&capture(&zai, &context, None).await),
            caps(&capture(&flash, &context, None).await),
            caps(&capture(&pro, &context, None).await),
        ],
        [
            (Some(131_072), None),
            (Some(384_000), None),
            (Some(64_000), None)
        ]
    );
}
