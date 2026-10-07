//! Port of `openai-completions-prompt-cache.test.ts`. The TS fake records the
//! client's `defaultHeaders`; here the headers of the sent HTTP request are
//! inspected. `PI_CACHE_RETENTION` is passed through the `env` option instead
//! of mutating the process environment.

use serde_json::json;

use super::support::{context, model, run_with_chunks, stop_chunks};
use crate::api::openai_completions::OpenAICompletionsOptions;
use crate::api::system_one_shared::test_fetch::Recorded;
use crate::providers::all::get_builtin_model;
use crate::types::{
    CacheRetention, JsonValue, Model, ProviderEnv, ProviderHeaders, ProviderRequestOptions,
    StreamOptions,
};

/// TS `createModel(overrides)`: `gpt-4o-mini` without its compat, as an
/// `openai-completions` model, with `overrides` merged on top.
// Test helpers take literal JSON by value, mirroring the TS call shape.
#[allow(clippy::needless_pass_by_value)]
fn create_model(overrides: JsonValue) -> Model {
    let base = get_builtin_model("openai", "gpt-4o-mini").expect("catalog model");
    let mut value = serde_json::to_value(&base).expect("serialize model");
    let object = value.as_object_mut().expect("model object");
    object.remove("compat");
    object.insert("api".into(), json!("openai-completions"));
    if let Some(overrides) = overrides.as_object() {
        for (key, value) in overrides {
            object.insert(key.clone(), value.clone());
        }
    }
    model(value)
}

#[derive(Default)]
struct CaptureOptions {
    cache_retention: Option<CacheRetention>,
    session_id: Option<String>,
    headers: Option<ProviderHeaders>,
    env: Option<ProviderEnv>,
}

/// TS `captureRequest(options, model)`: the payload and the sent request.
async fn capture_request(options: CaptureOptions, model: &Model) -> (JsonValue, Recorded) {
    let ctx = context(json!({
        "systemPrompt": "sys",
        "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
    }));
    let options = OpenAICompletionsOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test-key".to_owned()),
                headers: options.headers,
                // TS `delete process.env.PI_CACHE_RETENTION` in `beforeEach`.
                env: Some(options.env.unwrap_or_default()),
                ..ProviderRequestOptions::default()
            },
            cache_retention: options.cache_retention,
            session_id: options.session_id,
            ..StreamOptions::default()
        },
        ..OpenAICompletionsOptions::default()
    };
    let (request, _, message) = run_with_chunks(model, &ctx, options, stop_chunks()).await;
    let request =
        request.unwrap_or_else(|| panic!("no request was sent: {:?}", message.error_message));
    (request.json(), request)
}

fn session(session_id: &str) -> CaptureOptions {
    CaptureOptions {
        session_id: Some(session_id.to_owned()),
        ..CaptureOptions::default()
    }
}

#[tokio::test]
async fn sets_prompt_cache_key_for_direct_openai_requests_when_caching_is_enabled() {
    let (payload, _) = capture_request(session("session-123"), &create_model(json!({}))).await;

    assert_eq!(payload.get("prompt_cache_key"), Some(&json!("session-123")));
    assert_eq!(payload.get("prompt_cache_retention"), None);
}

#[tokio::test]
async fn sets_prompt_cache_retention_to_24h_for_direct_openai_requests_when_cache_retention_is_long(
) {
    let (payload, _) = capture_request(
        CaptureOptions {
            cache_retention: Some(CacheRetention::Long),
            ..session("session-456")
        },
        &create_model(json!({})),
    )
    .await;

    assert_eq!(payload.get("prompt_cache_key"), Some(&json!("session-456")));
    assert_eq!(payload.get("prompt_cache_retention"), Some(&json!("24h")));
}

#[tokio::test]
async fn clamps_prompt_cache_key_to_openais_64_character_limit() {
    let session_id = "x".repeat(67);
    let (payload, _) = capture_request(session(&session_id), &create_model(json!({}))).await;

    assert_eq!(
        payload.get("prompt_cache_key"),
        Some(&json!("x".repeat(64)))
    );
}

#[tokio::test]
async fn omits_prompt_cache_fields_when_cache_retention_is_none() {
    let (payload, _) = capture_request(
        CaptureOptions {
            cache_retention: Some(CacheRetention::None),
            ..session("session-789")
        },
        &create_model(json!({})),
    )
    .await;

    assert_eq!(payload.get("prompt_cache_key"), None);
    assert_eq!(payload.get("prompt_cache_retention"), None);
}

#[tokio::test]
async fn omits_prompt_cache_fields_for_non_openai_base_urls_without_compatible_long_retention() {
    let model = create_model(json!({
        "baseUrl": "https://proxy.example.com/v1",
        "compat": { "supportsLongCacheRetention": false },
    }));
    let (payload, _) = capture_request(
        CaptureOptions {
            cache_retention: Some(CacheRetention::Long),
            ..session("session-proxy")
        },
        &model,
    )
    .await;

    assert_eq!(payload.get("prompt_cache_key"), None);
    assert_eq!(payload.get("prompt_cache_retention"), None);
}

#[tokio::test]
async fn uses_pi_cache_retention_for_direct_openai_requests() {
    let (payload, _) = capture_request(
        CaptureOptions {
            env: Some(ProviderEnv::from([(
                "PI_CACHE_RETENTION".to_owned(),
                "long".to_owned(),
            )])),
            ..session("session-env")
        },
        &create_model(json!({})),
    )
    .await;

    assert_eq!(payload.get("prompt_cache_key"), Some(&json!("session-env")));
    assert_eq!(payload.get("prompt_cache_retention"), Some(&json!("24h")));
}

#[tokio::test]
async fn sends_known_session_affinity_headers_when_compat_send_session_affinity_headers_is_enabled()
{
    let model = create_model(json!({
        "baseUrl": "https://proxy.example.com/v1",
        "compat": { "sendSessionAffinityHeaders": true },
    }));
    let (_, request) = capture_request(session("session-affinity"), &model).await;

    assert_eq!(request.header("session_id"), Some("session-affinity"));
    assert_eq!(
        request.header("x-client-request-id"),
        Some("session-affinity")
    );
    assert_eq!(
        request.header("x-session-affinity"),
        Some("session-affinity")
    );
}

async fn sends_fireworks_session_affinity_for(model_id: &str) {
    let model = get_builtin_model("fireworks", model_id).expect("catalog model");
    let (_, request) = capture_request(session("fireworks-session"), &model).await;

    assert_eq!(
        request.header("x-session-affinity"),
        Some("fireworks-session")
    );
}

#[tokio::test]
async fn sends_fireworks_session_affinity_for_glm_5p3() {
    sends_fireworks_session_affinity_for("accounts/fireworks/models/glm-5p3").await;
}

#[tokio::test]
async fn sends_fireworks_session_affinity_for_glm_5p3_fast() {
    sends_fireworks_session_affinity_for("accounts/fireworks/routers/glm-5p3-fast").await;
}

#[tokio::test]
async fn sends_baseten_session_affinity_for_built_in_catalog_models() {
    let model = get_builtin_model("baseten", "zai-org/GLM-5.2").expect("catalog model");
    let (_, request) = capture_request(session("baseten-catalog-session"), &model).await;

    assert_eq!(
        request.header("x-session-affinity"),
        Some("baseten-catalog-session")
    );
    assert_eq!(
        request.header("x-client-request-id"),
        Some("baseten-catalog-session")
    );
}

#[tokio::test]
async fn uses_openai_no_session_format_when_configured() {
    let model = create_model(json!({
        "compat": { "sendSessionAffinityHeaders": true, "sessionAffinityFormat": "openai-nosession" },
    }));
    let (payload, request) = capture_request(session("session-nosession"), &model).await;

    assert_eq!(payload.get("session_id"), None);
    assert_eq!(
        payload.get("prompt_cache_key"),
        Some(&json!("session-nosession"))
    );
    assert_eq!(request.header("session_id"), None);
    assert_eq!(
        request.header("x-client-request-id"),
        Some("session-nosession")
    );
    assert_eq!(
        request.header("x-session-affinity"),
        Some("session-nosession")
    );
    assert_eq!(request.header("x-session-id"), None);
}

#[tokio::test]
async fn uses_openrouter_session_affinity_header_when_configured() {
    let model = create_model(json!({
        "baseUrl": "https://proxy.example.com/v1",
        "compat": { "sendSessionAffinityHeaders": true, "sessionAffinityFormat": "openrouter" },
    }));
    let (payload, request) = capture_request(session("session-proxy"), &model).await;

    assert_eq!(payload.get("session_id"), None);
    assert_eq!(payload.get("prompt_cache_key"), None);
    assert_eq!(request.header("x-session-id"), Some("session-proxy"));
    assert_eq!(request.header("session_id"), None);
    assert_eq!(request.header("x-client-request-id"), None);
    assert_eq!(request.header("x-session-affinity"), None);
}

#[tokio::test]
async fn sends_openrouter_session_affinity_header_by_default_for_built_in_openrouter_models() {
    let model = get_builtin_model("openrouter", "auto").expect("catalog model");
    let (payload, request) = capture_request(session("session-openrouter"), &model).await;

    assert_eq!(payload.get("session_id"), None);
    assert_eq!(payload.get("prompt_cache_key"), None);
    assert_eq!(request.header("x-session-id"), Some("session-openrouter"));
    assert_eq!(request.header("session_id"), None);
    assert_eq!(request.header("x-client-request-id"), None);
    assert_eq!(request.header("x-session-affinity"), None);
}

#[tokio::test]
async fn omits_openrouter_session_affinity_data_when_disabled() {
    let model = create_model(json!({
        "provider": "openrouter",
        "baseUrl": "https://openrouter.ai/api/v1",
        "compat": { "sendSessionAffinityHeaders": false },
    }));
    let (payload, request) = capture_request(session("session-openrouter"), &model).await;

    assert_eq!(payload.get("session_id"), None);
    assert_eq!(payload.get("prompt_cache_key"), None);
    assert_eq!(request.header("x-session-id"), None);
}

#[tokio::test]
async fn omits_session_affinity_headers_when_cache_retention_is_none() {
    let model = create_model(json!({
        "baseUrl": "https://proxy.example.com/v1",
        "compat": { "sendSessionAffinityHeaders": true },
    }));
    let (_, request) = capture_request(
        CaptureOptions {
            cache_retention: Some(CacheRetention::None),
            ..session("session-affinity")
        },
        &model,
    )
    .await;

    assert_eq!(request.header("session_id"), None);
    assert_eq!(request.header("x-client-request-id"), None);
    assert_eq!(request.header("x-session-affinity"), None);
}

#[tokio::test]
async fn lets_explicit_headers_override_generated_session_affinity_headers() {
    let model = create_model(json!({
        "baseUrl": "https://proxy.example.com/v1",
        "compat": { "sendSessionAffinityHeaders": true },
    }));
    let headers = ProviderHeaders::from([
        ("session_id".to_owned(), Some("override-session".to_owned())),
        (
            "x-client-request-id".to_owned(),
            Some("override-request".to_owned()),
        ),
        (
            "x-session-affinity".to_owned(),
            Some("override-affinity".to_owned()),
        ),
    ]);
    let (_, request) = capture_request(
        CaptureOptions {
            headers: Some(headers),
            ..session("session-affinity")
        },
        &model,
    )
    .await;

    assert_eq!(request.header("session_id"), Some("override-session"));
    assert_eq!(
        request.header("x-client-request-id"),
        Some("override-request")
    );
    assert_eq!(
        request.header("x-session-affinity"),
        Some("override-affinity")
    );
}
