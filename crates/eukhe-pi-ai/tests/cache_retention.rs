//! Port of `test/cache-retention.test.ts`.
//!
//! The TS `beforeEach` deletes `PI_CACHE_RETENTION` from `process.env` and
//! single cases set it to `"long"`. Here every request carries the scoped
//! `env` option instead of mutating the process environment (concurrent
//! tests share it): `PI_CACHE_RETENTION: "long"` where TS sets it, and
//! `PI_CACHE_RETENTION: "short"` otherwise, which every API resolves exactly
//! like an unset variable (only `"long"` opts in) and which shadows a value
//! inherited from the process environment.
//!
//! As in TS, `onPayload` records the payload and throws "payload captured",
//! so no request leaves the process.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::api::{anthropic_messages, openai_completions, openai_responses};
use eukhe_pi_ai::providers::all::get_builtin_model;
use eukhe_pi_ai::types::{OnPayload, ProviderStreamOptions};
use eukhe_pi_ai::utils::diagnostics::ErrorObject;
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    CacheRetention, Context, JsonValue, Model, ProviderEnv, TranscriptContext,
};
use serde_json::json;

/// A chat API module's `stream` function.
type StreamFn =
    fn(&Model, &TranscriptContext, ProviderStreamOptions) -> AssistantMessageEventStream;

type Captured = Arc<Mutex<Option<JsonValue>>>;

/// `Date.now()`.
fn now() -> u64 {
    let elapsed = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock after epoch");
    u64::try_from(elapsed.as_millis()).expect("epoch milliseconds fit u64")
}

/// The shared `normalizeContext({ systemPrompt, messages })` of the suite.
fn raw_context() -> Context {
    serde_json::from_value(json!({
        "systemPrompt": "You are a helpful assistant.",
        "messages": [{ "role": "user", "content": "Hello", "timestamp": now() }],
    }))
    .expect("context")
}

fn context() -> TranscriptContext {
    normalize_context(raw_context())
}

/// TS `getModel(provider, id)`.
fn get_model(provider: &str, id: &str) -> Model {
    get_builtin_model(provider, id).unwrap_or_else(|| panic!("no built-in model {provider}/{id}"))
}

/// TS `{ ...model, ...overrides }`.
// Test helpers take literal JSON by value, mirroring the TS call shape.
#[allow(clippy::needless_pass_by_value)]
fn with_overrides(model: &Model, overrides: JsonValue) -> Model {
    let mut value = serde_json::to_value(model).expect("serialize model");
    let object = value.as_object_mut().expect("model object");
    for (key, override_value) in overrides.as_object().expect("overrides object") {
        object.insert(key.clone(), override_value.clone());
    }
    serde_json::from_value(value).expect("model")
}

/// TS `stopAfterPayload(capture)`: records the payload, then throws
/// `PayloadCaptured`.
fn stop_after_payload() -> (OnPayload<Model>, Captured) {
    let captured: Captured = Arc::default();
    let sink = Arc::clone(&captured);
    let on_payload: OnPayload<Model> = Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async { Err(ErrorObject::named("PayloadCaptured", "payload captured").thrown()) })
    });
    (on_payload, captured)
}

/// `PI_CACHE_RETENTION` as the test leaves it.
#[derive(Clone, Copy)]
enum PiCacheRetention {
    /// Deleted by `beforeEach`.
    Unset,
    /// `process.env.PI_CACHE_RETENTION = "long"`.
    Long,
}

fn pi_cache_retention_env(value: PiCacheRetention) -> ProviderEnv {
    let value = match value {
        PiCacheRetention::Unset => "short",
        PiCacheRetention::Long => "long",
    };
    ProviderEnv::from([("PI_CACHE_RETENTION".to_owned(), value.to_owned())])
}

/// The options of one captured request.
struct Request {
    api_key: &'static str,
    cache_retention: Option<CacheRetention>,
    session_id: Option<&'static str>,
    env: PiCacheRetention,
}

impl Request {
    fn with_key(api_key: &'static str) -> Self {
        Self {
            api_key,
            cache_retention: None,
            session_id: None,
            env: PiCacheRetention::Unset,
        }
    }

    fn cache_retention(mut self, cache_retention: CacheRetention) -> Self {
        self.cache_retention = Some(cache_retention);
        self
    }

    fn session_id(mut self, session_id: &'static str) -> Self {
        self.session_id = Some(session_id);
        self
    }

    fn env(mut self, env: PiCacheRetention) -> Self {
        self.env = env;
        self
    }
}

/// Streams with `stopAfterPayload`, drains the (failing) stream, and returns
/// the captured payload.
async fn capture(
    stream: StreamFn,
    model: &Model,
    context: &TranscriptContext,
    request: Request,
) -> Option<JsonValue> {
    let (on_payload, captured) = stop_after_payload();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some(request.api_key.to_owned());
    options.stream.request.env = Some(pi_cache_retention_env(request.env));
    options.stream.request.on_payload = Some(on_payload);
    options.stream.cache_retention = request.cache_retention;
    options.stream.session_id = request.session_id.map(str::to_owned);
    stream(model, context, options).result().await;
    let payload = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take();
    payload
}

/// Live variant through the compat `stream` (env API key injection).
async fn capture_live(model: &Model, env: PiCacheRetention) -> Option<JsonValue> {
    let (on_payload, captured) = stop_after_payload();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.env = Some(pi_cache_retention_env(env));
    options.stream.request.on_payload = Some(on_payload);
    eukhe_pi_ai::compat::stream(model, raw_context(), options)
        .expect("stream")
        .result()
        .await;
    let payload = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take();
    payload
}

fn require_env(name: &str) {
    assert!(
        std::env::var_os(name).is_some_and(|value| !value.is_empty()),
        "{name} must be set to run this test"
    );
}

/// TS `expect(value).toBeUndefined()` on a payload field.
#[track_caller]
fn assert_absent(payload: &JsonValue, key: &str) {
    assert_eq!(payload.get(key), None, "{key} must be absent: {payload}");
}

// ---------------------------------------------------------------------------
// Anthropic Provider
// ---------------------------------------------------------------------------

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn anthropic_should_use_default_cache_ttl_no_ttl_field_when_pi_cache_retention_is_not_set() {
    require_env("ANTHROPIC_API_KEY");
    let model = get_model("anthropic", "claude-haiku-4-5");

    let payload = capture_live(&model, PiCacheRetention::Unset)
        .await
        .expect("payload captured");

    assert!(payload.get("system").is_some());
    assert_eq!(
        payload["system"][0]["cache_control"],
        json!({ "type": "ephemeral" })
    );
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn anthropic_should_use_1h_cache_ttl_when_pi_cache_retention_long() {
    require_env("ANTHROPIC_API_KEY");
    let model = get_model("anthropic", "claude-haiku-4-5");

    let payload = capture_live(&model, PiCacheRetention::Long)
        .await
        .expect("payload captured");

    assert!(payload.get("system").is_some());
    assert_eq!(
        payload["system"][0]["cache_control"],
        json!({ "type": "ephemeral", "ttl": "1h" })
    );
}

#[tokio::test]
async fn anthropic_should_add_ttl_for_non_api_anthropic_com_base_url_by_default() {
    let base_model = get_model("anthropic", "claude-haiku-4-5");
    let proxy_model = with_overrides(
        &base_model,
        json!({ "baseUrl": "https://my-proxy.example.com/v1" }),
    );

    let payload = capture(
        anthropic_messages::stream,
        &proxy_model,
        &context(),
        Request::with_key("fake-key").env(PiCacheRetention::Long),
    )
    .await
    .expect("payload captured");

    assert_eq!(
        payload["system"][0]["cache_control"],
        json!({ "type": "ephemeral", "ttl": "1h" })
    );
}

#[tokio::test]
async fn anthropic_should_omit_ttl_when_supports_long_cache_retention_is_false() {
    let base_model = get_model("anthropic", "claude-haiku-4-5");
    let proxy_model = with_overrides(
        &base_model,
        json!({
            "baseUrl": "https://my-proxy.example.com/v1",
            "compat": { "supportsLongCacheRetention": false },
        }),
    );

    let payload = capture(
        anthropic_messages::stream,
        &proxy_model,
        &context(),
        Request::with_key("fake-key").cache_retention(CacheRetention::Long),
    )
    .await
    .expect("payload captured");

    assert_eq!(
        payload["system"][0]["cache_control"],
        json!({ "type": "ephemeral" })
    );
}

#[tokio::test]
async fn anthropic_should_omit_cache_control_when_cache_retention_is_none() {
    let base_model = get_model("anthropic", "claude-haiku-4-5");

    let payload = capture(
        anthropic_messages::stream,
        &base_model,
        &context(),
        Request::with_key("fake-key").cache_retention(CacheRetention::None),
    )
    .await
    .expect("payload captured");

    assert_eq!(payload["system"][0].get("cache_control"), None);
}

#[tokio::test]
async fn anthropic_should_add_cache_control_to_string_user_messages() {
    let base_model = get_model("anthropic", "claude-haiku-4-5");

    let payload = capture(
        anthropic_messages::stream,
        &base_model,
        &context(),
        Request::with_key("fake-key"),
    )
    .await
    .expect("payload captured");

    let last_message = payload["messages"]
        .as_array()
        .and_then(|messages| messages.last())
        .expect("last message");
    let content = last_message["content"]
        .as_array()
        .expect("content is an array");
    let last_block = content.last().expect("last block");
    assert_eq!(last_block["cache_control"], json!({ "type": "ephemeral" }));
}

#[tokio::test]
async fn anthropic_should_set_1h_cache_ttl_when_cache_retention_is_long() {
    let base_model = get_model("anthropic", "claude-haiku-4-5");

    let payload = capture(
        anthropic_messages::stream,
        &base_model,
        &context(),
        Request::with_key("fake-key").cache_retention(CacheRetention::Long),
    )
    .await
    .expect("payload captured");

    assert_eq!(
        payload["system"][0]["cache_control"],
        json!({ "type": "ephemeral", "ttl": "1h" })
    );
}

// ---------------------------------------------------------------------------
// OpenAI Responses Provider
// ---------------------------------------------------------------------------

#[test]
fn openai_responses_does_not_enable_cache_warming_from_the_documented_ttl_alone() {
    for model_id in [
        "gpt-5.6-luna",
        "gpt-5.6-sol",
        "gpt-5.6-terra",
        "gpt-6-astra",
        "gpt-6-luna",
        "gpt-6-sol",
    ] {
        assert_eq!(
            get_model("openai", model_id).prompt_cache,
            None,
            "{model_id}"
        );
    }
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_should_not_set_prompt_cache_retention_when_pi_cache_retention_is_not_set()
{
    require_env("OPENAI_API_KEY");
    let model = get_model("openai", "gpt-4o-mini");

    let payload = capture_live(&model, PiCacheRetention::Unset)
        .await
        .expect("payload captured");

    assert_absent(&payload, "prompt_cache_retention");
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_should_set_prompt_cache_retention_to_24h_when_pi_cache_retention_long() {
    require_env("OPENAI_API_KEY");
    let model = get_model("openai", "gpt-4o-mini");

    let payload = capture_live(&model, PiCacheRetention::Long)
        .await
        .expect("payload captured");

    assert_eq!(payload["prompt_cache_retention"], json!("24h"));
}

#[tokio::test]
async fn openai_responses_should_set_prompt_cache_retention_for_non_api_openai_com_base_url_by_default(
) {
    let base_model = get_model("openai", "gpt-4o-mini");
    let proxy_model = with_overrides(
        &base_model,
        json!({ "baseUrl": "https://my-proxy.example.com/v1" }),
    );

    let payload = capture(
        openai_responses::stream,
        &proxy_model,
        &context(),
        Request::with_key("sk-fake-key").env(PiCacheRetention::Long),
    )
    .await
    .expect("payload captured");

    assert_eq!(payload["prompt_cache_retention"], json!("24h"));
}

#[tokio::test]
async fn openai_responses_should_omit_prompt_cache_retention_when_supports_long_cache_retention_is_false(
) {
    let model = with_overrides(
        &get_model("openai", "gpt-4o-mini"),
        json!({ "compat": { "supportsLongCacheRetention": false } }),
    );

    let payload = capture(
        openai_responses::stream,
        &model,
        &context(),
        Request::with_key("sk-fake-key")
            .cache_retention(CacheRetention::Long)
            .session_id("session-compat-false"),
    )
    .await
    .expect("payload captured");

    assert_absent(&payload, "prompt_cache_retention");
}

#[tokio::test]
async fn openai_responses_should_omit_prompt_cache_key_and_disable_implicit_writes_when_cache_retention_is_none(
) {
    let model = get_model("openai", "gpt-5.6-sol");

    let payload = capture(
        openai_responses::stream,
        &model,
        &context(),
        Request::with_key("sk-fake-key")
            .cache_retention(CacheRetention::None)
            .session_id("session-1"),
    )
    .await
    .expect("payload captured");

    assert_absent(&payload, "prompt_cache_key");
    assert_absent(&payload, "prompt_cache_retention");
    assert_eq!(
        payload["prompt_cache_options"],
        json!({ "mode": "explicit" })
    );
}

#[tokio::test]
async fn openai_responses_should_omit_prompt_cache_options_for_models_that_reject_it() {
    let model = get_model("openai", "gpt-4o-mini");

    let payload = capture(
        openai_responses::stream,
        &model,
        &context(),
        Request::with_key("sk-fake-key")
            .cache_retention(CacheRetention::None)
            .session_id("session-1"),
    )
    .await
    .expect("payload captured");

    assert_absent(&payload, "prompt_cache_key");
    assert_absent(&payload, "prompt_cache_options");
}

async fn should_use_the_supported_long_cache_field_for(
    model_id: &str,
    retention: Option<&str>,
    cache_options: Option<JsonValue>,
) {
    let model = get_model("openai", model_id);

    let payload = capture(
        openai_responses::stream,
        &model,
        &context(),
        Request::with_key("sk-fake-key")
            .cache_retention(CacheRetention::Long)
            .session_id("session-2"),
    )
    .await
    .unwrap_or(JsonValue::Null);

    assert_eq!(payload.get("prompt_cache_key"), Some(&json!("session-2")));
    assert_eq!(
        payload.get("prompt_cache_retention"),
        retention.map(|retention| json!(retention)).as_ref()
    );
    assert_eq!(payload.get("prompt_cache_options"), cache_options.as_ref());
}

#[tokio::test]
async fn openai_responses_should_use_the_supported_long_cache_field_for_gpt_4o_mini() {
    should_use_the_supported_long_cache_field_for("gpt-4o-mini", Some("24h"), None).await;
}

#[tokio::test]
async fn openai_responses_should_use_the_supported_long_cache_field_for_gpt_6_astra() {
    should_use_the_supported_long_cache_field_for(
        "gpt-6-astra",
        None,
        Some(json!({ "ttl": "30m" })),
    )
    .await;
}

#[tokio::test]
async fn openai_responses_should_use_the_supported_long_cache_field_for_gpt_6_sol() {
    should_use_the_supported_long_cache_field_for("gpt-6-sol", None, Some(json!({ "ttl": "30m" })))
        .await;
}

#[tokio::test]
async fn openai_responses_should_use_the_supported_long_cache_field_for_gpt_6_luna() {
    should_use_the_supported_long_cache_field_for(
        "gpt-6-luna",
        None,
        Some(json!({ "ttl": "30m" })),
    )
    .await;
}

// ---------------------------------------------------------------------------
// OpenAI Completions Provider
// ---------------------------------------------------------------------------

/// TS `createCompletionsModel(compat)`.
fn create_completions_model(compat: Option<JsonValue>) -> Model {
    let mut value = json!({
        "id": "test-model",
        "name": "Test Model",
        "api": "openai-completions",
        "provider": "test-openai-completions",
        "baseUrl": "https://my-proxy.example.com/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 4096,
    });
    if let Some(compat) = compat {
        value["compat"] = compat;
    }
    serde_json::from_value(value).expect("model")
}

/// `model.compat?.[key]` (`Null` when unset).
fn compat_field(model: &Model, key: &str) -> JsonValue {
    serde_json::to_value(model).expect("serialize model")["compat"][key].clone()
}

#[tokio::test]
async fn openai_completions_should_set_prompt_cache_retention_for_non_api_openai_com_base_url_by_default(
) {
    let payload = capture(
        openai_completions::stream,
        &create_completions_model(None),
        &context(),
        Request::with_key("fake-key")
            .cache_retention(CacheRetention::Long)
            .session_id("session-completions"),
    )
    .await
    .expect("payload captured");

    assert_eq!(payload["prompt_cache_key"], json!("session-completions"));
    assert_eq!(payload["prompt_cache_retention"], json!("24h"));
}

#[tokio::test]
async fn openai_completions_should_omit_prompt_cache_retention_when_supports_long_cache_retention_is_false(
) {
    let payload = capture(
        openai_completions::stream,
        &create_completions_model(Some(json!({ "supportsLongCacheRetention": false }))),
        &context(),
        Request::with_key("fake-key")
            .cache_retention(CacheRetention::Long)
            .session_id("session-completions-false"),
    )
    .await
    .expect("payload captured");

    assert_absent(&payload, "prompt_cache_key");
    assert_absent(&payload, "prompt_cache_retention");
}

async fn should_omit_long_cache_retention_for(provider: &str, id: &str) {
    let model = get_model(provider, id);

    let payload = capture(
        openai_completions::stream,
        &model,
        &context(),
        Request::with_key("fake-key")
            .cache_retention(CacheRetention::Long)
            .session_id("session-opencode-long-cache-unsupported"),
    )
    .await;

    assert_eq!(
        compat_field(&model, "supportsLongCacheRetention"),
        json!(false)
    );
    let payload = payload.expect("payload captured");
    assert_absent(&payload, "prompt_cache_key");
    assert_absent(&payload, "prompt_cache_retention");
}

#[tokio::test]
async fn openai_completions_should_omit_long_cache_retention_for_opencode_deepseek_v4_flash() {
    should_omit_long_cache_retention_for("opencode", "deepseek-v4-flash").await;
}

#[tokio::test]
async fn openai_completions_should_omit_long_cache_retention_for_opencode_deepseek_v4_pro() {
    should_omit_long_cache_retention_for("opencode", "deepseek-v4-pro").await;
}

#[tokio::test]
async fn openai_completions_should_omit_long_cache_retention_for_opencode_kimi_k2_5() {
    should_omit_long_cache_retention_for("opencode", "kimi-k2.5").await;
}

#[tokio::test]
async fn openai_completions_should_omit_long_cache_retention_for_opencode_kimi_k2_6() {
    should_omit_long_cache_retention_for("opencode", "kimi-k2.6").await;
}

#[tokio::test]
async fn openai_completions_should_omit_long_cache_retention_for_opencode_minimax_m2_7() {
    should_omit_long_cache_retention_for("opencode", "minimax-m2.7").await;
}

async fn should_omit_strict_field_on_tools_for_cerebras(id: &str) {
    let model = get_model("cerebras", id);
    let context_with_tools: Context = serde_json::from_value(json!({
        "messages": [
            {
                "role": "system",
                "content": "test",
                "toolsAdded": [
                    {
                        "name": "t1",
                        "description": "strict tool",
                        "parameters": {
                            "type": "object",
                            "properties": { "x": { "type": "string" } },
                            "required": ["x"],
                        },
                        // TS `{ type: "json_schema" }` (cast `as any`); the
                        // typed config requires `strict`, and `"prefer"` is
                        // the variant that does not demand strict support.
                        "constrainedSampling": { "type": "json_schema", "strict": "prefer" },
                    },
                    {
                        "name": "t2",
                        "description": "non-strict tool",
                        "parameters": {
                            "type": "object",
                            "properties": { "y": { "type": "string" } },
                            "required": ["y"],
                        },
                    },
                ],
                "timestamp": 0,
            },
            { "role": "user", "content": "hello", "timestamp": 1 },
        ],
    }))
    .expect("context");

    let payload = capture(
        openai_completions::stream,
        &model,
        &normalize_context(context_with_tools),
        Request::with_key("fake-key").session_id("test"),
    )
    .await;

    assert_eq!(compat_field(&model, "supportsStrictMode"), JsonValue::Null);
    let payload = payload.expect("payload captured");
    let tools = payload["tools"].as_array().expect("tools");
    for tool in tools {
        assert_eq!(tool["function"].get("strict"), None, "{tool}");
    }
}

#[tokio::test]
async fn openai_completions_should_omit_strict_field_on_tools_for_cerebras_gpt_oss_120b() {
    should_omit_strict_field_on_tools_for_cerebras("gpt-oss-120b").await;
}

#[tokio::test]
async fn openai_completions_should_omit_strict_field_on_tools_for_cerebras_qwen_3_8_27b() {
    should_omit_strict_field_on_tools_for_cerebras("qwen-3.8-27b").await;
}
