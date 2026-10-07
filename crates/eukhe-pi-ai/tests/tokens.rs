//! Port of `test/tokens.test.ts`: token statistics on aborted streams.
//!
//! Every case streams from a live provider and is `#[ignore]`d with the
//! credentials it needs. TS `describe.skipIf(!process.env.X)` becomes a check
//! that fails with a clear message when `X` is missing. OAuth tokens that TS
//! resolves with `test/oauth.ts` are read from `PI_TEST_<PROVIDER>_TOKEN`.
//! TS `{ retry: 3 }` runs the case up to three times.

use std::any::Any;
use std::future::Future;
use std::panic::AssertUnwindSafe;

use eukhe_chord::context::AbortController;
use eukhe_pi_ai::compat::{get_model, get_models, stream};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{AssistantMessageEvent, Context, JsonValue, Model, StopReason};
use futures::{FutureExt, StreamExt};
use serde_json::json;

fn now() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis(),
    )
    .unwrap_or(u64::MAX)
}

fn env_value(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

/// The env var a `describe.skipIf(!process.env.X)` block needs.
fn require_env(name: &str) -> String {
    env_value(name).unwrap_or_else(|| panic!("{name} is not set; this live test needs it"))
}

/// TS `resolveApiKey(provider)` (test/oauth.ts) as `PI_TEST_<PROVIDER>_TOKEN`.
fn oauth_token(provider: &str) -> String {
    require_env(&format!(
        "PI_TEST_{}_TOKEN",
        provider.to_uppercase().replace('-', "_")
    ))
}

/// TS `hasAzureOpenAICredentials` (test/azure-utils.ts).
fn require_azure_openai_credentials() {
    assert!(
        env_value("AZURE_OPENAI_API_KEY").is_some()
            && (env_value("AZURE_OPENAI_BASE_URL").is_some()
                || env_value("AZURE_OPENAI_RESOURCE_NAME").is_some()),
        "Azure OpenAI credentials are not set (AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME)"
    );
}

/// TS `resolveAzureDeploymentName` (test/azure-utils.ts).
fn resolve_azure_deployment_name(model_id: &str) -> Option<String> {
    let map_value = env_value("AZURE_OPENAI_DEPLOYMENT_NAME_MAP")?;
    map_value.split(',').find_map(|entry| {
        let mut parts = entry.trim().split('=');
        let id = parts.next()?.trim();
        let deployment = parts.next()?.trim();
        (!id.is_empty() && !deployment.is_empty() && id == model_id).then(|| deployment.to_owned())
    })
}

/// TS `hasBedrockCredentials` (test/bedrock-utils.ts).
fn require_bedrock_credentials() {
    assert!(
        env_value("AWS_PROFILE").is_some()
            || (env_value("AWS_ACCESS_KEY_ID").is_some()
                && env_value("AWS_SECRET_ACCESS_KEY").is_some())
            || env_value("AWS_BEARER_TOKEN_BEDROCK").is_some(),
        "AWS credentials are not set (AWS_PROFILE, AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK)"
    );
}

/// TS `hasCloudflareWorkersAICredentials` (test/cloudflare-utils.ts).
fn require_cloudflare_workers_ai_credentials() {
    require_env("CLOUDFLARE_API_KEY");
    require_env("CLOUDFLARE_ACCOUNT_ID");
}

/// TS `hasCloudflareAiGatewayCredentials` (test/cloudflare-utils.ts).
fn require_cloudflare_ai_gateway_credentials() {
    require_cloudflare_workers_ai_credentials();
    require_env("CLOUDFLARE_GATEWAY_ID");
}

fn model(provider: &str, id: &str) -> Model {
    get_model(provider, id).unwrap_or_else(|| panic!("built-in model {provider}/{id}"))
}

/// TS `{ ...baseModel, api: "openai-completions" }` with `compat` dropped.
fn as_openai_completions(model: &Model) -> Model {
    let mut value = serde_json::to_value(model).expect("model json");
    let object = value.as_object_mut().expect("model object");
    object.remove("compat");
    object.insert("api".into(), json!("openai-completions"));
    serde_json::from_value(value).expect("model")
}

/// `StreamOptionsWithExtras`: `apiKey` plus provider extras.
fn options(api_key: Option<String>, extra: &JsonValue) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = api_key;
    options.extra = serde_json::from_value(extra.clone()).expect("extra");
    options
}

/// TS `{ retry }`: up to `attempts` runs; the last failure propagates.
async fn with_retry<F, Fut>(attempts: usize, mut attempt: F)
where
    F: FnMut() -> Fut,
    Fut: Future<Output = ()>,
{
    let mut last_failure: Option<Box<dyn Any + Send>> = None;
    for _ in 0..attempts {
        match AssertUnwindSafe(attempt()).catch_unwind().await {
            Ok(()) => return,
            Err(panic) => last_failure = Some(panic),
        }
    }
    if let Some(panic) = last_failure {
        std::panic::resume_unwind(panic);
    }
}

async fn test_tokens_on_abort(llm: &Model, options: ProviderStreamOptions) {
    let context: Context = serde_json::from_value(json!({
        "messages": [{
            "role": "user",
            "content": "Write a long poem with 20 stanzas about the beauty of nature.",
            "timestamp": now(),
        }],
        "systemPrompt": "You are a helpful assistant.",
    }))
    .expect("context");

    let controller = AbortController::new();
    let mut options = options;
    options.stream.request.signal = Some(controller.signal());
    let response = stream(llm, context, options).expect("stream");

    let mut abort_fired = false;
    // JS `text.length`: UTF-16 code units.
    let mut text_length = 0usize;
    let mut events = response.events();
    while let Some(event) = events.next().await {
        if abort_fired {
            continue;
        }
        if let AssistantMessageEvent::TextDelta { delta, .. }
        | AssistantMessageEvent::ThinkingDelta { delta, .. } = &event
        {
            text_length += delta.encode_utf16().count();
            if text_length >= 1000 {
                abort_fired = true;
                controller.abort(None);
            }
        }
    }
    drop(events);

    let msg = response.result().await;

    assert_eq!(msg.stop_reason, StopReason::Aborted);

    // OpenAI providers, OpenAI Codex, zai, and Amazon Bedrock only send usage in the final chunk,
    // so when aborted they have no token stats. Anthropic and Google send usage information early in the stream.
    // MiniMax and Kimi report input tokens but not output tokens differently on aborted requests.
    if matches!(
        llm.api.as_str(),
        "openai-completions"
            | "mistral-conversations"
            | "openai-responses"
            | "azure-openai-responses"
            | "openai-codex-responses"
    ) || matches!(
        llm.provider.as_str(),
        "zai" | "amazon-bedrock" | "vercel-ai-gateway"
    ) {
        assert_eq!(msg.usage.input, 0);
        assert_eq!(msg.usage.output, 0);
    } else if llm.provider == "minimax" {
        // MiniMax M2.7 does not report token usage for aborted requests.
        assert_eq!(msg.usage.input, 0);
        assert_eq!(msg.usage.output, 0);
    } else if llm.provider == "kimi-coding" {
        // Kimi reports input tokens early but output tokens only in the final chunk.
        assert!(msg.usage.input > 0);
        assert_eq!(msg.usage.output, 0);
    } else {
        assert!(msg.usage.input > 0);
        assert!(msg.usage.output > 0);

        // Some providers (Copilot) have zero cost rates
        if llm.cost.input > 0.0 {
            assert!(msg.usage.cost.input > 0.0);
            assert!(msg.usage.cost.total > 0.0);
        }
    }
}

/// Runs [`test_tokens_on_abort`] with TS `{ retry: 3 }`.
async fn run(llm: &Model, api_key: Option<&str>, extra: &JsonValue) {
    with_retry(3, || {
        test_tokens_on_abort(llm, options(api_key.map(str::to_owned), extra))
    })
    .await;
}

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn google_should_include_token_stats_when_aborted_mid_stream() {
    require_env("GEMINI_API_KEY");
    let llm = model("google", "gemini-2.5-flash");
    run(&llm, None, &json!({ "thinking": { "enabled": true } })).await;
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_completions_should_include_token_stats_when_aborted_mid_stream() {
    require_env("OPENAI_API_KEY");
    let llm = as_openai_completions(&model("openai", "gpt-4o-mini"));
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_should_include_token_stats_when_aborted_mid_stream() {
    require_env("OPENAI_API_KEY");
    let llm = model("openai", "gpt-5.4-mini");
    run(&llm, None, &json!({ "reasoningEffort": "low" })).await;
}

#[tokio::test]
#[ignore = "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored"]
async fn azure_openai_responses_should_include_token_stats_when_aborted_mid_stream() {
    require_azure_openai_credentials();
    let llm = model("azure", "gpt-4o-mini");
    let azure_options = resolve_azure_deployment_name(&llm.id)
        .map_or_else(|| json!({}), |name| json!({ "azureDeploymentName": name }));
    run(&llm, None, &azure_options).await;
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn anthropic_should_include_token_stats_when_aborted_mid_stream() {
    require_env("ANTHROPIC_API_KEY");
    let llm = model("anthropic", "claude-sonnet-4-6");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs XAI_API_KEY; run with --ignored"]
async fn xai_should_include_token_stats_when_aborted_mid_stream() {
    require_env("XAI_API_KEY");
    let llm = model("xai", "grok-4.3");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs GROQ_API_KEY; run with --ignored"]
async fn groq_should_include_token_stats_when_aborted_mid_stream() {
    require_env("GROQ_API_KEY");
    let llm = model("groq", "openai/gpt-oss-20b");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs CEREBRAS_API_KEY; run with --ignored"]
async fn cerebras_should_include_token_stats_when_aborted_mid_stream() {
    require_env("CEREBRAS_API_KEY");
    let preferred_cerebras_model_ids = ["gpt-oss-120b", "zai-glm-4.7", "llama3.1-8b"];
    let cerebras_models = get_models("cerebras");
    let llm = cerebras_models
        .iter()
        .find(|model| preferred_cerebras_model_ids.contains(&model.id.as_str()))
        .or_else(|| cerebras_models.first())
        .expect("No Cerebras models available")
        .clone();
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs CLOUDFLARE_API_KEY and CLOUDFLARE_ACCOUNT_ID; run with --ignored"]
async fn cloudflare_workers_ai_should_include_token_stats_when_aborted_mid_stream() {
    require_cloudflare_workers_ai_credentials();
    let llm = model("cloudflare-workers-ai", "@cf/moonshotai/kimi-k2.6");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs CLOUDFLARE_API_KEY, CLOUDFLARE_ACCOUNT_ID and CLOUDFLARE_GATEWAY_ID; run with --ignored"]
async fn cloudflare_ai_gateway_should_include_token_stats_when_aborted_mid_stream() {
    require_cloudflare_ai_gateway_credentials();
    let llm = model(
        "cloudflare-ai-gateway",
        "workers-ai/@cf/moonshotai/kimi-k2.6",
    );
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs HF_TOKEN; run with --ignored"]
async fn hugging_face_should_include_token_stats_when_aborted_mid_stream() {
    require_env("HF_TOKEN");
    let llm = model("huggingface", "moonshotai/Kimi-K2.5");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs TOGETHER_API_KEY; run with --ignored"]
async fn together_ai_should_include_token_stats_when_aborted_mid_stream() {
    require_env("TOGETHER_API_KEY");
    let llm = model("together", "moonshotai/Kimi-K3");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs BASETEN_API_KEY; run with --ignored"]
async fn baseten_should_include_token_stats_when_aborted_mid_stream() {
    require_env("BASETEN_API_KEY");
    let llm = model("baseten", "zai-org/GLM-5.2");
    run(&llm, None, &json!({ "reasoningEffort": "high" })).await;
}

#[tokio::test]
#[ignore = "needs ZAI_API_KEY; run with --ignored"]
async fn zai_should_include_token_stats_when_aborted_mid_stream() {
    require_env("ZAI_API_KEY");
    let llm = model("zai", "glm-5.2");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs MISTRAL_API_KEY; run with --ignored"]
async fn mistral_should_include_token_stats_when_aborted_mid_stream() {
    require_env("MISTRAL_API_KEY");
    let llm = model("mistral", "devstral-medium-latest");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs MINIMAX_API_KEY; run with --ignored"]
async fn minimax_should_include_token_stats_when_aborted_mid_stream() {
    require_env("MINIMAX_API_KEY");
    let llm = model("minimax", "MiniMax-M2.7");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs KIMI_API_KEY; run with --ignored"]
async fn kimi_for_coding_should_include_token_stats_when_aborted_mid_stream() {
    require_env("KIMI_API_KEY");
    let llm = model("kimi-coding", "kimi-for-coding");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs META_API_KEY; run with --ignored"]
async fn meta_should_include_token_stats_when_aborted_mid_stream() {
    require_env("META_API_KEY");
    let llm = model("meta", "muse-spark-1.3");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs AI_GATEWAY_API_KEY; run with --ignored"]
async fn vercel_ai_gateway_should_include_token_stats_when_aborted_mid_stream() {
    require_env("AI_GATEWAY_API_KEY");
    let llm = model("vercel-ai-gateway", "google/gemini-2.5-flash");
    run(&llm, None, &json!({})).await;
}

// FIXME(xiaomi): Xiaomi's Anthropic-compatible stream does not populate
// usage in the message_start event the way Anthropic does — usage only
// arrives at message_stop. Aborting mid-stream therefore loses input/output
// token counts. Non-streaming usage works (see total_tokens.rs).
// Re-enable once upstream sends usage in message_start.
#[tokio::test]
#[ignore = "it.skip upstream (FIXME xiaomi: no usage in message_start); needs XIAOMI_API_KEY; run with --ignored"]
async fn xiaomi_should_include_token_stats_when_aborted_mid_stream() {
    require_env("XIAOMI_API_KEY");
    let llm = model("xiaomi", "mimo-v2.5-pro");
    run(&llm, None, &json!({})).await;
}

// FIXME(xiaomi): see the API-billing case above — same upstream streaming
// usage limitation applies to Token Plan endpoints.
#[tokio::test]
#[ignore = "it.skip upstream (FIXME xiaomi: no usage in message_start); needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_cn_should_include_token_stats_when_aborted_mid_stream() {
    require_env("XIAOMI_TOKEN_PLAN_CN_API_KEY");
    let llm = model("xiaomi-token-plan-cn", "mimo-v2.5-pro");
    run(&llm, None, &json!({})).await;
}

// FIXME(xiaomi): see the API-billing case above.
#[tokio::test]
#[ignore = "it.skip upstream (FIXME xiaomi: no usage in message_start); needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_ams_should_include_token_stats_when_aborted_mid_stream() {
    require_env("XIAOMI_TOKEN_PLAN_AMS_API_KEY");
    let llm = model("xiaomi-token-plan-ams", "mimo-v2.5-pro");
    run(&llm, None, &json!({})).await;
}

// FIXME(xiaomi): see the API-billing case above.
#[tokio::test]
#[ignore = "it.skip upstream (FIXME xiaomi: no usage in message_start); needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_sgp_should_include_token_stats_when_aborted_mid_stream() {
    require_env("XIAOMI_TOKEN_PLAN_SGP_API_KEY");
    let llm = model("xiaomi-token-plan-sgp", "mimo-v2.5-pro");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_should_include_token_stats_when_aborted_mid_stream() {
    require_env("QWEN_TOKEN_PLAN_API_KEY");
    let llm = model("qwen-token-plan", "qwen3.7-max");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_individual_should_include_token_stats_when_aborted_mid_stream() {
    require_env("QWEN_TOKEN_PLAN_API_KEY");
    let llm = model("qwen-token-plan-individual", "qwen3.8-max");
    run(&llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn qwen_token_plan_cn_should_include_token_stats_when_aborted_mid_stream() {
    require_env("QWEN_TOKEN_PLAN_CN_API_KEY");
    let llm = model("qwen-token-plan-cn", "qwen3.7-max");
    run(&llm, None, &json!({})).await;
}

// OAuth-based providers (TS: credentials from ~/.pi/agent/oauth.json).

#[tokio::test]
#[ignore = "needs PI_TEST_ANTHROPIC_TOKEN (Anthropic OAuth); run with --ignored"]
async fn anthropic_oauth_should_include_token_stats_when_aborted_mid_stream() {
    let token = oauth_token("anthropic");
    let llm = model("anthropic", "claude-sonnet-4-6");
    run(&llm, Some(&token), &json!({})).await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored"]
async fn github_copilot_claude_haiku_4_5_should_include_token_stats_when_aborted_mid_stream() {
    let token = oauth_token("github-copilot");
    let llm = model("github-copilot", "claude-haiku-4.5");
    run(&llm, Some(&token), &json!({})).await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored"]
async fn github_copilot_claude_sonnet_4_should_include_token_stats_when_aborted_mid_stream() {
    let token = oauth_token("github-copilot");
    let llm = model("github-copilot", "claude-sonnet-4.6");
    run(&llm, Some(&token), &json!({})).await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_OPENAI_CODEX_TOKEN; run with --ignored"]
async fn openai_codex_gpt_5_5_should_include_token_stats_when_aborted_mid_stream() {
    let token = oauth_token("openai-codex");
    let llm = model("openai-codex", "gpt-5.5");
    run(&llm, Some(&token), &json!({})).await;
}

#[tokio::test]
#[ignore = "needs AWS_PROFILE, AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored"]
async fn amazon_bedrock_should_include_token_stats_when_aborted_mid_stream() {
    require_bedrock_credentials();
    let llm = model(
        "amazon-bedrock",
        "global.anthropic.claude-sonnet-4-5-20250929-v1:0",
    );
    run(&llm, None, &json!({})).await;
}
