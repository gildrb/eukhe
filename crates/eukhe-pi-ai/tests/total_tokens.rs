//! Port of `test/total-tokens.test.ts`: `totalTokens` across all providers.
//!
//! totalTokens represents the total number of tokens processed by the LLM,
//! including input (with cache) and output (with thinking). This is the
//! base for calculating context size for the next request.
//!
//! - `OpenAI` Completions: Uses native `total_tokens` field
//! - `OpenAI` Responses: Uses native `total_tokens` field
//! - Google: Uses native `totalTokenCount` field
//! - Anthropic: Computed as input + output + cacheRead + cacheWrite
//! - Other `OpenAI`-compatible providers: Uses native `total_tokens` field
//!
//! Every case talks to a live provider and is `#[ignore]`d with the
//! credentials it needs. TS `describe.skipIf(!process.env.X)` becomes a check
//! that fails with a clear message when `X` is missing. OAuth tokens that TS
//! resolves with `test/oauth.ts` are read from `PI_TEST_<PROVIDER>_TOKEN`.
//! TS `{ retry: 3 }` runs the case up to three times.

use std::any::Any;
use std::future::Future;
use std::panic::AssertUnwindSafe;
use std::sync::LazyLock;

use eukhe_pi_ai::compat::{complete, get_model};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{Context, JsonValue, Message, Model, StopReason, Usage};
use futures::FutureExt;
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

/// Generate a long system prompt to trigger caching (>2k bytes for most providers)
static LONG_SYSTEM_PROMPT: LazyLock<String> = LazyLock::new(|| {
    format!(
        "You are a helpful assistant. Be concise in your responses.\n\nHere is some additional context that makes this system prompt long enough to trigger caching:\n\n{}\n\nRemember: Always be helpful and concise.",
        ["Lorem ipsum dolor sit amet, consectetur adipiscing elit. Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris."; 50]
            .join("\n\n")
    )
});

async fn test_total_tokens_with_cache(
    llm: &Model,
    options: ProviderStreamOptions,
) -> (Usage, Usage) {
    // First request - no cache
    let context1: Context = serde_json::from_value(json!({
        "systemPrompt": *LONG_SYSTEM_PROMPT,
        "messages": [{
            "role": "user",
            "content": "What is 2 + 2? Reply with just the number.",
            "timestamp": now(),
        }],
    }))
    .expect("context");

    let response1 = complete(llm, context1.clone(), options.clone())
        .await
        .expect("first response");
    assert_eq!(
        response1.stop_reason,
        StopReason::Stop,
        "Error: {:?}",
        response1.error_message
    );

    // Second request - should trigger cache read (same system prompt, add conversation)
    let mut messages = context1.messages;
    messages.push(Message::Assistant(response1.clone())); // Include previous assistant response
    messages.push(
        serde_json::from_value(json!({
            "role": "user",
            "content": "What is 3 + 3? Reply with just the number.",
            "timestamp": now(),
        }))
        .expect("user message"),
    );
    let context2 = Context {
        system_prompt: Some(LONG_SYSTEM_PROMPT.clone()),
        messages,
        tools: None,
    };

    let response2 = complete(llm, context2, options)
        .await
        .expect("second response");
    assert_eq!(
        response2.stop_reason,
        StopReason::Stop,
        "Error: {:?}",
        response2.error_message
    );

    (response1.usage, response2.usage)
}

fn log_usage(label: &str, usage: &Usage) {
    let computed = usage.input + usage.output + usage.cache_read + usage.cache_write;
    println!("  {label}:");
    println!(
        "    input: {}, output: {}, cacheRead: {}, cacheWrite: {}",
        usage.input, usage.output, usage.cache_read, usage.cache_write
    );
    println!(
        "    totalTokens: {}, computed: {computed}",
        usage.total_tokens
    );
}

#[track_caller]
fn assert_total_tokens_equals_components(usage: &Usage) {
    let computed = usage.input + usage.output + usage.cache_read + usage.cache_write;
    assert_eq!(usage.total_tokens, computed);
}

/// Whether a case also expects cache activity (the Anthropic cases).
#[derive(Clone, Copy)]
enum CacheActivity {
    Expected,
    NotChecked,
}

/// One TS `it` body with `{ retry: 3 }`.
async fn run(
    label: &str,
    llm: &Model,
    api_key: Option<&str>,
    extra: &JsonValue,
    cache: CacheActivity,
) {
    with_retry(3, || async {
        println!("\n{label} / {}:", llm.id);
        let (first, second) =
            test_total_tokens_with_cache(llm, options(api_key.map(str::to_owned), extra)).await;

        log_usage("First request", &first);
        log_usage("Second request", &second);

        assert_total_tokens_equals_components(&first);
        assert_total_tokens_equals_components(&second);

        match cache {
            CacheActivity::Expected => {
                // Anthropic should have cache activity
                let has_cache =
                    second.cache_read > 0 || second.cache_write > 0 || first.cache_write > 0;
                assert!(has_cache);
            }
            CacheActivity::NotChecked => {}
        }
    })
    .await;
}

// Anthropic

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn anthropic_api_key_claude_sonnet_4_5_should_return_total_tokens_equal_to_sum_of_components()
{
    let key = require_env("ANTHROPIC_API_KEY");
    let llm = model("anthropic", "claude-sonnet-4-5");
    run(
        "Anthropic",
        &llm,
        Some(&key),
        &json!({}),
        CacheActivity::Expected,
    )
    .await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_ANTHROPIC_TOKEN (Anthropic OAuth); run with --ignored"]
async fn anthropic_oauth_claude_sonnet_4_should_return_total_tokens_equal_to_sum_of_components() {
    let token = oauth_token("anthropic");
    let llm = model("anthropic", "claude-sonnet-4-6");
    run(
        "Anthropic OAuth",
        &llm,
        Some(&token),
        &json!({}),
        CacheActivity::Expected,
    )
    .await;
}

// OpenAI

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_completions_gpt_4o_mini_should_return_total_tokens_equal_to_sum_of_components() {
    require_env("OPENAI_API_KEY");
    let llm = as_openai_completions(&model("openai", "gpt-4o-mini"));
    run(
        "OpenAI Completions",
        &llm,
        None,
        &json!({}),
        CacheActivity::NotChecked,
    )
    .await;
}

/// TS names this case "claude-haiku-4.5" but runs `openai/gpt-4o`.
#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_claude_haiku_4_5_should_return_total_tokens_equal_to_sum_of_components() {
    require_env("OPENAI_API_KEY");
    let llm = model("openai", "gpt-4o");
    run(
        "OpenAI Responses",
        &llm,
        None,
        &json!({}),
        CacheActivity::NotChecked,
    )
    .await;
}

#[tokio::test]
#[ignore = "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored"]
async fn azure_openai_responses_gpt_4o_mini_should_return_total_tokens_equal_to_sum_of_components()
{
    require_azure_openai_credentials();
    let llm = model("azure", "gpt-4o-mini");
    let azure_options = resolve_azure_deployment_name(&llm.id)
        .map_or_else(|| json!({}), |name| json!({ "azureDeploymentName": name }));
    run(
        "Azure OpenAI Responses",
        &llm,
        None,
        &azure_options,
        CacheActivity::NotChecked,
    )
    .await;
}

// Google

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn google_gemini_2_5_flash_should_return_total_tokens_equal_to_sum_of_components() {
    require_env("GEMINI_API_KEY");
    let llm = model("google", "gemini-2.5-flash");
    run("Google", &llm, None, &json!({}), CacheActivity::NotChecked).await;
}

/// Cases whose TS body passes `apiKey: process.env.<VAR>`.
async fn run_with_env_key(label: &str, var: &str, provider: &str, id: &str, extra: &JsonValue) {
    let key = require_env(var);
    let llm = model(provider, id);
    run(label, &llm, Some(&key), extra, CacheActivity::NotChecked).await;
}

#[tokio::test]
#[ignore = "needs XAI_API_KEY; run with --ignored"]
async fn xai_grok_4_3_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key("xAI", "XAI_API_KEY", "xai", "grok-4.3", &json!({})).await;
}

#[tokio::test]
#[ignore = "needs GROQ_API_KEY; run with --ignored"]
async fn groq_openai_gpt_oss_120b_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "Groq",
        "GROQ_API_KEY",
        "groq",
        "openai/gpt-oss-120b",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs CEREBRAS_API_KEY; run with --ignored"]
async fn cerebras_gpt_oss_120b_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "Cerebras",
        "CEREBRAS_API_KEY",
        "cerebras",
        "gpt-oss-120b",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs CLOUDFLARE_API_KEY and CLOUDFLARE_ACCOUNT_ID; run with --ignored"]
async fn cloudflare_workers_ai_kimi_k2_6_should_return_total_tokens_equal_to_sum_of_components() {
    require_cloudflare_workers_ai_credentials();
    run_with_env_key(
        "Cloudflare Workers AI",
        "CLOUDFLARE_API_KEY",
        "cloudflare-workers-ai",
        "@cf/moonshotai/kimi-k2.6",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs CLOUDFLARE_API_KEY, CLOUDFLARE_ACCOUNT_ID and CLOUDFLARE_GATEWAY_ID; run with --ignored"]
async fn cloudflare_ai_gateway_kimi_k2_6_should_return_total_tokens_equal_to_sum_of_components() {
    require_cloudflare_ai_gateway_credentials();
    run_with_env_key(
        "Cloudflare AI Gateway",
        "CLOUDFLARE_API_KEY",
        "cloudflare-ai-gateway",
        "workers-ai/@cf/moonshotai/kimi-k2.6",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs HF_TOKEN; run with --ignored"]
async fn hugging_face_kimi_k2_5_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "Hugging Face",
        "HF_TOKEN",
        "huggingface",
        "moonshotai/Kimi-K2.5",
        &json!({}),
    )
    .await;
}

/// TS names this case "Kimi-K2.6" but runs `moonshotai/Kimi-K3`.
#[tokio::test]
#[ignore = "needs TOGETHER_API_KEY; run with --ignored"]
async fn together_ai_kimi_k2_6_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "Together AI",
        "TOGETHER_API_KEY",
        "together",
        "moonshotai/Kimi-K3",
        &json!({ "reasoningEffort": "high" }),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs BASETEN_API_KEY; run with --ignored"]
async fn baseten_glm_5_2_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "Baseten",
        "BASETEN_API_KEY",
        "baseten",
        "zai-org/GLM-5.2",
        &json!({ "reasoningEffort": "high" }),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs ZAI_API_KEY; run with --ignored"]
async fn zai_glm_5_2_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key("z.ai", "ZAI_API_KEY", "zai", "glm-5.2", &json!({})).await;
}

#[tokio::test]
#[ignore = "needs MISTRAL_API_KEY; run with --ignored"]
async fn mistral_devstral_medium_latest_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "Mistral",
        "MISTRAL_API_KEY",
        "mistral",
        "devstral-medium-latest",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs MINIMAX_API_KEY; run with --ignored"]
async fn minimax_minimax_m2_7_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "MiniMax",
        "MINIMAX_API_KEY",
        "minimax",
        "MiniMax-M2.7",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_API_KEY; run with --ignored"]
async fn xiaomi_mimo_v2_5_pro_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "Xiaomi MiMo",
        "XIAOMI_API_KEY",
        "xiaomi",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_cn_mimo_v2_5_pro_should_return_total_tokens_equal_to_sum_of_components()
{
    run_with_env_key(
        "Xiaomi MiMo Token Plan CN",
        "XIAOMI_TOKEN_PLAN_CN_API_KEY",
        "xiaomi-token-plan-cn",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_ams_mimo_v2_5_pro_should_return_total_tokens_equal_to_sum_of_components()
{
    run_with_env_key(
        "Xiaomi MiMo Token Plan AMS",
        "XIAOMI_TOKEN_PLAN_AMS_API_KEY",
        "xiaomi-token-plan-ams",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_sgp_mimo_v2_5_pro_should_return_total_tokens_equal_to_sum_of_components()
{
    run_with_env_key(
        "Xiaomi MiMo Token Plan SGP",
        "XIAOMI_TOKEN_PLAN_SGP_API_KEY",
        "xiaomi-token-plan-sgp",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_qwen3_7_max_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "Qwen Token Plan",
        "QWEN_TOKEN_PLAN_API_KEY",
        "qwen-token-plan",
        "qwen3.7-max",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_individual_qwen3_8_max_should_return_total_tokens_equal_to_sum_of_components(
) {
    run_with_env_key(
        "Qwen Token Plan Individual",
        "QWEN_TOKEN_PLAN_API_KEY",
        "qwen-token-plan-individual",
        "qwen3.8-max",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn qwen_token_plan_cn_qwen3_7_max_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "Qwen Token Plan CN",
        "QWEN_TOKEN_PLAN_CN_API_KEY",
        "qwen-token-plan-cn",
        "qwen3.7-max",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs KIMI_API_KEY; run with --ignored"]
async fn kimi_for_coding_kimi_for_coding_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "Kimi For Coding",
        "KIMI_API_KEY",
        "kimi-coding",
        "kimi-for-coding",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs AI_GATEWAY_API_KEY; run with --ignored"]
async fn vercel_ai_gateway_gemini_2_5_flash_should_return_total_tokens_equal_to_sum_of_components()
{
    run_with_env_key(
        "Vercel AI Gateway",
        "AI_GATEWAY_API_KEY",
        "vercel-ai-gateway",
        "google/gemini-2.5-flash",
        &json!({}),
    )
    .await;
}

// OpenRouter - Multiple backend providers

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_claude_sonnet_4_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "OpenRouter",
        "OPENROUTER_API_KEY",
        "openrouter",
        "anthropic/claude-sonnet-4",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_deepseek_chat_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "OpenRouter",
        "OPENROUTER_API_KEY",
        "openrouter",
        "deepseek/deepseek-chat",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_mistral_small_3_2_24b_instruct_should_return_total_tokens_equal_to_sum_of_components(
) {
    run_with_env_key(
        "OpenRouter",
        "OPENROUTER_API_KEY",
        "openrouter",
        "mistralai/mistral-small-3.2-24b-instruct",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_gemini_2_5_flash_should_return_total_tokens_equal_to_sum_of_components() {
    run_with_env_key(
        "OpenRouter",
        "OPENROUTER_API_KEY",
        "openrouter",
        "google/gemini-2.5-flash",
        &json!({}),
    )
    .await;
}

/// TS repeats the `deepseek/deepseek-chat` case verbatim.
#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_deepseek_chat_should_return_total_tokens_equal_to_sum_of_components_2() {
    run_with_env_key(
        "OpenRouter",
        "OPENROUTER_API_KEY",
        "openrouter",
        "deepseek/deepseek-chat",
        &json!({}),
    )
    .await;
}

// GitHub Copilot (OAuth)

#[tokio::test]
#[ignore = "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored"]
async fn github_copilot_claude_haiku_4_5_should_return_total_tokens_equal_to_sum_of_components() {
    let token = oauth_token("github-copilot");
    let llm = model("github-copilot", "claude-haiku-4.5");
    run(
        "GitHub Copilot",
        &llm,
        Some(&token),
        &json!({}),
        CacheActivity::NotChecked,
    )
    .await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored"]
async fn github_copilot_claude_sonnet_4_should_return_total_tokens_equal_to_sum_of_components() {
    let token = oauth_token("github-copilot");
    let llm = model("github-copilot", "claude-sonnet-4.6");
    run(
        "GitHub Copilot",
        &llm,
        Some(&token),
        &json!({}),
        CacheActivity::NotChecked,
    )
    .await;
}

#[tokio::test]
#[ignore = "needs AWS_PROFILE, AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored"]
async fn amazon_bedrock_claude_sonnet_4_5_should_return_total_tokens_equal_to_sum_of_components() {
    require_bedrock_credentials();
    let llm = model(
        "amazon-bedrock",
        "global.anthropic.claude-sonnet-4-5-20250929-v1:0",
    );
    run(
        "Amazon Bedrock",
        &llm,
        None,
        &json!({}),
        CacheActivity::NotChecked,
    )
    .await;
}

// OpenAI Codex (OAuth)

#[tokio::test]
#[ignore = "needs PI_TEST_OPENAI_CODEX_TOKEN; run with --ignored"]
async fn openai_codex_gpt_5_5_should_return_total_tokens_equal_to_sum_of_components() {
    let token = oauth_token("openai-codex");
    let llm = model("openai-codex", "gpt-5.5");
    run(
        "OpenAI Codex",
        &llm,
        Some(&token),
        &json!({}),
        CacheActivity::NotChecked,
    )
    .await;
}
