//! Port of `test/abort.test.ts`: aborting a provider stream mid-generation
//! or before it starts ends the request with `stopReason: "aborted"`, and the
//! conversation continues afterwards.
//!
//! Every TS case talks to a live provider and is skipped without its
//! credentials; here each case is `#[ignore]`d and fails with a clear message
//! when its credential is missing. Keys reach the request through the compat
//! `stream`/`complete` env API key injection, as in TS. The `OpenAI` Codex
//! token, which TS resolves from `~/.pi/agent/auth.json` (`test/oauth.ts`),
//! comes from `PI_TEST_OPENAI_CODEX_TOKEN`.

mod common;

use std::future::Future;
use std::panic::{resume_unwind, AssertUnwindSafe};

use common::user;
use eukhe_chord::context::AbortController;
use eukhe_pi_ai::compat::{complete, get_model, stream};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{AssistantMessageEvent, Context, JsonValue, Message, Model, StopReason};
use futures::{FutureExt, StreamExt};
use serde_json::json;

/// TS `{ retry: 3 }`.
const RETRY_ATTEMPTS: usize = 3;

/// Runs `attempt` until it passes, up to [`RETRY_ATTEMPTS`] times; the last
/// failure propagates.
async fn with_retry<F, Fut>(mut attempt: F)
where
    F: FnMut() -> Fut,
    Fut: Future<Output = ()>,
{
    for n in 1..=RETRY_ATTEMPTS {
        match AssertUnwindSafe(attempt()).catch_unwind().await {
            Ok(()) => return,
            Err(panic) if n == RETRY_ATTEMPTS => resume_unwind(panic),
            Err(_) => {}
        }
    }
}

fn env_set(name: &str) -> bool {
    std::env::var(name).is_ok_and(|value| !value.is_empty())
}

/// The TS `describe.skipIf(!process.env.<name>)` gate.
fn require_env(name: &str) {
    assert!(env_set(name), "{name} is not set");
}

/// TS `hasAzureOpenAICredentials` (`test/azure-utils.ts`).
fn has_azure_openai_credentials() -> bool {
    env_set("AZURE_OPENAI_API_KEY")
        && (env_set("AZURE_OPENAI_BASE_URL") || env_set("AZURE_OPENAI_RESOURCE_NAME"))
}

/// TS `resolveAzureDeploymentName` (`test/azure-utils.ts`).
fn resolve_azure_deployment_name(model_id: &str) -> Option<String> {
    let map_value = std::env::var("AZURE_OPENAI_DEPLOYMENT_NAME_MAP").ok()?;
    map_value.split(',').find_map(|entry| {
        let mut parts = entry.trim().splitn(2, '=');
        let id = parts.next()?.trim();
        let deployment = parts.next()?.trim();
        (!id.is_empty() && !deployment.is_empty() && id == model_id).then(|| deployment.to_owned())
    })
}

/// TS `hasBedrockCredentials` (`test/bedrock-utils.ts`).
fn has_bedrock_credentials() -> bool {
    env_set("AWS_PROFILE")
        || (env_set("AWS_ACCESS_KEY_ID") && env_set("AWS_SECRET_ACCESS_KEY"))
        || env_set("AWS_BEARER_TOKEN_BEDROCK")
}

/// TS `resolveApiKey("openai-codex")` (`test/oauth.ts`).
fn openai_codex_token() -> String {
    std::env::var("PI_TEST_OPENAI_CODEX_TOKEN")
        .ok()
        .filter(|token| !token.is_empty())
        .expect("PI_TEST_OPENAI_CODEX_TOKEN is not set")
}

fn model(provider: &str, id: &str) -> Model {
    get_model(provider, id).unwrap_or_else(|| panic!("model {provider}/{id}"))
}

/// The TS `StreamOptions & Record<string, unknown>` extras object.
fn options(extra: &JsonValue) -> ProviderStreamOptions {
    ProviderStreamOptions {
        extra: serde_json::from_value(extra.clone()).expect("stream options"),
        ..ProviderStreamOptions::default()
    }
}

/// `{ ...options, signal: controller.signal }`.
fn with_signal(
    options: &ProviderStreamOptions,
    controller: &AbortController,
) -> ProviderStreamOptions {
    let mut options = options.clone();
    options.stream.request.signal = Some(controller.signal());
    options
}

/// JS `string.length`.
fn js_length(text: &str) -> usize {
    text.encode_utf16().count()
}

/// TS `testAbortSignal`.
async fn test_abort_signal(llm: &Model, options: &ProviderStreamOptions) {
    let mut context = Context {
        system_prompt: Some("You are a helpful assistant.".to_owned()),
        messages: vec![user(
            "What is 15 + 27? Think step by step. Then list 50 first names.",
        )],
        tools: None,
    };

    let mut abort_fired = false;
    let mut text = String::new();
    let controller = AbortController::new();
    let response = stream(llm, context.clone(), with_signal(options, &controller)).expect("stream");
    let mut events = response.events();
    while let Some(event) = events.next().await {
        if abort_fired {
            return;
        }
        if let AssistantMessageEvent::TextDelta { delta, .. }
        | AssistantMessageEvent::ThinkingDelta { delta, .. } = &event
        {
            text.push_str(delta);
        }
        if js_length(&text) >= 50 {
            controller.abort(None);
            abort_fired = true;
        }
    }
    let msg = response.result().await;

    // If we get here without throwing, the abort didn't work
    assert_eq!(msg.stop_reason, StopReason::Aborted);
    assert!(!msg.content.is_empty());

    context.messages.push(Message::Assistant(msg));
    context
        .messages
        .push(user("Please continue, but only generate 5 names."));

    let follow_up = complete(llm, context, options.clone())
        .await
        .expect("complete");
    assert_eq!(follow_up.stop_reason, StopReason::Stop);
    assert!(!follow_up.content.is_empty());
}

/// TS `testImmediateAbort`.
async fn test_immediate_abort(llm: &Model, options: &ProviderStreamOptions) {
    let controller = AbortController::new();

    controller.abort(None);

    let context = Context {
        system_prompt: None,
        messages: vec![user("Hello")],
        tools: None,
    };

    let response = complete(llm, context, with_signal(options, &controller))
        .await
        .expect("complete");
    assert_eq!(response.stop_reason, StopReason::Aborted);
}

/// TS `testAbortThenNewMessage`.
async fn test_abort_then_new_message(llm: &Model, options: &ProviderStreamOptions) {
    // First request: abort immediately before any response content arrives
    let controller = AbortController::new();
    controller.abort(None);

    let mut context = Context {
        system_prompt: None,
        messages: vec![user("Hello, how are you?")],
        tools: None,
    };

    let aborted_response = complete(llm, context.clone(), with_signal(options, &controller))
        .await
        .expect("complete");
    assert_eq!(aborted_response.stop_reason, StopReason::Aborted);
    // The aborted message has empty content since we aborted before anything arrived
    assert_eq!(aborted_response.content.len(), 0);

    // Add the aborted assistant message to context (this is what happens in the real coding agent)
    context.messages.push(Message::Assistant(aborted_response));

    // Second request: send a new message - this should work even with the aborted message in context
    context.messages.push(user("What is 2 + 2?"));

    let follow_up = complete(llm, context, options.clone())
        .await
        .expect("complete");
    assert_eq!(follow_up.stop_reason, StopReason::Stop);
    assert!(!follow_up.content.is_empty());
}

/// Runs `test_abort_signal` with TS `{ retry: 3 }`.
async fn abort_mid_stream(llm: &Model, options: &ProviderStreamOptions) {
    with_retry(|| test_abort_signal(llm, options)).await;
}

/// Runs `test_immediate_abort` with TS `{ retry: 3 }`.
async fn immediate_abort(llm: &Model, options: &ProviderStreamOptions) {
    with_retry(|| test_immediate_abort(llm, options)).await;
}

// Google Provider Abort

fn google_llm() -> Model {
    model("google", "gemini-2.5-flash")
}

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn google_should_abort_mid_stream() {
    require_env("GEMINI_API_KEY");
    abort_mid_stream(
        &google_llm(),
        &options(&json!({ "thinking": { "enabled": true } })),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn google_should_handle_immediate_abort() {
    require_env("GEMINI_API_KEY");
    immediate_abort(
        &google_llm(),
        &options(&json!({ "thinking": { "enabled": true } })),
    )
    .await;
}

// OpenAI Completions Provider Abort

/// `getModel("openai", "gpt-4o-mini")` without `compat`, on the
/// `openai-completions` api.
fn openai_completions_llm() -> Model {
    let mut llm = model("openai", "gpt-4o-mini");
    llm.compat = None;
    "openai-completions".clone_into(&mut llm.api);
    llm
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_completions_should_abort_mid_stream() {
    require_env("OPENAI_API_KEY");
    abort_mid_stream(&openai_completions_llm(), &options(&json!({}))).await;
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_completions_should_handle_immediate_abort() {
    require_env("OPENAI_API_KEY");
    immediate_abort(&openai_completions_llm(), &options(&json!({}))).await;
}

// OpenAI Responses Provider Abort

fn openai_responses_llm() -> Model {
    model("openai", "gpt-5-mini")
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_should_abort_mid_stream() {
    require_env("OPENAI_API_KEY");
    abort_mid_stream(&openai_responses_llm(), &options(&json!({}))).await;
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_should_handle_immediate_abort() {
    require_env("OPENAI_API_KEY");
    immediate_abort(&openai_responses_llm(), &options(&json!({}))).await;
}

// Azure OpenAI Responses Provider Abort

/// The Azure model and `azureDeploymentName ? { azureDeploymentName } : {}`.
fn azure() -> (Model, ProviderStreamOptions) {
    assert!(
        has_azure_openai_credentials(),
        "AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME are not set"
    );
    let llm = model("azure", "gpt-4o-mini");
    let azure_options = resolve_azure_deployment_name(&llm.id).map_or_else(
        || json!({}),
        |azure_deployment_name| json!({ "azureDeploymentName": azure_deployment_name }),
    );
    (llm, options(&azure_options))
}

#[tokio::test]
#[ignore = "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored"]
async fn azure_openai_responses_should_abort_mid_stream() {
    let (llm, azure_options) = azure();
    abort_mid_stream(&llm, &azure_options).await;
}

#[tokio::test]
#[ignore = "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored"]
async fn azure_openai_responses_should_handle_immediate_abort() {
    let (llm, azure_options) = azure();
    immediate_abort(&llm, &azure_options).await;
}

// Anthropic Provider Abort

fn anthropic_llm() -> Model {
    model("anthropic", "claude-sonnet-4-6")
}

fn anthropic_options() -> ProviderStreamOptions {
    options(&json!({ "thinkingEnabled": true, "thinkingBudgetTokens": 2048 }))
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_OAUTH_TOKEN; run with --ignored"]
async fn anthropic_should_abort_mid_stream() {
    require_env("ANTHROPIC_OAUTH_TOKEN");
    abort_mid_stream(&anthropic_llm(), &anthropic_options()).await;
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_OAUTH_TOKEN; run with --ignored"]
async fn anthropic_should_handle_immediate_abort() {
    require_env("ANTHROPIC_OAUTH_TOKEN");
    immediate_abort(&anthropic_llm(), &anthropic_options()).await;
}

// Mistral Provider Abort

fn mistral_llm() -> Model {
    model("mistral", "devstral-medium-latest")
}

#[tokio::test]
#[ignore = "needs MISTRAL_API_KEY; run with --ignored"]
async fn mistral_should_abort_mid_stream() {
    require_env("MISTRAL_API_KEY");
    abort_mid_stream(&mistral_llm(), &options(&json!({}))).await;
}

#[tokio::test]
#[ignore = "needs MISTRAL_API_KEY; run with --ignored"]
async fn mistral_should_handle_immediate_abort() {
    require_env("MISTRAL_API_KEY");
    immediate_abort(&mistral_llm(), &options(&json!({}))).await;
}

// Together AI Provider Abort

fn together_llm() -> Model {
    model("together", "moonshotai/Kimi-K3")
}

#[tokio::test]
#[ignore = "needs TOGETHER_API_KEY; run with --ignored"]
async fn together_should_abort_mid_stream() {
    require_env("TOGETHER_API_KEY");
    abort_mid_stream(
        &together_llm(),
        &options(&json!({ "reasoningEffort": "high" })),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs TOGETHER_API_KEY; run with --ignored"]
async fn together_should_handle_immediate_abort() {
    require_env("TOGETHER_API_KEY");
    immediate_abort(
        &together_llm(),
        &options(&json!({ "reasoningEffort": "high" })),
    )
    .await;
}

// Baseten Provider Abort

fn baseten_llm() -> Model {
    model("baseten", "zai-org/GLM-5.2")
}

#[tokio::test]
#[ignore = "needs BASETEN_API_KEY; run with --ignored"]
async fn baseten_should_abort_mid_stream() {
    require_env("BASETEN_API_KEY");
    abort_mid_stream(
        &baseten_llm(),
        &options(&json!({ "reasoningEffort": "high" })),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs BASETEN_API_KEY; run with --ignored"]
async fn baseten_should_handle_immediate_abort() {
    require_env("BASETEN_API_KEY");
    immediate_abort(
        &baseten_llm(),
        &options(&json!({ "reasoningEffort": "high" })),
    )
    .await;
}

// MiniMax Provider Abort

fn minimax_llm() -> Model {
    model("minimax", "MiniMax-M2.7")
}

#[tokio::test]
#[ignore = "needs MINIMAX_API_KEY; run with --ignored"]
async fn minimax_should_abort_mid_stream() {
    require_env("MINIMAX_API_KEY");
    abort_mid_stream(&minimax_llm(), &options(&json!({}))).await;
}

#[tokio::test]
#[ignore = "needs MINIMAX_API_KEY; run with --ignored"]
async fn minimax_should_handle_immediate_abort() {
    require_env("MINIMAX_API_KEY");
    immediate_abort(&minimax_llm(), &options(&json!({}))).await;
}

// Xiaomi MiMo (API billing) Provider Abort

#[tokio::test]
#[ignore = "needs XIAOMI_API_KEY; run with --ignored"]
async fn xiaomi_should_abort_mid_stream() {
    require_env("XIAOMI_API_KEY");
    abort_mid_stream(&model("xiaomi", "mimo-v2.5-pro"), &options(&json!({}))).await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_API_KEY; run with --ignored"]
async fn xiaomi_should_handle_immediate_abort() {
    require_env("XIAOMI_API_KEY");
    immediate_abort(&model("xiaomi", "mimo-v2.5-pro"), &options(&json!({}))).await;
}

// Xiaomi MiMo Token Plan (CN) Provider Abort

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_cn_should_abort_mid_stream() {
    require_env("XIAOMI_TOKEN_PLAN_CN_API_KEY");
    abort_mid_stream(
        &model("xiaomi-token-plan-cn", "mimo-v2.5-pro"),
        &options(&json!({})),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_cn_should_handle_immediate_abort() {
    require_env("XIAOMI_TOKEN_PLAN_CN_API_KEY");
    immediate_abort(
        &model("xiaomi-token-plan-cn", "mimo-v2.5-pro"),
        &options(&json!({})),
    )
    .await;
}

// Xiaomi MiMo Token Plan (AMS) Provider Abort

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_ams_should_abort_mid_stream() {
    require_env("XIAOMI_TOKEN_PLAN_AMS_API_KEY");
    abort_mid_stream(
        &model("xiaomi-token-plan-ams", "mimo-v2.5-pro"),
        &options(&json!({})),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_ams_should_handle_immediate_abort() {
    require_env("XIAOMI_TOKEN_PLAN_AMS_API_KEY");
    immediate_abort(
        &model("xiaomi-token-plan-ams", "mimo-v2.5-pro"),
        &options(&json!({})),
    )
    .await;
}

// Xiaomi MiMo Token Plan (SGP) Provider Abort

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_sgp_should_abort_mid_stream() {
    require_env("XIAOMI_TOKEN_PLAN_SGP_API_KEY");
    abort_mid_stream(
        &model("xiaomi-token-plan-sgp", "mimo-v2.5-pro"),
        &options(&json!({})),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_sgp_should_handle_immediate_abort() {
    require_env("XIAOMI_TOKEN_PLAN_SGP_API_KEY");
    immediate_abort(
        &model("xiaomi-token-plan-sgp", "mimo-v2.5-pro"),
        &options(&json!({})),
    )
    .await;
}

// Qwen Token Plan Provider Abort

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_should_abort_mid_stream() {
    require_env("QWEN_TOKEN_PLAN_API_KEY");
    abort_mid_stream(
        &model("qwen-token-plan", "qwen3.7-max"),
        &options(&json!({})),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_should_handle_immediate_abort() {
    require_env("QWEN_TOKEN_PLAN_API_KEY");
    immediate_abort(
        &model("qwen-token-plan", "qwen3.7-max"),
        &options(&json!({})),
    )
    .await;
}

// Qwen Token Plan Individual Provider Abort

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_individual_should_abort_mid_stream() {
    require_env("QWEN_TOKEN_PLAN_API_KEY");
    abort_mid_stream(
        &model("qwen-token-plan-individual", "qwen3.8-max"),
        &options(&json!({})),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_individual_should_handle_immediate_abort() {
    require_env("QWEN_TOKEN_PLAN_API_KEY");
    immediate_abort(
        &model("qwen-token-plan-individual", "qwen3.8-max"),
        &options(&json!({})),
    )
    .await;
}

// Qwen Token Plan (CN) Provider Abort

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn qwen_token_plan_cn_should_abort_mid_stream() {
    require_env("QWEN_TOKEN_PLAN_CN_API_KEY");
    abort_mid_stream(
        &model("qwen-token-plan-cn", "qwen3.7-max"),
        &options(&json!({})),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn qwen_token_plan_cn_should_handle_immediate_abort() {
    require_env("QWEN_TOKEN_PLAN_CN_API_KEY");
    immediate_abort(
        &model("qwen-token-plan-cn", "qwen3.7-max"),
        &options(&json!({})),
    )
    .await;
}

// Kimi For Coding Provider Abort

#[tokio::test]
#[ignore = "needs KIMI_API_KEY; run with --ignored"]
async fn kimi_coding_should_abort_mid_stream() {
    require_env("KIMI_API_KEY");
    abort_mid_stream(
        &model("kimi-coding", "kimi-for-coding"),
        &options(&json!({})),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs KIMI_API_KEY; run with --ignored"]
async fn kimi_coding_should_handle_immediate_abort() {
    require_env("KIMI_API_KEY");
    immediate_abort(
        &model("kimi-coding", "kimi-for-coding"),
        &options(&json!({})),
    )
    .await;
}

// Vercel AI Gateway Provider Abort

fn vercel_ai_gateway_llm() -> Model {
    model("vercel-ai-gateway", "google/gemini-2.5-flash")
}

#[tokio::test]
#[ignore = "needs AI_GATEWAY_API_KEY; run with --ignored"]
async fn vercel_ai_gateway_should_abort_mid_stream() {
    require_env("AI_GATEWAY_API_KEY");
    abort_mid_stream(&vercel_ai_gateway_llm(), &options(&json!({}))).await;
}

#[tokio::test]
#[ignore = "needs AI_GATEWAY_API_KEY; run with --ignored"]
async fn vercel_ai_gateway_should_handle_immediate_abort() {
    require_env("AI_GATEWAY_API_KEY");
    immediate_abort(&vercel_ai_gateway_llm(), &options(&json!({}))).await;
}

// OpenAI Codex Provider Abort

fn openai_codex_options() -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some(openai_codex_token());
    options
}

#[tokio::test]
#[ignore = "needs PI_TEST_OPENAI_CODEX_TOKEN (OpenAI Codex OAuth); run with --ignored"]
async fn openai_codex_should_abort_mid_stream() {
    let options = openai_codex_options();
    abort_mid_stream(&model("openai-codex", "gpt-5.5"), &options).await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_OPENAI_CODEX_TOKEN (OpenAI Codex OAuth); run with --ignored"]
async fn openai_codex_should_handle_immediate_abort() {
    let options = openai_codex_options();
    immediate_abort(&model("openai-codex", "gpt-5.5"), &options).await;
}

// Amazon Bedrock Provider Abort

fn bedrock_llm() -> Model {
    assert!(
        has_bedrock_credentials(),
        "AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK is not set"
    );
    model(
        "amazon-bedrock",
        "global.anthropic.claude-sonnet-4-5-20250929-v1:0",
    )
}

#[tokio::test]
#[ignore = "needs AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored"]
async fn amazon_bedrock_should_abort_mid_stream() {
    abort_mid_stream(&bedrock_llm(), &options(&json!({ "reasoning": "medium" }))).await;
}

#[tokio::test]
#[ignore = "needs AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored"]
async fn amazon_bedrock_should_handle_immediate_abort() {
    immediate_abort(&bedrock_llm(), &options(&json!({}))).await;
}

#[tokio::test]
#[ignore = "needs AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored"]
async fn amazon_bedrock_should_handle_abort_then_new_message() {
    let llm = bedrock_llm();
    let options = options(&json!({}));
    with_retry(|| test_abort_then_new_message(&llm, &options)).await;
}
