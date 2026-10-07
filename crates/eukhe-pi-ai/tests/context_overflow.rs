//! Port of `test/context-overflow.test.ts`: context overflow error handling
//! across providers.
//!
//! Context overflow occurs when the input (prompt + history) exceeds the
//! model's context window. This is different from output token limits.
//! Expected behavior: all providers return `stopReason: "error"` with an
//! `errorMessage` that indicates the context was too large, OR (for z.ai)
//! return successfully with `usage.input > contextWindow`.
//! `is_context_overflow()` must return true for all providers.
//!
//! All cases hit real endpoints or local servers; the TS suites are skipped
//! without credentials or a detected local server, here they are
//! `#[ignore]`d. TS `resolveApiKey()` OAuth tokens (read from
//! `~/.pi/agent/oauth.json`) come from the env vars named in the ignore
//! reasons.

use std::time::Duration;

use eukhe_pi_ai::compat::{complete, get_model, get_models};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::overflow::is_context_overflow;
use eukhe_types::pi_ai::{AssistantMessage, Context, Model, StopReason, Usage};
use regex::Regex;
use serde_json::json;

/// Lorem ipsum paragraph for realistic token estimation.
const LOREM_IPSUM: &str = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum. ";

fn env_value(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

fn require_env(name: &str) -> String {
    env_value(name).unwrap_or_else(|| panic!("Missing {name}; this test needs it set"))
}

fn builtin(provider: &str, id: &str) -> Model {
    get_model(provider, id).unwrap_or_else(|| panic!("unknown model {provider}/{id}"))
}

fn now_ms() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock after epoch")
            .as_millis(),
    )
    .expect("epoch millis fit u64")
}

/// A string that exceeds the context window, using chars/4 as the token
/// estimate (works better with varied text than repeated chars).
#[allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss
)] // JS number math: context windows are far below 2^53 and the result is a positive integer.
fn generate_overflow_content(context_window: u64) -> String {
    let target_tokens = context_window + 10_000; // Exceed by 10k tokens.
    let target_chars = target_tokens as f64 * 4.0 * 1.5;
    let repetitions = (target_chars / LOREM_IPSUM.len() as f64).ceil() as usize;
    LOREM_IPSUM.repeat(repetitions)
}

struct OverflowResult {
    provider: String,
    model: String,
    context_window: u64,
    stop_reason: StopReason,
    error_message: Option<String>,
    usage: Usage,
    has_usage_data: bool,
    response: AssistantMessage,
}

async fn test_context_overflow(model: &Model, api_key: &str) -> OverflowResult {
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are a helpful assistant.",
        "messages": [{
            "role": "user",
            "content": generate_overflow_content(model.context_window),
            "timestamp": now_ms(),
        }],
    }))
    .expect("context");

    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some(api_key.to_owned());
    let response = complete(model, context, options).await.expect("complete");

    let has_usage_data = response.usage.input > 0 || response.usage.cache_read > 0;

    OverflowResult {
        provider: model.provider.clone(),
        model: model.id.clone(),
        context_window: model.context_window,
        stop_reason: response.stop_reason,
        error_message: response.error_message.clone(),
        usage: response.usage,
        has_usage_data,
        response,
    }
}

fn log_result(result: &OverflowResult) {
    println!("\n{} / {}:", result.provider, result.model);
    println!("  contextWindow: {}", result.context_window);
    println!(
        "  stopReason: {}",
        serde_json::to_value(result.stop_reason).expect("stopReason")
    );
    println!("  errorMessage: {:?}", result.error_message);
    println!(
        "  usage: {}",
        serde_json::to_string(&result.usage).expect("usage")
    );
    println!("  hasUsageData: {}", result.has_usage_data);
}

/// `expect(result.errorMessage).toMatch(pattern)`.
#[track_caller]
fn assert_error_matches(result: &OverflowResult, pattern: &str) {
    let message = result
        .error_message
        .as_deref()
        .unwrap_or_else(|| panic!("errorMessage missing; expected to match {pattern}"));
    assert!(
        Regex::new(pattern).expect("pattern").is_match(message),
        "errorMessage {message:?} does not match {pattern}"
    );
}

#[track_caller]
fn assert_overflow(result: &OverflowResult, model: &Model) {
    assert!(
        is_context_overflow(&result.response, Some(model.context_window)),
        "isContextOverflow returned false"
    );
}

/// The common shape: `stopReason` "error", optional message pattern, and
/// overflow detection.
async fn expect_error_overflow(model: &Model, api_key: &str, pattern: Option<&str>) {
    let result = test_context_overflow(model, api_key).await;
    log_result(&result);

    assert_eq!(result.stop_reason, StopReason::Error);
    if let Some(pattern) = pattern {
        assert_error_matches(&result, pattern);
    }
    assert_overflow(&result, model);
}

/// Xiaomi silently truncates oversized input to fill the context window
/// exactly, then returns `finish_reason` "length" with output=0 (no room left
/// to generate). A detectable overflow signal with `stopReason` "length".
async fn expect_length_overflow(model: &Model, api_key: &str) {
    let result = test_context_overflow(model, api_key).await;
    log_result(&result);

    assert_eq!(result.stop_reason, StopReason::Length);
    assert_eq!(result.usage.output, 0);
    assert_overflow(&result, model);
}

// =============================================================================
// Anthropic
// Expected pattern: "prompt is too long: X tokens > Y maximum"
// =============================================================================

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn anthropic_api_key_claude_haiku_4_5_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("ANTHROPIC_API_KEY");
    let model = builtin("anthropic", "claude-haiku-4-5");
    expect_error_overflow(&model, &api_key, Some("(?i)prompt is too long")).await;
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_OAUTH_TOKEN; run with --ignored"]
async fn anthropic_oauth_claude_sonnet_4_should_detect_overflow_via_is_context_overflow() {
    let token = require_env("ANTHROPIC_OAUTH_TOKEN");
    let model = builtin("anthropic", "claude-sonnet-4-6");
    expect_error_overflow(&model, &token, Some("(?i)prompt is too long")).await;
}

// =============================================================================
// GitHub Copilot (OAuth): Google and Anthropic models via Copilot
// =============================================================================

#[tokio::test]
#[ignore = "needs GITHUB_COPILOT_OAUTH_TOKEN; run with --ignored"]
async fn github_copilot_google_model_should_detect_overflow_via_is_context_overflow() {
    let token = require_env("GITHUB_COPILOT_OAUTH_TOKEN");
    let model = get_models("github-copilot")
        .into_iter()
        .find(|candidate| candidate.id.starts_with("gemini-"))
        .expect("No Google models available through GitHub Copilot");
    expect_error_overflow(&model, &token, Some(r"(?i)exceeds the limit of \d+")).await;
}

#[tokio::test]
#[ignore = "needs GITHUB_COPILOT_OAUTH_TOKEN; run with --ignored"]
async fn github_copilot_claude_sonnet_4_should_detect_overflow_via_is_context_overflow() {
    let token = require_env("GITHUB_COPILOT_OAUTH_TOKEN");
    let model = builtin("github-copilot", "claude-sonnet-4.6");
    expect_error_overflow(
        &model,
        &token,
        Some(r"(?i)exceeds the limit of \d+|input is too long"),
    )
    .await;
}

// =============================================================================
// OpenAI
// Expected pattern: "exceeds the context window"
// =============================================================================

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_completions_gpt_4o_mini_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("OPENAI_API_KEY");
    let model = Model {
        api: "openai-completions".into(),
        ..builtin("openai", "gpt-4o-mini")
    };
    expect_error_overflow(&model, &api_key, Some("(?i)maximum context length")).await;
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_gpt_4o_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("OPENAI_API_KEY");
    let model = builtin("openai", "gpt-4o");
    expect_error_overflow(&model, &api_key, Some("(?i)exceeds the context window")).await;
}

#[tokio::test]
#[ignore = "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored"]
async fn azure_openai_responses_gpt_4o_mini_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("AZURE_OPENAI_API_KEY");
    assert!(
        env_value("AZURE_OPENAI_BASE_URL").is_some()
            || env_value("AZURE_OPENAI_RESOURCE_NAME").is_some(),
        "Missing AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME"
    );
    let model = builtin("azure", "gpt-4o-mini");
    expect_error_overflow(&model, &api_key, Some("(?i)context|maximum")).await;
}

// =============================================================================
// Google
// Expected pattern: "input token count (X) exceeds the maximum"
// =============================================================================

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn google_gemini_2_5_flash_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("GEMINI_API_KEY");
    let model = builtin("google", "gemini-2.5-flash");
    expect_error_overflow(
        &model,
        &api_key,
        Some("(?i)input token count.*exceeds the maximum"),
    )
    .await;
}

// =============================================================================
// OpenAI Codex (OAuth): ChatGPT Plus/Pro subscription
// =============================================================================

#[tokio::test]
#[ignore = "needs OPENAI_CODEX_OAUTH_TOKEN; run with --ignored"]
async fn openai_codex_gpt_5_5_should_detect_overflow_via_is_context_overflow() {
    let token = require_env("OPENAI_CODEX_OAUTH_TOKEN");
    let model = builtin("openai-codex", "gpt-5.5");
    expect_error_overflow(&model, &token, None).await;
}

// =============================================================================
// Amazon Bedrock
// Expected pattern: "Input is too long for requested model"
// =============================================================================

#[tokio::test]
#[ignore = "needs AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored"]
async fn amazon_bedrock_claude_sonnet_4_5_should_detect_overflow_via_is_context_overflow() {
    assert!(
        env_value("AWS_PROFILE").is_some()
            || (env_value("AWS_ACCESS_KEY_ID").is_some()
                && env_value("AWS_SECRET_ACCESS_KEY").is_some())
            || env_value("AWS_BEARER_TOKEN_BEDROCK").is_some(),
        "Missing AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK"
    );
    let model = builtin(
        "amazon-bedrock",
        "global.anthropic.claude-sonnet-4-5-20250929-v1:0",
    );
    expect_error_overflow(&model, "", None).await;
}

// =============================================================================
// xAI
// Expected pattern: "maximum prompt length is X but the request contains Y"
// =============================================================================

#[tokio::test]
#[ignore = "needs XAI_API_KEY; run with --ignored"]
async fn xai_grok_4_3_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("XAI_API_KEY");
    let model = builtin("xai", "grok-4.3");
    expect_error_overflow(&model, &api_key, Some(r"(?i)maximum prompt length is \d+")).await;
}

// =============================================================================
// Groq
// Expected pattern: "reduce the length of the messages"
// =============================================================================

#[tokio::test]
#[ignore = "needs GROQ_API_KEY; run with --ignored"]
async fn groq_llama_3_3_70b_versatile_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("GROQ_API_KEY");
    let model = builtin("groq", "llama-3.3-70b-versatile");
    expect_error_overflow(
        &model,
        &api_key,
        Some("(?i)reduce the length of the messages"),
    )
    .await;
}

// =============================================================================
// Cerebras
// Expected: 400/413 status code with no body
// =============================================================================

#[tokio::test]
#[ignore = "needs CEREBRAS_API_KEY; run with --ignored"]
async fn cerebras_available_model_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("CEREBRAS_API_KEY");
    let preferred_cerebras_model_ids = ["gpt-oss-120b", "zai-glm-4.7", "llama3.1-8b"];
    let cerebras_models = get_models("cerebras");
    let model = cerebras_models
        .iter()
        .find(|candidate| preferred_cerebras_model_ids.contains(&candidate.id.as_str()))
        .or_else(|| cerebras_models.first())
        .cloned()
        .expect("No Cerebras models available");

    // Cerebras returns status code with no body (400, 413, or 429 for token rate limit).
    expect_error_overflow(&model, &api_key, Some(r"(?i)4(00|13|29).*\(no body\)")).await;
}

// =============================================================================
// Hugging Face: OpenAI-compatible Inference Router
// =============================================================================

#[tokio::test]
#[ignore = "needs HF_TOKEN; run with --ignored"]
async fn hugging_face_kimi_k2_5_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("HF_TOKEN");
    let model = builtin("huggingface", "moonshotai/Kimi-K2.5");
    expect_error_overflow(&model, &api_key, None).await;
}

// =============================================================================
// Together AI: OpenAI-compatible Chat Completions API
// =============================================================================

#[tokio::test]
#[ignore = "needs TOGETHER_API_KEY; run with --ignored"]
async fn together_ai_kimi_k3_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("TOGETHER_API_KEY");
    let model = builtin("together", "moonshotai/Kimi-K3");
    expect_error_overflow(&model, &api_key, None).await;
}

// =============================================================================
// z.ai: may return explicit overflow error text, may accept overflow silently,
// or may rate limit instead
// =============================================================================

#[tokio::test]
#[ignore = "needs ZAI_API_KEY; run with --ignored"]
async fn zai_glm_5_2_should_detect_overflow_via_is_context_overflow_when_zai_reports_it() {
    let api_key = require_env("ZAI_API_KEY");
    let model = builtin("zai", "glm-5.2");
    let result = test_context_overflow(&model, &api_key).await;
    log_result(&result);

    // z.ai behavior is inconsistent:
    // - Sometimes returns explicit overflow error text via non-standard finish_reason handling
    // - Sometimes accepts overflow and returns successfully with usage.input > contextWindow
    // - Sometimes returns rate limit error
    let overflow_text = Regex::new("(?i)model_context_window_exceeded").expect("pattern");
    match result.stop_reason {
        StopReason::Error => {
            if result
                .error_message
                .as_deref()
                .is_some_and(|message| overflow_text.is_match(message))
            {
                assert_overflow(&result, &model);
            } else {
                println!("  z.ai returned non-overflow error (possibly rate limited), skipping overflow detection");
            }
        }
        StopReason::Stop => {
            if result.has_usage_data && result.usage.input > model.context_window {
                assert_overflow(&result, &model);
            } else {
                println!(
                    "  z.ai returned stop without overflow usage data, skipping overflow detection"
                );
            }
        }
        StopReason::Length
        | StopReason::ToolUse
        | StopReason::Aborted
        | StopReason::Pending
        | StopReason::Deferred => {}
    }
}

// =============================================================================
// Mistral
// =============================================================================

#[tokio::test]
#[ignore = "needs MISTRAL_API_KEY; run with --ignored"]
async fn mistral_devstral_medium_latest_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("MISTRAL_API_KEY");
    let model = builtin("mistral", "devstral-medium-latest");
    expect_error_overflow(
        &model,
        &api_key,
        Some(r"(?i)too large for model with \d+ maximum context length"),
    )
    .await;
}

// =============================================================================
// MiniMax
// =============================================================================

#[tokio::test]
#[ignore = "needs MINIMAX_API_KEY; run with --ignored"]
async fn minimax_m2_7_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("MINIMAX_API_KEY");
    let model = builtin("minimax", "MiniMax-M2.7");
    expect_error_overflow(&model, &api_key, None).await;
}

// =============================================================================
// Xiaomi MiMo
// =============================================================================

#[tokio::test]
#[ignore = "needs XIAOMI_API_KEY; run with --ignored"]
async fn xiaomi_mimo_v2_5_pro_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("XIAOMI_API_KEY");
    expect_length_overflow(&builtin("xiaomi", "mimo-v2.5-pro"), &api_key).await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_cn_mimo_v2_5_pro_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("XIAOMI_TOKEN_PLAN_CN_API_KEY");
    expect_length_overflow(&builtin("xiaomi-token-plan-cn", "mimo-v2.5-pro"), &api_key).await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_ams_mimo_v2_5_pro_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("XIAOMI_TOKEN_PLAN_AMS_API_KEY");
    expect_length_overflow(&builtin("xiaomi-token-plan-ams", "mimo-v2.5-pro"), &api_key).await;
}

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_sgp_mimo_v2_5_pro_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("XIAOMI_TOKEN_PLAN_SGP_API_KEY");
    expect_length_overflow(&builtin("xiaomi-token-plan-sgp", "mimo-v2.5-pro"), &api_key).await;
}

// =============================================================================
// Qwen Token Plan
// =============================================================================

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_qwen3_7_max_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("QWEN_TOKEN_PLAN_API_KEY");
    let model = builtin("qwen-token-plan", "qwen3.7-max");
    expect_error_overflow(&model, &api_key, Some("(?i)input length")).await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_individual_qwen3_8_max_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("QWEN_TOKEN_PLAN_API_KEY");
    let model = builtin("qwen-token-plan-individual", "qwen3.8-max");
    expect_error_overflow(&model, &api_key, Some("(?i)input length")).await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn qwen_token_plan_cn_qwen3_7_max_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("QWEN_TOKEN_PLAN_CN_API_KEY");
    let model = builtin("qwen-token-plan-cn", "qwen3.7-max");
    expect_error_overflow(&model, &api_key, Some("(?i)input length")).await;
}

// =============================================================================
// Kimi For Coding
// =============================================================================

#[tokio::test]
#[ignore = "needs KIMI_API_KEY; run with --ignored"]
async fn kimi_for_coding_should_detect_overflow_via_is_context_overflow() {
    let api_key = require_env("KIMI_API_KEY");
    let model = builtin("kimi-coding", "kimi-for-coding");
    expect_error_overflow(&model, &api_key, None).await;
}

// =============================================================================
// Vercel AI Gateway
// =============================================================================

#[tokio::test]
#[ignore = "needs AI_GATEWAY_API_KEY; run with --ignored"]
async fn vercel_ai_gateway_google_gemini_2_5_flash_should_detect_overflow_via_is_context_overflow()
{
    let api_key = require_env("AI_GATEWAY_API_KEY");
    let model = builtin("vercel-ai-gateway", "google/gemini-2.5-flash");
    expect_error_overflow(&model, &api_key, None).await;
}

// =============================================================================
// OpenRouter: multiple backend providers
// Expected pattern: "maximum context length is X tokens"
// =============================================================================

const OPENROUTER_PATTERN: &str = r"(?i)maximum context length is \d+ tokens";

async fn openrouter_case(id: &str) {
    let api_key = require_env("OPENROUTER_API_KEY");
    let model = builtin("openrouter", id);
    expect_error_overflow(&model, &api_key, Some(OPENROUTER_PATTERN)).await;
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_anthropic_claude_sonnet_4_should_detect_overflow_via_is_context_overflow() {
    openrouter_case("anthropic/claude-sonnet-4").await;
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_deepseek_v3_2_should_detect_overflow_via_is_context_overflow() {
    openrouter_case("deepseek/deepseek-v3.2").await;
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_mistral_large_2512_should_detect_overflow_via_is_context_overflow() {
    openrouter_case("mistralai/mistral-large").await;
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_google_gemini_2_5_flash_should_detect_overflow_via_is_context_overflow() {
    openrouter_case("google/gemini-2.5-flash").await;
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_meta_llama_4_scout_should_detect_overflow_via_is_context_overflow() {
    openrouter_case("meta-llama/llama-4-scout").await;
}

// =============================================================================
// Local servers (skipped in TS when PI_NO_LOCAL_LLM is set or not detected)
// =============================================================================

fn local_model(
    id: &str,
    provider: &str,
    base_url: &str,
    reasoning: bool,
    context_window: u64,
    max_tokens: u64,
    name: &str,
) -> Model {
    serde_json::from_value(json!({
        "id": id,
        "api": "openai-completions",
        "provider": provider,
        "baseUrl": base_url,
        "reasoning": reasoning,
        "input": ["text"],
        "contextWindow": context_window,
        "maxTokens": max_tokens,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "name": name,
    }))
    .expect("local model")
}

fn assert_local_llm_enabled() {
    assert!(
        env_value("PI_NO_LOCAL_LLM").is_none(),
        "PI_NO_LOCAL_LLM is set; local LLM tests are disabled"
    );
}

/// `curl -s --max-time 1 <url>` succeeding.
async fn probe(url: &str) -> bool {
    reqwest::Client::new()
        .get(url)
        .timeout(Duration::from_secs(1))
        .send()
        .await
        .is_ok()
}

/// `ollama serve`, stopped with SIGTERM on drop (TS `afterAll`).
struct OllamaServer(tokio::process::Child);

impl Drop for OllamaServer {
    fn drop(&mut self) {
        if let Some(pid) = self.0.id() {
            let _status = std::process::Command::new("kill")
                .args(["-TERM", &pid.to_string()])
                .status();
        }
    }
}

/// TS `beforeAll`: pull `gpt-oss:20b` if missing, start `ollama serve`, and
/// wait until `/api/tags` answers OK. `None` when the pull fails (the TS
/// suite then runs against no server).
async fn start_ollama() -> Option<OllamaServer> {
    let listed = tokio::process::Command::new("sh")
        .args(["-c", "ollama list | grep -q 'gpt-oss:20b'"])
        .status()
        .await
        .is_ok_and(|status| status.success());
    if !listed {
        println!("Pulling gpt-oss:20b model for Ollama overflow tests...");
        let pulled = tokio::process::Command::new("ollama")
            .args(["pull", "gpt-oss:20b"])
            .status()
            .await
            .is_ok_and(|status| status.success());
        if !pulled {
            eprintln!("Failed to pull gpt-oss:20b model, tests will be skipped");
            return None;
        }
    }

    let child = tokio::process::Command::new("ollama")
        .arg("serve")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .expect("spawn ollama serve");
    let server = OllamaServer(child);

    let client = reqwest::Client::new();
    tokio::time::sleep(Duration::from_millis(1000)).await;
    loop {
        let ready = client
            .get("http://localhost:11434/api/tags")
            .send()
            .await
            .is_ok_and(|response| response.status().is_success());
        if ready {
            break;
        }
        tokio::time::sleep(Duration::from_millis(500)).await;
    }
    Some(server)
}

#[tokio::test]
#[ignore = "needs a local ollama install (gpt-oss:20b) and PI_NO_LOCAL_LLM unset; run with --ignored"]
async fn ollama_gpt_oss_20b_should_detect_overflow_via_is_context_overflow_ollama_silently_truncates(
) {
    let model = local_model(
        "gpt-oss:20b",
        "ollama",
        "http://localhost:11434/v1",
        true,
        128_000,
        16_000,
        "Ollama GPT-OSS 20B",
    );
    assert_local_llm_enabled();
    let installed = std::process::Command::new("which")
        .arg("ollama")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok_and(|status| status.success());
    assert!(installed, "ollama is not installed");
    let _server = start_ollama().await;

    let result = test_context_overflow(&model, "ollama").await;
    log_result(&result);

    // Ollama silently truncates input instead of erroring: it returns
    // stopReason "stop" with truncated usage, so overflow is only detectable
    // via usage comparison.
    if result.stop_reason == StopReason::Stop && result.has_usage_data {
        // A "silent overflow"; Ollama gives no way to detect it, accepted as is.
        println!(
            "  Ollama silently truncated input to {} tokens",
            result.usage.input
        );
    } else if result.stop_reason == StopReason::Error {
        assert_overflow(&result, &model);
    }
}

#[tokio::test]
#[ignore = "needs LM Studio running on localhost:1234 and PI_NO_LOCAL_LLM unset; run with --ignored"]
async fn lm_studio_should_detect_overflow_via_is_context_overflow() {
    let model = local_model(
        "local-model",
        "lm-studio",
        "http://localhost:1234/v1",
        false,
        8192,
        2048,
        "LM Studio Local Model",
    );
    assert_local_llm_enabled();
    assert!(
        probe("http://localhost:1234/v1/models").await,
        "LM Studio is not running on localhost:1234"
    );
    expect_error_overflow(&model, "lm-studio", None).await;
}

/// TS probe: `/health` answers and `POST /v1/completions` is not 404/405/000.
async fn llama_cpp_running() -> bool {
    if !probe("http://localhost:8081/health").await {
        return false;
    }
    let status = reqwest::Client::new()
        .post("http://localhost:8081/v1/completions")
        .timeout(Duration::from_secs(1))
        .header("content-type", "application/json")
        .body(r#"{"model":"local-model","prompt":"ping","max_tokens":1}"#)
        .send()
        .await
        .map_or(0, |response| response.status().as_u16());
    status != 404 && status != 405 && status != 0
}

#[tokio::test]
#[ignore = "needs a llama.cpp server on localhost:8081 exposing /v1/completions and PI_NO_LOCAL_LLM unset; run with --ignored"]
async fn llama_cpp_should_detect_overflow_via_is_context_overflow() {
    // Small context (4096) to match the server --ctx-size setting.
    let model = local_model(
        "local-model",
        "llama.cpp",
        "http://localhost:8081/v1",
        false,
        4096,
        2048,
        "llama.cpp Local Model",
    );
    assert_local_llm_enabled();
    assert!(
        llama_cpp_running().await,
        "llama.cpp is not running on localhost:8081 with /v1/completions"
    );
    expect_error_overflow(&model, "llama.cpp", None).await;
}
