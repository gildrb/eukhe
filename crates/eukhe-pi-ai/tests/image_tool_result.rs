//! Port of `test/image-tool-result.test.ts`: tool results with images across
//! all providers.
//!
//! Every case talks to a live provider and is `#[ignore]`d with the
//! credentials it needs. TS `describe.skipIf(!process.env.X)` becomes a check
//! that fails with a clear message when `X` is missing. OAuth tokens that TS
//! resolves with `test/oauth.ts` are read from `PI_TEST_<PROVIDER>_TOKEN`.
//! TS `{ retry: N }` runs the case up to N times.

use std::any::Any;
use std::future::Future;
use std::panic::AssertUnwindSafe;

use base64::Engine as _;
use eukhe_pi_ai::compat::{complete, get_model};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, Context, JsonValue, Message, Modality, Model, StopReason,
};
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

fn red_circle_base64() -> String {
    let image_path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/red-circle.png");
    base64::engine::general_purpose::STANDARD.encode(std::fs::read(image_path).expect("image"))
}

/// The first text block of an assistant message.
fn first_text(content: &[AssistantContentBlock]) -> Option<&str> {
    content.iter().find_map(|block| match block {
        AssistantContentBlock::Text(text) => Some(text.text.as_str()),
        AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
    })
}

/// The tool round shared by both TS helpers: the model must call `tool_name`,
/// then answer with `stop` after a tool result of `result_content`. Returns
/// the lowercased first text block of the second response.
async fn tool_round(
    model: &Model,
    options: &ProviderStreamOptions,
    tool: &JsonValue,
    prompt: &str,
    result_content: impl FnOnce(String) -> JsonValue,
) -> String {
    let tool_name = tool["name"].as_str().expect("tool name").to_owned();
    let mut context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are a helpful assistant that uses tools when asked.",
        "messages": [{ "role": "user", "content": prompt, "timestamp": now() }],
        "tools": [tool],
    }))
    .expect("context");

    // First request - LLM should call the tool
    let first_response = complete(model, context.clone(), options.clone())
        .await
        .expect("first response");
    assert_eq!(
        first_response.stop_reason,
        StopReason::ToolUse,
        "Error: {:?}",
        first_response.error_message
    );

    // Find the tool call
    let tool_call = first_response
        .content
        .iter()
        .find_map(|block| match block {
            AssistantContentBlock::ToolCall(call) => Some(call.clone()),
            AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
        })
        .expect("Expected tool call");
    assert_eq!(tool_call.name, tool_name);

    // Add the tool call to context
    context
        .messages
        .push(Message::Assistant(first_response.clone()));

    context.messages.push(
        serde_json::from_value(json!({
            "role": "toolResult",
            "toolCallId": tool_call.id,
            "toolName": tool_call.name,
            "content": result_content(red_circle_base64()),
            "isError": false,
            "timestamp": now(),
        }))
        .expect("tool result"),
    );

    // Second request - LLM should describe the tool result
    let second_response = complete(model, context, options.clone())
        .await
        .expect("second response");
    assert_eq!(
        second_response.stop_reason,
        StopReason::Stop,
        "Error: {:?}",
        second_response.error_message
    );
    assert!(second_response
        .error_message
        .as_deref()
        .is_none_or(str::is_empty));

    first_text(&second_response.content)
        .expect("Expected text content")
        .to_lowercase()
}

/// Test that tool results containing only images work correctly across all providers.
/// This verifies that:
/// 1. Tool results can contain image content blocks
/// 2. Providers correctly pass images from tool results to the LLM
/// 3. The LLM can see and describe images returned by tools
async fn handle_tool_with_image_result(model: &Model, options: &ProviderStreamOptions) {
    // Check if the model supports images
    if !model.input.contains(&Modality::Image) {
        println!(
            "Skipping tool image result test - model {} doesn't support images",
            model.id
        );
        return;
    }

    // Define a tool that returns only an image (no text)
    let get_image_tool = json!({
        "name": "get_circle",
        "description": "Returns a circle image for visualization",
        "parameters": { "type": "object", "properties": {} },
    });

    let lower_content = tool_round(
        model,
        options,
        &get_image_tool,
        "Call the get_circle tool to get an image, and describe what you see, shapes, colors, etc.",
        // Create tool result with ONLY an image (no text)
        |base64_image| json!([{ "type": "image", "data": base64_image, "mimeType": "image/png" }]),
    )
    .await;

    // Should mention red and circle since that's what the image shows
    assert!(lower_content.contains("red"), "{lower_content}");
    assert!(lower_content.contains("circle"), "{lower_content}");
}

/// Test that tool results containing both text and images work correctly across all providers.
/// This verifies that:
/// 1. Tool results can contain mixed content blocks (text + images)
/// 2. Providers correctly pass both text and images from tool results to the LLM
/// 3. The LLM can see both the text and images in tool results
async fn handle_tool_with_text_and_image_result(model: &Model, options: &ProviderStreamOptions) {
    // Check if the model supports images
    if !model.input.contains(&Modality::Image) {
        println!(
            "Skipping tool text+image result test - model {} doesn't support images",
            model.id
        );
        return;
    }

    // Define a tool that returns both text and an image
    let get_image_tool = json!({
        "name": "get_circle_with_description",
        "description": "Returns a circle image with a text description",
        "parameters": { "type": "object", "properties": {} },
    });

    let lower_content = tool_round(
        model,
        options,
        &get_image_tool,
        "Use the get_circle_with_description tool and tell me what you learned. Also say what color the shape is.",
        // Create tool result with BOTH text and image
        |base64_image| {
            json!([
                {
                    "type": "text",
                    "text": "This is a geometric shape with specific properties: it has a diameter of 100 pixels.",
                },
                { "type": "image", "data": base64_image, "mimeType": "image/png" },
            ])
        },
    )
    .await;

    // Should mention details from the text (diameter/pixels)
    assert!(
        ["diameter", "100", "pixel"]
            .iter()
            .any(|word| lower_content.contains(word)),
        "{lower_content}"
    );
    // Should also mention the visual properties (red and circle)
    assert!(lower_content.contains("red"), "{lower_content}");
    assert!(lower_content.contains("circle"), "{lower_content}");
}

/// Which TS helper a case runs.
#[derive(Clone, Copy)]
enum Case {
    OnlyImage,
    TextAndImage,
}

async fn run(case: Case, attempts: usize, llm: &Model, api_key: Option<&str>, extra: &JsonValue) {
    let options = options(api_key.map(str::to_owned), extra);
    with_retry(attempts, || async {
        match case {
            Case::OnlyImage => handle_tool_with_image_result(llm, &options).await,
            Case::TextAndImage => handle_tool_with_text_and_image_result(llm, &options).await,
        }
    })
    .await;
}

/// A `describe.skipIf(!process.env.<var>)` provider case with `{ retry: 3 }`.
async fn run_env(case: Case, var: &str, provider: &str, id: &str, extra: &JsonValue) {
    require_env(var);
    run(case, 3, &model(provider, id), None, extra).await;
}

// Google Provider (gemini-2.5-flash)

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn google_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "GEMINI_API_KEY",
        "google",
        "gemini-2.5-flash",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs GEMINI_API_KEY; run with --ignored"]
async fn google_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "GEMINI_API_KEY",
        "google",
        "gemini-2.5-flash",
        &json!({}),
    )
    .await;
}

// OpenAI Completions Provider (gpt-4o-mini)

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_completions_should_handle_tool_result_with_only_image() {
    require_env("OPENAI_API_KEY");
    let llm = as_openai_completions(&model("openai", "gpt-4o-mini"));
    run(Case::OnlyImage, 3, &llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_completions_should_handle_tool_result_with_text_and_image() {
    require_env("OPENAI_API_KEY");
    let llm = as_openai_completions(&model("openai", "gpt-4o-mini"));
    run(Case::TextAndImage, 3, &llm, None, &json!({})).await;
}

// OpenAI Responses Provider (gpt-5-mini)

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "OPENAI_API_KEY",
        "openai",
        "gpt-5-mini",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "OPENAI_API_KEY",
        "openai",
        "gpt-5-mini",
        &json!({}),
    )
    .await;
}

// Azure OpenAI Responses Provider (gpt-4o-mini)

async fn run_azure(case: Case) {
    require_azure_openai_credentials();
    let llm = model("azure", "gpt-4o-mini");
    let azure_options = resolve_azure_deployment_name(&llm.id)
        .map_or_else(|| json!({}), |name| json!({ "azureDeploymentName": name }));
    run(case, 3, &llm, None, &azure_options).await;
}

#[tokio::test]
#[ignore = "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored"]
async fn azure_openai_responses_should_handle_tool_result_with_only_image() {
    run_azure(Case::OnlyImage).await;
}

#[tokio::test]
#[ignore = "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored"]
async fn azure_openai_responses_should_handle_tool_result_with_text_and_image() {
    run_azure(Case::TextAndImage).await;
}

// Anthropic Provider (claude-haiku-4-5)

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn anthropic_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "ANTHROPIC_API_KEY",
        "anthropic",
        "claude-haiku-4-5",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs ANTHROPIC_API_KEY; run with --ignored"]
async fn anthropic_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "ANTHROPIC_API_KEY",
        "anthropic",
        "claude-haiku-4-5",
        &json!({}),
    )
    .await;
}

// OpenRouter Provider (glm-4.5v)

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "OPENROUTER_API_KEY",
        "openrouter",
        "z-ai/glm-4.5v",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn openrouter_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "OPENROUTER_API_KEY",
        "openrouter",
        "z-ai/glm-4.5v",
        &json!({}),
    )
    .await;
}

// Mistral Provider (pixtral-12b), TS `{ retry: 5 }`

#[tokio::test]
#[ignore = "needs MISTRAL_API_KEY; run with --ignored"]
async fn mistral_should_handle_tool_result_with_only_image() {
    require_env("MISTRAL_API_KEY");
    let llm = model("mistral", "pixtral-12b");
    run(Case::OnlyImage, 5, &llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs MISTRAL_API_KEY; run with --ignored"]
async fn mistral_should_handle_tool_result_with_text_and_image() {
    require_env("MISTRAL_API_KEY");
    let llm = model("mistral", "pixtral-12b");
    run(Case::TextAndImage, 5, &llm, None, &json!({})).await;
}

// Together AI Provider (Kimi-K3)

#[tokio::test]
#[ignore = "needs TOGETHER_API_KEY; run with --ignored"]
async fn together_ai_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "TOGETHER_API_KEY",
        "together",
        "moonshotai/Kimi-K3",
        &json!({ "reasoningEffort": "high" }),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs TOGETHER_API_KEY; run with --ignored"]
async fn together_ai_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "TOGETHER_API_KEY",
        "together",
        "moonshotai/Kimi-K3",
        &json!({ "reasoningEffort": "high" }),
    )
    .await;
}

// Baseten Provider (Kimi-K2.6)

#[tokio::test]
#[ignore = "needs BASETEN_API_KEY; run with --ignored"]
async fn baseten_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "BASETEN_API_KEY",
        "baseten",
        "moonshotai/Kimi-K2.6",
        &json!({ "reasoningEffort": "high" }),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs BASETEN_API_KEY; run with --ignored"]
async fn baseten_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "BASETEN_API_KEY",
        "baseten",
        "moonshotai/Kimi-K2.6",
        &json!({ "reasoningEffort": "high" }),
    )
    .await;
}

// Xiaomi MiMo (API billing) Provider (mimo-v2.5-pro)

#[tokio::test]
#[ignore = "needs XIAOMI_API_KEY; run with --ignored"]
async fn xiaomi_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "XIAOMI_API_KEY",
        "xiaomi",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

// FIXME(xiaomi): when a tool_result contains both a descriptive text block
// and an image block, MiMo locks onto the text and ignores the image (it
// reports the text-derived diameter but never mentions the image's color).
// The image-only case above proves the image reaches the model, and the
// text-only path obviously works, so this is a multimodal-fusion quality
// issue in the model, not a transport bug. Re-enable when upstream model
// quality improves.
#[tokio::test]
#[ignore = "it.skip upstream (FIXME xiaomi: multimodal fusion); needs XIAOMI_API_KEY; run with --ignored"]
async fn xiaomi_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "XIAOMI_API_KEY",
        "xiaomi",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

// Xiaomi MiMo Token Plan (CN) Provider (mimo-v2.5-pro)

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_cn_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "XIAOMI_TOKEN_PLAN_CN_API_KEY",
        "xiaomi-token-plan-cn",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

// FIXME(xiaomi): see the API-billing case above — same multimodal-fusion
// limitation applies to Token Plan endpoints (same model behind both).
#[tokio::test]
#[ignore = "it.skip upstream (FIXME xiaomi: multimodal fusion); needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_cn_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "XIAOMI_TOKEN_PLAN_CN_API_KEY",
        "xiaomi-token-plan-cn",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

// Xiaomi MiMo Token Plan (AMS) Provider (mimo-v2.5-pro)

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_ams_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "XIAOMI_TOKEN_PLAN_AMS_API_KEY",
        "xiaomi-token-plan-ams",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

// FIXME(xiaomi): see the API-billing case above.
#[tokio::test]
#[ignore = "it.skip upstream (FIXME xiaomi: multimodal fusion); needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_ams_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "XIAOMI_TOKEN_PLAN_AMS_API_KEY",
        "xiaomi-token-plan-ams",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

// Xiaomi MiMo Token Plan (SGP) Provider (mimo-v2.5-pro)

#[tokio::test]
#[ignore = "needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_sgp_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "XIAOMI_TOKEN_PLAN_SGP_API_KEY",
        "xiaomi-token-plan-sgp",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

// FIXME(xiaomi): see the API-billing case above.
#[tokio::test]
#[ignore = "it.skip upstream (FIXME xiaomi: multimodal fusion); needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored"]
async fn xiaomi_token_plan_sgp_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "XIAOMI_TOKEN_PLAN_SGP_API_KEY",
        "xiaomi-token-plan-sgp",
        "mimo-v2.5-pro",
        &json!({}),
    )
    .await;
}

// Qwen Token Plan Provider (qwen3.7-max)

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "QWEN_TOKEN_PLAN_API_KEY",
        "qwen-token-plan",
        "qwen3.7-max",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "QWEN_TOKEN_PLAN_API_KEY",
        "qwen-token-plan",
        "qwen3.7-max",
        &json!({}),
    )
    .await;
}

// Qwen Token Plan Individual Provider (qwen3.8-max)

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_individual_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "QWEN_TOKEN_PLAN_API_KEY",
        "qwen-token-plan-individual",
        "qwen3.8-max",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored"]
async fn qwen_token_plan_individual_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "QWEN_TOKEN_PLAN_API_KEY",
        "qwen-token-plan-individual",
        "qwen3.8-max",
        &json!({}),
    )
    .await;
}

// Qwen Token Plan (CN) Provider (qwen3.7-max)

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn qwen_token_plan_cn_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "QWEN_TOKEN_PLAN_CN_API_KEY",
        "qwen-token-plan-cn",
        "qwen3.7-max",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored"]
async fn qwen_token_plan_cn_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "QWEN_TOKEN_PLAN_CN_API_KEY",
        "qwen-token-plan-cn",
        "qwen3.7-max",
        &json!({}),
    )
    .await;
}

// Kimi For Coding Provider (kimi-for-coding)

#[tokio::test]
#[ignore = "needs KIMI_API_KEY; run with --ignored"]
async fn kimi_for_coding_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "KIMI_API_KEY",
        "kimi-coding",
        "kimi-for-coding",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs KIMI_API_KEY; run with --ignored"]
async fn kimi_for_coding_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "KIMI_API_KEY",
        "kimi-coding",
        "kimi-for-coding",
        &json!({}),
    )
    .await;
}

// Vercel AI Gateway Provider (google/gemini-2.5-flash)

#[tokio::test]
#[ignore = "needs AI_GATEWAY_API_KEY; run with --ignored"]
async fn vercel_ai_gateway_should_handle_tool_result_with_only_image() {
    run_env(
        Case::OnlyImage,
        "AI_GATEWAY_API_KEY",
        "vercel-ai-gateway",
        "google/gemini-2.5-flash",
        &json!({}),
    )
    .await;
}

#[tokio::test]
#[ignore = "needs AI_GATEWAY_API_KEY; run with --ignored"]
async fn vercel_ai_gateway_should_handle_tool_result_with_text_and_image() {
    run_env(
        Case::TextAndImage,
        "AI_GATEWAY_API_KEY",
        "vercel-ai-gateway",
        "google/gemini-2.5-flash",
        &json!({}),
    )
    .await;
}

// Amazon Bedrock Provider (claude-sonnet-4-5)

async fn run_bedrock(case: Case) {
    require_bedrock_credentials();
    let llm = model(
        "amazon-bedrock",
        "global.anthropic.claude-sonnet-4-5-20250929-v1:0",
    );
    run(case, 3, &llm, None, &json!({})).await;
}

#[tokio::test]
#[ignore = "needs AWS_PROFILE, AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored"]
async fn amazon_bedrock_should_handle_tool_result_with_only_image() {
    run_bedrock(Case::OnlyImage).await;
}

#[tokio::test]
#[ignore = "needs AWS_PROFILE, AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored"]
async fn amazon_bedrock_should_handle_tool_result_with_text_and_image() {
    run_bedrock(Case::TextAndImage).await;
}

// OAuth-based providers (TS: credentials from ~/.pi/agent/oauth.json).

async fn run_oauth(case: Case, provider: &str, id: &str) {
    let token = oauth_token(provider);
    run(case, 3, &model(provider, id), Some(&token), &json!({})).await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_ANTHROPIC_TOKEN (Anthropic OAuth); run with --ignored"]
async fn anthropic_oauth_should_handle_tool_result_with_only_image() {
    run_oauth(Case::OnlyImage, "anthropic", "claude-sonnet-4-5").await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_ANTHROPIC_TOKEN (Anthropic OAuth); run with --ignored"]
async fn anthropic_oauth_should_handle_tool_result_with_text_and_image() {
    run_oauth(Case::TextAndImage, "anthropic", "claude-sonnet-4-5").await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored"]
async fn github_copilot_claude_haiku_4_5_should_handle_tool_result_with_only_image() {
    run_oauth(Case::OnlyImage, "github-copilot", "claude-haiku-4.5").await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored"]
async fn github_copilot_claude_haiku_4_5_should_handle_tool_result_with_text_and_image() {
    run_oauth(Case::TextAndImage, "github-copilot", "claude-haiku-4.5").await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored"]
async fn github_copilot_claude_sonnet_4_should_handle_tool_result_with_only_image() {
    run_oauth(Case::OnlyImage, "github-copilot", "claude-sonnet-4.6").await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored"]
async fn github_copilot_claude_sonnet_4_should_handle_tool_result_with_text_and_image() {
    run_oauth(Case::TextAndImage, "github-copilot", "claude-sonnet-4.6").await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_OPENAI_CODEX_TOKEN; run with --ignored"]
async fn openai_codex_gpt_5_5_should_handle_tool_result_with_only_image() {
    run_oauth(Case::OnlyImage, "openai-codex", "gpt-5.5").await;
}

#[tokio::test]
#[ignore = "needs PI_TEST_OPENAI_CODEX_TOKEN; run with --ignored"]
async fn openai_codex_gpt_5_5_should_handle_tool_result_with_text_and_image() {
    run_oauth(Case::TextAndImage, "openai-codex", "gpt-5.5").await;
}
