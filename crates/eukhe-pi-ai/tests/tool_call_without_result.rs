//! Port of `test/tool-call-without-result.test.ts`.
//!
//! Every case talks to a real provider, so each is `#[ignore]`d with the
//! credentials it needs. TS `describe.skipIf(!process.env.X)` becomes a
//! check that fails with a clear message when the variable is missing; the
//! OAuth suites read the resolved token from `PI_TEST_<PROVIDER>_TOKEN`
//! (TS `resolveApiKey` from `test/oauth.ts`). TS `{ retry: 3 }` is kept as up
//! to three attempts.

mod anthropic_support;
mod openai_responses_support;

use std::time::{SystemTime, UNIX_EPOCH};

use anthropic_support::resolve_test_api_key;
use eukhe_pi_ai::compat::{complete, get_model};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{AssistantContentBlock, Context, JsonValue, Message, Model, StopReason};
use openai_responses_support::azure::{
    has_azure_openai_credentials, resolve_azure_deployment_name,
};
use serde_json::json;

/// `Date.now()`.
fn now() -> u64 {
    let elapsed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after epoch");
    u64::try_from(elapsed.as_millis()).expect("epoch millis fit u64")
}

fn env_set(name: &str) -> bool {
    std::env::var(name).is_ok_and(|value| !value.is_empty())
}

/// TS `calculateTool` (`Type.Object` with a described `Type.String`).
fn calculate_tool() -> JsonValue {
    json!({
        "name": "calculate",
        "description": "Evaluate mathematical expressions",
        "parameters": {
            "type": "object",
            "properties": {
                "expression": {
                    "description": "The mathematical expression to evaluate",
                    "type": "string",
                },
            },
            "required": ["expression"],
        },
    })
}

/// The credentials a TS suite's `skipIf` checks.
#[derive(Clone, Copy)]
enum Auth {
    /// `process.env.<NAME>`.
    Env(&'static str),
    /// TS `hasAzureOpenAICredentials()`; passes `azureDeploymentName` when mapped.
    Azure,
    /// TS `hasBedrockCredentials()`.
    Bedrock,
    /// TS `hasCloudflareWorkersAICredentials()`.
    CloudflareWorkersAi,
    /// TS `hasCloudflareAiGatewayCredentials()`.
    CloudflareAiGateway,
    /// TS `resolveApiKey(provider)`, passed as `apiKey`.
    OAuthToken(&'static str),
}

/// How the suite derives its model from the catalog entry.
#[derive(Clone, Copy)]
enum ModelShape {
    /// `getModel(provider, id)`.
    Catalog,
    /// `{ ...baseModel without compat, api: "openai-completions" }`.
    OpenAiCompletionsWithoutCompat,
}

struct Target {
    provider: &'static str,
    model: &'static str,
    shape: ModelShape,
    auth: Auth,
    /// Extra stream options (TS `StreamOptionsWithExtras`).
    extra: JsonValue,
}

impl Target {
    const fn new(provider: &'static str, model: &'static str, auth: Auth) -> Self {
        Self {
            provider,
            model,
            shape: ModelShape::Catalog,
            auth,
            extra: JsonValue::Null,
        }
    }

    fn with_shape(mut self, shape: ModelShape) -> Self {
        self.shape = shape;
        self
    }

    fn with_extra(mut self, extra: JsonValue) -> Self {
        self.extra = extra;
        self
    }

    fn model(&self) -> Model {
        let mut model = get_model(self.provider, self.model)
            .unwrap_or_else(|| panic!("built-in model {}/{}", self.provider, self.model));
        match self.shape {
            ModelShape::Catalog => {}
            ModelShape::OpenAiCompletionsWithoutCompat => {
                model.compat = None;
                model.api = "openai-completions".into();
            }
        }
        model
    }

    /// Fails with a clear message when the suite's credentials are missing.
    fn options(&self) -> ProviderStreamOptions {
        let mut options = ProviderStreamOptions::default();
        match self.auth {
            Auth::Env(name) => assert!(env_set(name), "{name} is not set"),
            Auth::Azure => {
                assert!(
                    has_azure_openai_credentials(),
                    "AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME are not set"
                );
                if let Some(name) = resolve_azure_deployment_name(self.model) {
                    options
                        .extra
                        .insert("azureDeploymentName".into(), json!(name));
                }
            }
            Auth::Bedrock => assert!(
                env_set("AWS_PROFILE")
                    || (env_set("AWS_ACCESS_KEY_ID") && env_set("AWS_SECRET_ACCESS_KEY"))
                    || env_set("AWS_BEARER_TOKEN_BEDROCK"),
                "AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK is not set"
            ),
            Auth::CloudflareWorkersAi => assert!(
                env_set("CLOUDFLARE_API_KEY") && env_set("CLOUDFLARE_ACCOUNT_ID"),
                "CLOUDFLARE_API_KEY and CLOUDFLARE_ACCOUNT_ID are not set"
            ),
            Auth::CloudflareAiGateway => assert!(
                env_set("CLOUDFLARE_API_KEY")
                    && env_set("CLOUDFLARE_ACCOUNT_ID")
                    && env_set("CLOUDFLARE_GATEWAY_ID"),
                "CLOUDFLARE_API_KEY, CLOUDFLARE_ACCOUNT_ID and CLOUDFLARE_GATEWAY_ID are not set"
            ),
            Auth::OAuthToken(provider) => {
                let token = resolve_test_api_key(provider).unwrap_or_else(|| {
                    panic!(
                        "PI_TEST_{}_TOKEN is not set",
                        provider.to_uppercase().replace('-', "_")
                    )
                });
                options.stream.request.api_key = Some(token);
            }
        }
        if let Some(extra) = self.extra.as_object() {
            for (key, value) in extra {
                options.extra.insert(key.clone(), value.clone());
            }
        }
        options
    }
}

fn user_message(text: &str) -> Message {
    serde_json::from_value(json!({ "role": "user", "content": text, "timestamp": now() }))
        .expect("user message")
}

/// TS `testToolCallWithoutResult`; `Err` describes the failed expectation.
async fn attempt(target: &Target) -> Result<(), String> {
    let model = target.model();
    // Step 1: Create context with the calculate tool
    let mut context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are a helpful assistant. Use the calculate tool when asked to perform calculations.",
        "messages": [],
        "tools": [calculate_tool()],
    }))
    .expect("context");

    // Step 2: Ask the LLM to make a tool call
    context.messages.push(user_message(
        "Please calculate 25 * 18 using the calculate tool.",
    ));

    // Step 3: Get the assistant's response (should contain a tool call)
    let first_response = complete(&model, context.clone(), target.options())
        .await
        .map_err(|error| error.to_string())?;
    println!(
        "First response: {}",
        serde_json::to_string_pretty(&first_response).expect("response json")
    );
    let has_tool_call = first_response
        .content
        .iter()
        .any(|block| matches!(block, AssistantContentBlock::ToolCall(_)));
    context.messages.push(Message::Assistant(first_response));
    if !has_tool_call {
        return Err("Expected assistant to make a tool call, but none was found".to_owned());
    }

    // Step 4: Send a user message WITHOUT providing tool result
    context
        .messages
        .push(user_message("Never mind, just tell me what is 2+2?"));

    // Step 5: The fix should filter out the orphaned tool call, and the request should succeed
    let second_response = complete(&model, context, target.options())
        .await
        .map_err(|error| error.to_string())?;
    println!(
        "Second response: {}",
        serde_json::to_string_pretty(&second_response).expect("response json")
    );

    if second_response.stop_reason == StopReason::Error {
        return Err(format!(
            "second response errored: {:?}",
            second_response.error_message
        ));
    }
    if second_response.content.is_empty() {
        return Err("second response has no content".to_owned());
    }
    let text_content = second_response
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join(" ");
    let tool_calls = second_response
        .content
        .iter()
        .filter(|block| matches!(block, AssistantContentBlock::ToolCall(_)))
        .count();
    if tool_calls == 0 && text_content.is_empty() {
        return Err("second response has neither text nor tool calls".to_owned());
    }
    println!("Answer: {text_content}");

    if !matches!(
        second_response.stop_reason,
        StopReason::Stop | StopReason::ToolUse
    ) {
        return Err(format!(
            "expected stopReason stop or toolUse, got {:?}",
            second_response.stop_reason
        ));
    }
    Ok(())
}

/// TS `{ retry: 3 }`: up to three attempts.
async fn run(target: Target) {
    let mut last = Ok(());
    for _attempt in 0..3 {
        last = attempt(&target).await;
        if last.is_ok() {
            return;
        }
    }
    if let Err(error) = last {
        panic!("{error}");
    }
}

/// One TS `it("should filter out tool calls without corresponding tool results")`.
macro_rules! tool_call_case {
    ($name:ident, $reason:literal, $target:expr) => {
        #[tokio::test]
        #[ignore = $reason]
        async fn $name() {
            run($target).await;
        }
    };
}

tool_call_case!(
    google_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs GEMINI_API_KEY; run with --ignored",
    Target::new("google", "gemini-2.5-flash", Auth::Env("GEMINI_API_KEY"))
);
tool_call_case!(
    openai_completions_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs OPENAI_API_KEY; run with --ignored",
    Target::new("openai", "gpt-4o-mini", Auth::Env("OPENAI_API_KEY"))
        .with_shape(ModelShape::OpenAiCompletionsWithoutCompat)
);
tool_call_case!(
    openai_responses_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs OPENAI_API_KEY; run with --ignored",
    Target::new("openai", "gpt-5-mini", Auth::Env("OPENAI_API_KEY"))
);
tool_call_case!(
    azure_openai_responses_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored",
    Target::new("azure", "gpt-4o-mini", Auth::Azure)
);
tool_call_case!(
    anthropic_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs ANTHROPIC_API_KEY; run with --ignored",
    Target::new(
        "anthropic",
        "claude-haiku-4-5",
        Auth::Env("ANTHROPIC_API_KEY")
    )
);
tool_call_case!(
    xai_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs XAI_API_KEY; run with --ignored",
    Target::new("xai", "grok-4.3", Auth::Env("XAI_API_KEY"))
);
tool_call_case!(
    groq_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs GROQ_API_KEY; run with --ignored",
    Target::new("groq", "openai/gpt-oss-20b", Auth::Env("GROQ_API_KEY"))
);
tool_call_case!(
    cerebras_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs CEREBRAS_API_KEY; run with --ignored",
    Target::new("cerebras", "gpt-oss-120b", Auth::Env("CEREBRAS_API_KEY"))
);
tool_call_case!(
    cloudflare_workers_ai_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs CLOUDFLARE_API_KEY and CLOUDFLARE_ACCOUNT_ID; run with --ignored",
    Target::new(
        "cloudflare-workers-ai",
        "@cf/moonshotai/kimi-k2.6",
        Auth::CloudflareWorkersAi
    )
);
tool_call_case!(
    cloudflare_ai_gateway_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs CLOUDFLARE_API_KEY, CLOUDFLARE_ACCOUNT_ID and CLOUDFLARE_GATEWAY_ID; run with --ignored",
    Target::new(
        "cloudflare-ai-gateway",
        "workers-ai/@cf/moonshotai/kimi-k2.6",
        Auth::CloudflareAiGateway
    )
);
tool_call_case!(
    hugging_face_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs HF_TOKEN; run with --ignored",
    Target::new("huggingface", "moonshotai/Kimi-K2.5", Auth::Env("HF_TOKEN"))
);
tool_call_case!(
    together_ai_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs TOGETHER_API_KEY; run with --ignored",
    Target::new(
        "together",
        "moonshotai/Kimi-K3",
        Auth::Env("TOGETHER_API_KEY")
    )
    .with_extra(json!({ "reasoningEffort": "high" }))
);
tool_call_case!(
    baseten_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs BASETEN_API_KEY; run with --ignored",
    Target::new("baseten", "zai-org/GLM-5.2", Auth::Env("BASETEN_API_KEY"))
        .with_extra(json!({ "reasoningEffort": "high" }))
);
tool_call_case!(
    zai_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs ZAI_API_KEY; run with --ignored",
    Target::new("zai", "glm-5.2", Auth::Env("ZAI_API_KEY"))
);
tool_call_case!(
    mistral_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs MISTRAL_API_KEY; run with --ignored",
    Target::new(
        "mistral",
        "devstral-medium-latest",
        Auth::Env("MISTRAL_API_KEY")
    )
);
tool_call_case!(
    minimax_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs MINIMAX_API_KEY; run with --ignored",
    Target::new("minimax", "MiniMax-M2.7", Auth::Env("MINIMAX_API_KEY"))
);
tool_call_case!(
    xiaomi_mimo_api_billing_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs XIAOMI_API_KEY; run with --ignored",
    Target::new("xiaomi", "mimo-v2.5-pro", Auth::Env("XIAOMI_API_KEY"))
);
tool_call_case!(
    xiaomi_mimo_token_plan_cn_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored",
    Target::new(
        "xiaomi-token-plan-cn",
        "mimo-v2.5-pro",
        Auth::Env("XIAOMI_TOKEN_PLAN_CN_API_KEY")
    )
);
tool_call_case!(
    xiaomi_mimo_token_plan_ams_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored",
    Target::new(
        "xiaomi-token-plan-ams",
        "mimo-v2.5-pro",
        Auth::Env("XIAOMI_TOKEN_PLAN_AMS_API_KEY")
    )
);
tool_call_case!(
    xiaomi_mimo_token_plan_sgp_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored",
    Target::new(
        "xiaomi-token-plan-sgp",
        "mimo-v2.5-pro",
        Auth::Env("XIAOMI_TOKEN_PLAN_SGP_API_KEY")
    )
);
tool_call_case!(
    qwen_token_plan_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored",
    Target::new(
        "qwen-token-plan",
        "qwen3.7-max",
        Auth::Env("QWEN_TOKEN_PLAN_API_KEY")
    )
);
tool_call_case!(
    qwen_token_plan_individual_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored",
    Target::new(
        "qwen-token-plan-individual",
        "qwen3.8-max",
        Auth::Env("QWEN_TOKEN_PLAN_API_KEY")
    )
);
tool_call_case!(
    qwen_token_plan_cn_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored",
    Target::new(
        "qwen-token-plan-cn",
        "qwen3.7-max",
        Auth::Env("QWEN_TOKEN_PLAN_CN_API_KEY")
    )
);
tool_call_case!(
    kimi_for_coding_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs KIMI_API_KEY; run with --ignored",
    Target::new("kimi-coding", "kimi-for-coding", Auth::Env("KIMI_API_KEY"))
);
tool_call_case!(
    vercel_ai_gateway_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs AI_GATEWAY_API_KEY; run with --ignored",
    Target::new(
        "vercel-ai-gateway",
        "google/gemini-2.5-flash",
        Auth::Env("AI_GATEWAY_API_KEY")
    )
);
tool_call_case!(
    amazon_bedrock_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored",
    Target::new(
        "amazon-bedrock",
        "global.anthropic.claude-sonnet-4-5-20250929-v1:0",
        Auth::Bedrock
    )
);
tool_call_case!(
    anthropic_oauth_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs PI_TEST_ANTHROPIC_TOKEN; run with --ignored",
    Target::new(
        "anthropic",
        "claude-haiku-4-5",
        Auth::OAuthToken("anthropic")
    )
);
tool_call_case!(
    github_copilot_claude_haiku_4_5_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored",
    Target::new(
        "github-copilot",
        "claude-haiku-4.5",
        Auth::OAuthToken("github-copilot")
    )
);
// TS labels this case "claude-sonnet-4" while requesting `claude-sonnet-4.6`.
tool_call_case!(
    github_copilot_claude_sonnet_4_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored",
    Target::new(
        "github-copilot",
        "claude-sonnet-4.6",
        Auth::OAuthToken("github-copilot")
    )
);
tool_call_case!(
    openai_codex_gpt_5_5_should_filter_out_tool_calls_without_corresponding_tool_results,
    "needs PI_TEST_OPENAI_CODEX_TOKEN; run with --ignored",
    Target::new("openai-codex", "gpt-5.5", Auth::OAuthToken("openai-codex"))
);
