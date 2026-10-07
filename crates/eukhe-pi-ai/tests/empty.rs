//! Port of `test/empty.test.ts`.
//!
//! Every case talks to a real provider, so each is `#[ignore]`d with the
//! credentials it needs. TS `describe.skipIf(!process.env.X)` becomes a
//! check that fails with a clear message when the variable is missing; the
//! OAuth suites read the resolved token from `PI_TEST_<PROVIDER>_TOKEN`
//! (TS `resolveApiKey` from `test/oauth.ts`). TS `{ retry: 3 }` is kept as up
//! to three attempts. TS `expect(response.role).toBe("assistant")` holds by
//! construction: `complete` returns an `AssistantMessage`.

mod anthropic_support;
mod openai_responses_support;

use std::time::{SystemTime, UNIX_EPOCH};

use anthropic_support::resolve_test_api_key;
use eukhe_pi_ai::compat::{complete, get_model};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{Context, JsonValue, Model, StopReason};
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

struct Target {
    provider: &'static str,
    model: &'static str,
    auth: Auth,
    /// Extra stream options (TS `StreamOptionsWithExtras`).
    extra: JsonValue,
}

impl Target {
    const fn new(provider: &'static str, model: &'static str, auth: Auth) -> Self {
        Self {
            provider,
            model,
            auth,
            extra: JsonValue::Null,
        }
    }

    fn with_extra(mut self, extra: JsonValue) -> Self {
        self.extra = extra;
        self
    }

    fn model(&self) -> Model {
        get_model(self.provider, self.model)
            .unwrap_or_else(|| panic!("built-in model {}/{}", self.provider, self.model))
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

#[derive(Clone, Copy)]
enum Case {
    /// TS `testEmptyMessage`.
    EmptyContentArray,
    /// TS `testEmptyStringMessage`.
    EmptyStringContent,
    /// TS `testWhitespaceOnlyMessage`.
    WhitespaceOnlyContent,
    /// TS `testEmptyAssistantMessage`.
    EmptyAssistantMessage,
}

fn case_context(case: Case, model: &Model) -> Context {
    let messages = match case {
        Case::EmptyContentArray => json!([{ "role": "user", "content": [], "timestamp": now() }]),
        Case::EmptyStringContent => json!([{ "role": "user", "content": "", "timestamp": now() }]),
        Case::WhitespaceOnlyContent => {
            json!([{ "role": "user", "content": "   \n\t  ", "timestamp": now() }])
        }
        Case::EmptyAssistantMessage => json!([
            { "role": "user", "content": "Hello, how are you?", "timestamp": now() },
            {
                "role": "assistant",
                "content": [],
                "api": model.api,
                "provider": model.provider,
                "model": model.id,
                "usage": {
                    "input": 10,
                    "output": 0,
                    "cacheRead": 0,
                    "cacheWrite": 0,
                    "totalTokens": 10,
                    "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                },
                "stopReason": "stop",
                "timestamp": now(),
            },
            { "role": "user", "content": "Please respond this time.", "timestamp": now() },
        ]),
    };
    serde_json::from_value(json!({ "messages": messages })).expect("context")
}

/// One attempt; `Err` describes the failed expectation.
async fn attempt(case: Case, target: &Target) -> Result<(), String> {
    let model = target.model();
    let context = case_context(case, &model);
    let response = complete(&model, context, target.options())
        .await
        .map_err(|error| error.to_string())?;
    if response.stop_reason == StopReason::Error {
        if response.error_message.is_none() {
            return Err("stopReason is error but errorMessage is undefined".to_owned());
        }
    } else if matches!(case, Case::EmptyAssistantMessage) && response.content.is_empty() {
        return Err("expected non-empty content".to_owned());
    }
    Ok(())
}

/// TS `{ retry: 3 }`: up to three attempts.
async fn run(case: Case, target: Target) {
    let mut last = Ok(());
    for _attempt in 0..3 {
        last = attempt(case, &target).await;
        if last.is_ok() {
            return;
        }
    }
    if let Err(error) = last {
        panic!("{error}");
    }
}

/// One TS suite: the four cases against `$target`.
macro_rules! empty_suite {
    ($suite:ident, $reason:literal, $target:expr) => {
        mod $suite {
            use super::*;

            #[tokio::test]
            #[ignore = $reason]
            async fn should_handle_empty_content_array() {
                run(Case::EmptyContentArray, $target).await;
            }

            #[tokio::test]
            #[ignore = $reason]
            async fn should_handle_empty_string_content() {
                run(Case::EmptyStringContent, $target).await;
            }

            #[tokio::test]
            #[ignore = $reason]
            async fn should_handle_whitespace_only_content() {
                run(Case::WhitespaceOnlyContent, $target).await;
            }

            #[tokio::test]
            #[ignore = $reason]
            async fn should_handle_empty_assistant_message_in_conversation() {
                run(Case::EmptyAssistantMessage, $target).await;
            }
        }
    };
}

empty_suite!(
    google,
    "needs GEMINI_API_KEY; run with --ignored",
    Target::new("google", "gemini-2.5-flash", Auth::Env("GEMINI_API_KEY"))
);
empty_suite!(
    openai_completions,
    "needs OPENAI_API_KEY; run with --ignored",
    Target::new("openai", "gpt-4o-mini", Auth::Env("OPENAI_API_KEY"))
);
empty_suite!(
    openai_responses,
    "needs OPENAI_API_KEY; run with --ignored",
    Target::new("openai", "gpt-5-mini", Auth::Env("OPENAI_API_KEY"))
);
empty_suite!(
    azure_openai_responses,
    "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored",
    Target::new("azure", "gpt-4o-mini", Auth::Azure)
);
empty_suite!(
    anthropic,
    "needs ANTHROPIC_API_KEY; run with --ignored",
    Target::new(
        "anthropic",
        "claude-haiku-4-5",
        Auth::Env("ANTHROPIC_API_KEY")
    )
);
empty_suite!(
    xai,
    "needs XAI_API_KEY; run with --ignored",
    Target::new("xai", "grok-4.3", Auth::Env("XAI_API_KEY"))
);
empty_suite!(
    groq,
    "needs GROQ_API_KEY; run with --ignored",
    Target::new("groq", "openai/gpt-oss-20b", Auth::Env("GROQ_API_KEY"))
);
empty_suite!(
    cerebras,
    "needs CEREBRAS_API_KEY; run with --ignored",
    Target::new("cerebras", "gpt-oss-120b", Auth::Env("CEREBRAS_API_KEY"))
);
empty_suite!(
    cloudflare_workers_ai,
    "needs CLOUDFLARE_API_KEY and CLOUDFLARE_ACCOUNT_ID; run with --ignored",
    Target::new(
        "cloudflare-workers-ai",
        "@cf/moonshotai/kimi-k2.6",
        Auth::CloudflareWorkersAi
    )
);
empty_suite!(
    cloudflare_ai_gateway,
    "needs CLOUDFLARE_API_KEY, CLOUDFLARE_ACCOUNT_ID and CLOUDFLARE_GATEWAY_ID; run with --ignored",
    Target::new(
        "cloudflare-ai-gateway",
        "workers-ai/@cf/moonshotai/kimi-k2.6",
        Auth::CloudflareAiGateway
    )
);
empty_suite!(
    hugging_face,
    "needs HF_TOKEN; run with --ignored",
    Target::new("huggingface", "moonshotai/Kimi-K2.5", Auth::Env("HF_TOKEN"))
);
empty_suite!(
    together_ai,
    "needs TOGETHER_API_KEY; run with --ignored",
    Target::new(
        "together",
        "moonshotai/Kimi-K3",
        Auth::Env("TOGETHER_API_KEY")
    )
);
empty_suite!(
    baseten,
    "needs BASETEN_API_KEY; run with --ignored",
    Target::new("baseten", "zai-org/GLM-5.2", Auth::Env("BASETEN_API_KEY"))
        .with_extra(json!({ "reasoningEffort": "high" }))
);
empty_suite!(
    zai,
    "needs ZAI_API_KEY; run with --ignored",
    Target::new("zai", "glm-5.2", Auth::Env("ZAI_API_KEY"))
);
empty_suite!(
    mistral,
    "needs MISTRAL_API_KEY; run with --ignored",
    Target::new(
        "mistral",
        "devstral-medium-latest",
        Auth::Env("MISTRAL_API_KEY")
    )
);
empty_suite!(
    minimax,
    "needs MINIMAX_API_KEY; run with --ignored",
    Target::new("minimax", "MiniMax-M2.7", Auth::Env("MINIMAX_API_KEY"))
);
empty_suite!(
    xiaomi_mimo_api_billing,
    "needs XIAOMI_API_KEY; run with --ignored",
    Target::new("xiaomi", "mimo-v2.5-pro", Auth::Env("XIAOMI_API_KEY"))
);
empty_suite!(
    xiaomi_mimo_token_plan_cn,
    "needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored",
    Target::new(
        "xiaomi-token-plan-cn",
        "mimo-v2.5-pro",
        Auth::Env("XIAOMI_TOKEN_PLAN_CN_API_KEY")
    )
);
empty_suite!(
    xiaomi_mimo_token_plan_ams,
    "needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored",
    Target::new(
        "xiaomi-token-plan-ams",
        "mimo-v2.5-pro",
        Auth::Env("XIAOMI_TOKEN_PLAN_AMS_API_KEY")
    )
);
empty_suite!(
    xiaomi_mimo_token_plan_sgp,
    "needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored",
    Target::new(
        "xiaomi-token-plan-sgp",
        "mimo-v2.5-pro",
        Auth::Env("XIAOMI_TOKEN_PLAN_SGP_API_KEY")
    )
);
empty_suite!(
    qwen_token_plan,
    "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored",
    Target::new(
        "qwen-token-plan",
        "qwen3.7-max",
        Auth::Env("QWEN_TOKEN_PLAN_API_KEY")
    )
);
empty_suite!(
    qwen_token_plan_individual,
    "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored",
    Target::new(
        "qwen-token-plan-individual",
        "qwen3.8-max",
        Auth::Env("QWEN_TOKEN_PLAN_API_KEY")
    )
);
empty_suite!(
    qwen_token_plan_cn,
    "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored",
    Target::new(
        "qwen-token-plan-cn",
        "qwen3.7-max",
        Auth::Env("QWEN_TOKEN_PLAN_CN_API_KEY")
    )
);
empty_suite!(
    kimi_for_coding,
    "needs KIMI_API_KEY; run with --ignored",
    Target::new("kimi-coding", "kimi-for-coding", Auth::Env("KIMI_API_KEY"))
);
empty_suite!(
    vercel_ai_gateway,
    "needs AI_GATEWAY_API_KEY; run with --ignored",
    Target::new(
        "vercel-ai-gateway",
        "google/gemini-2.5-flash",
        Auth::Env("AI_GATEWAY_API_KEY")
    )
);
empty_suite!(
    amazon_bedrock,
    "needs AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored",
    Target::new(
        "amazon-bedrock",
        "global.anthropic.claude-sonnet-4-5-20250929-v1:0",
        Auth::Bedrock
    )
);
empty_suite!(
    anthropic_oauth,
    "needs PI_TEST_ANTHROPIC_TOKEN; run with --ignored",
    Target::new(
        "anthropic",
        "claude-haiku-4-5",
        Auth::OAuthToken("anthropic")
    )
);
empty_suite!(
    github_copilot_claude_haiku_4_5,
    "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored",
    Target::new(
        "github-copilot",
        "claude-haiku-4.5",
        Auth::OAuthToken("github-copilot")
    )
);
// TS labels this suite "claude-sonnet-4" while requesting `claude-sonnet-4.6`.
empty_suite!(
    github_copilot_claude_sonnet_4,
    "needs PI_TEST_GITHUB_COPILOT_TOKEN; run with --ignored",
    Target::new(
        "github-copilot",
        "claude-sonnet-4.6",
        Auth::OAuthToken("github-copilot")
    )
);
empty_suite!(
    openai_codex_gpt_5_5,
    "needs PI_TEST_OPENAI_CODEX_TOKEN; run with --ignored",
    Target::new("openai-codex", "gpt-5.5", Auth::OAuthToken("openai-codex"))
);
