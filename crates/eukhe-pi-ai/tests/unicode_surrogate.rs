//! Port of `test/unicode-surrogate.test.ts`: tool results with emoji and
//! other non-BMP characters (and an unpaired high surrogate) must reach every
//! provider as valid JSON. All cases hit real endpoints; the TS suites are
//! skipped without credentials, here they are `#[ignore]`d. TS
//! `resolveApiKey()` OAuth tokens (read from `~/.pi/agent/oauth.json`) come
//! from the env vars named in the ignore reasons. TS `{ retry: 3 }` is a loop
//! of 3 attempts.
//!
//! A Rust `String` cannot hold the unpaired surrogate `0xD83D`; the text is
//! built from UTF-16 code units through `sanitize_surrogates_utf16`, which is
//! what the TS `sanitizeSurrogates` turns it into before the request.

use std::future::Future;

use eukhe_pi_ai::compat::{complete, get_model};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::sanitize_unicode::sanitize_surrogates_utf16;
use eukhe_types::pi_ai::{AssistantContentBlock, Context, Model, StopReason};
use serde_json::{json, Value as JsonValue};

fn env_value(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

fn require_env(name: &str) -> String {
    env_value(name).unwrap_or_else(|| panic!("Missing {name}; this test needs it set"))
}

fn builtin(provider: &str, id: &str) -> Model {
    get_model(provider, id).unwrap_or_else(|| panic!("unknown model {provider}/{id}"))
}

fn options(api_key: Option<String>, extra: &JsonValue) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = api_key;
    options.extra = serde_json::from_value(extra.clone()).expect("extra options");
    options
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

/// A model and the per-request options of one TS `describe` block.
struct Target {
    model: Model,
    options: JsonValue,
    api_key: Option<String>,
}

impl Target {
    fn env(provider: &str, id: &str, env: &[&str]) -> Self {
        for name in env {
            require_env(name);
        }
        Self {
            model: builtin(provider, id),
            options: json!({}),
            api_key: None,
        }
    }

    fn oauth(provider: &str, id: &str, token_env: &str) -> Self {
        Self {
            model: builtin(provider, id),
            options: json!({}),
            api_key: Some(require_env(token_env)),
        }
    }

    fn with_options(mut self, options: JsonValue) -> Self {
        self.options = options;
        self
    }

    fn stream_options(&self) -> ProviderStreamOptions {
        options(self.api_key.clone(), &self.options)
    }
}

/// TS `{ retry: 3 }`.
async fn with_retries<F, Fut>(mut attempt: F)
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<(), String>>,
{
    let mut failure = String::new();
    for number in 1..=3 {
        match attempt().await {
            Ok(()) => return,
            Err(error) => {
                eprintln!("attempt {number} failed: {error}");
                failure = error;
            }
        }
    }
    panic!("{failure}");
}

/// Which TS scenario a case runs.
#[derive(Clone, Copy)]
enum Scenario {
    EmojiInToolResults,
    RealWorldLinkedInData,
    UnpairedHighSurrogate,
}

struct ScenarioInput {
    tool_call_id: &'static str,
    tool_name: &'static str,
    tool_description: &'static str,
    first_prompt: &'static str,
    tool_result_text: String,
    follow_up: &'static str,
}

const EMOJI_TEXT: &str = r#"Test with emoji 🙈 and other characters:
- Monkey emoji: 🙈
- Thumbs up: 👍
- Heart: ❤️
- Thinking face: 🤔
- Rocket: 🚀
- Mixed text: Mario Zechner wann? Wo? Bin grad äußersr eventuninformiert 🙈
- Japanese: こんにちは
- Chinese: 你好
- Mathematical symbols: ∑∫∂√
- Special quotes: "curly" 'quotes'"#;

const LINKEDIN_TEXT: &str = r#"Post: Hab einen "Generative KI für Nicht-Techniker" Workshop gebaut.
Unanswered Comments: 2

=> {
  "comments": [
    {
      "author": "Matthias Neumayer's  graphic link",
      "text": "Leider nehmen das viel zu wenige Leute ernst"
    },
    {
      "author": "Matthias Neumayer's  graphic link",
      "text": "Mario Zechner wann? Wo? Bin grad äußersr eventuninformiert 🙈"
    }
  ]
}"#;

/// `` `Text with unpaired surrogate: ${String.fromCharCode(0xd83d)} <- should be sanitized` ``.
fn unpaired_surrogate_text() -> String {
    let mut units: Vec<u16> = "Text with unpaired surrogate: ".encode_utf16().collect();
    units.push(0xD83D);
    units.extend(" <- should be sanitized".encode_utf16());
    sanitize_surrogates_utf16(&units)
}

impl Scenario {
    fn input(self, model: &Model) -> ScenarioInput {
        let mistral = model.provider == "mistral";
        match self {
            Self::EmojiInToolResults => ScenarioInput {
                tool_call_id: if mistral { "testtool1" } else { "test_1" },
                tool_name: "test_tool",
                tool_description: "A test tool",
                first_prompt: "Use the test tool",
                tool_result_text: EMOJI_TEXT.to_owned(),
                follow_up: "Summarize the tool result briefly.",
            },
            Self::RealWorldLinkedInData => ScenarioInput {
                tool_call_id: if mistral { "linkedin1" } else { "linkedin_1" },
                tool_name: "linkedin_skill",
                tool_description: "Get LinkedIn comments",
                first_prompt: "Use the linkedin tool to get comments",
                tool_result_text: LINKEDIN_TEXT.to_owned(),
                follow_up: "How many comments are there?",
            },
            Self::UnpairedHighSurrogate => ScenarioInput {
                tool_call_id: if mistral { "testtool2" } else { "test_2" },
                tool_name: "test_tool",
                tool_description: "A test tool",
                first_prompt: "Use the test tool",
                tool_result_text: unpaired_surrogate_text(),
                follow_up: "What did the tool return?",
            },
        }
    }

    fn context(self, model: &Model) -> Context {
        let input = self.input(model);
        serde_json::from_value(json!({
            "systemPrompt": "You are a helpful assistant.",
            "messages": [
                { "role": "user", "content": input.first_prompt, "timestamp": now_ms() },
                {
                    "role": "assistant",
                    "content": [{
                        "type": "toolCall",
                        "id": input.tool_call_id,
                        "name": input.tool_name,
                        "arguments": {},
                    }],
                    "api": model.api,
                    "provider": model.provider,
                    "model": model.id,
                    "usage": {
                        "input": 0,
                        "output": 0,
                        "cacheRead": 0,
                        "cacheWrite": 0,
                        "totalTokens": 0,
                        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                    },
                    "stopReason": "toolUse",
                    "timestamp": now_ms(),
                },
                {
                    "role": "toolResult",
                    "toolCallId": input.tool_call_id,
                    "toolName": input.tool_name,
                    "content": [{ "type": "text", "text": input.tool_result_text }],
                    "isError": false,
                    "timestamp": now_ms(),
                },
                { "role": "user", "content": input.follow_up, "timestamp": now_ms() },
            ],
            "tools": [{
                "name": input.tool_name,
                "description": input.tool_description,
                // `Type.Object({})`.
                "parameters": { "type": "object", "properties": {} },
            }],
        }))
        .expect("context")
    }

    async fn check(self, target: &Target) -> Result<(), String> {
        let response = complete(
            &target.model,
            self.context(&target.model),
            target.stream_options(),
        )
        .await
        .map_err(|error| format!("{error:?}"))?;

        if response.stop_reason == StopReason::Error {
            return Err(format!(
                "stopReason is \"error\": {:?}",
                response.error_message
            ));
        }
        if response
            .error_message
            .as_deref()
            .is_some_and(|m| !m.is_empty())
        {
            return Err(format!("errorMessage is set: {:?}", response.error_message));
        }
        match self {
            Self::EmojiInToolResults | Self::UnpairedHighSurrogate => {
                if response.content.is_empty() {
                    return Err("content is empty".to_owned());
                }
            }
            Self::RealWorldLinkedInData => {
                let has_text = response
                    .content
                    .iter()
                    .any(|block| matches!(block, AssistantContentBlock::Text(_)));
                if !has_text {
                    return Err(format!("no text block in {:?}", response.content));
                }
            }
        }
        Ok(())
    }
}

async fn run(target: Target, scenario: Scenario) {
    with_retries(|| scenario.check(&target)).await;
}

/// One TS provider `describe` block: its three `it` cases.
macro_rules! unicode_suite {
    ($suite:ident, $reason:literal, $target:expr) => {
        mod $suite {
            use super::{run, Scenario, Target};

            #[allow(clippy::redundant_closure_call)] // The macro takes the target as a closure literal.
            fn target() -> Target {
                ($target)()
            }

            #[tokio::test]
            #[ignore = $reason]
            async fn should_handle_emoji_in_tool_results() {
                run(target(), Scenario::EmojiInToolResults).await;
            }

            #[tokio::test]
            #[ignore = $reason]
            async fn should_handle_real_world_linkedin_comment_data_with_emoji() {
                run(target(), Scenario::RealWorldLinkedInData).await;
            }

            #[tokio::test]
            #[ignore = $reason]
            async fn should_handle_unpaired_high_surrogate_0xd83d_in_tool_results() {
                run(target(), Scenario::UnpairedHighSurrogate).await;
            }
        }
    };
}

fn has_azure_openai_credentials() -> bool {
    env_value("AZURE_OPENAI_API_KEY").is_some()
        && (env_value("AZURE_OPENAI_BASE_URL").is_some()
            || env_value("AZURE_OPENAI_RESOURCE_NAME").is_some())
}

/// TS `resolveAzureDeploymentName()`: the last `modelId=deployment` entry of
/// `AZURE_OPENAI_DEPLOYMENT_NAME_MAP` for `model_id`.
fn resolve_azure_deployment_name(model_id: &str) -> Option<String> {
    let map_value = env_value("AZURE_OPENAI_DEPLOYMENT_NAME_MAP")?;
    map_value
        .split(',')
        .filter_map(|entry| {
            let mut parts = entry.trim().split('=');
            let id = parts.next()?.trim();
            let deployment = parts.next()?.trim();
            (!id.is_empty() && !deployment.is_empty()).then_some((id, deployment))
        })
        .rfind(|(id, _)| *id == model_id)
        .map(|(_, deployment)| deployment.to_owned())
}

fn azure_target() -> Target {
    assert!(
        has_azure_openai_credentials(),
        "Missing AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME"
    );
    let target = Target::env("azure", "gpt-4o-mini", &[]);
    match resolve_azure_deployment_name(&target.model.id) {
        Some(name) => target.with_options(json!({ "azureDeploymentName": name })),
        None => target,
    }
}

fn bedrock_target() -> Target {
    let has_credentials = env_value("AWS_PROFILE").is_some()
        || (env_value("AWS_ACCESS_KEY_ID").is_some()
            && env_value("AWS_SECRET_ACCESS_KEY").is_some())
        || env_value("AWS_BEARER_TOKEN_BEDROCK").is_some();
    assert!(
        has_credentials,
        "Missing AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK"
    );
    Target::env(
        "amazon-bedrock",
        "global.anthropic.claude-sonnet-4-5-20250929-v1:0",
        &[],
    )
}

unicode_suite!(google, "needs GEMINI_API_KEY; run with --ignored", || {
    Target::env("google", "gemini-2.5-flash", &["GEMINI_API_KEY"])
});
unicode_suite!(
    openai_completions,
    "needs OPENAI_API_KEY; run with --ignored",
    || Target::env("openai", "gpt-4o-mini", &["OPENAI_API_KEY"])
);
unicode_suite!(
    openai_responses,
    "needs OPENAI_API_KEY; run with --ignored",
    || Target::env("openai", "gpt-5-mini", &["OPENAI_API_KEY"])
);
unicode_suite!(
    azure_openai_responses,
    "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored",
    super::azure_target
);
unicode_suite!(
    anthropic,
    "needs ANTHROPIC_API_KEY; run with --ignored",
    || Target::env("anthropic", "claude-haiku-4-5", &["ANTHROPIC_API_KEY"])
);
unicode_suite!(
    anthropic_oauth,
    "needs ANTHROPIC_OAUTH_TOKEN; run with --ignored",
    || Target::oauth("anthropic", "claude-haiku-4-5", "ANTHROPIC_OAUTH_TOKEN")
);
unicode_suite!(
    github_copilot_claude_haiku_4_5,
    "needs GITHUB_COPILOT_OAUTH_TOKEN; run with --ignored",
    || Target::oauth(
        "github-copilot",
        "claude-haiku-4.5",
        "GITHUB_COPILOT_OAUTH_TOKEN"
    )
);
unicode_suite!(
    github_copilot_claude_sonnet_4,
    "needs GITHUB_COPILOT_OAUTH_TOKEN; run with --ignored",
    || Target::oauth(
        "github-copilot",
        "claude-sonnet-4.6",
        "GITHUB_COPILOT_OAUTH_TOKEN"
    )
);
unicode_suite!(
    xai,
    "needs XAI_API_KEY; run with --ignored",
    || Target::env("xai", "grok-4.3", &["XAI_API_KEY"])
);
unicode_suite!(groq, "needs GROQ_API_KEY; run with --ignored", || {
    Target::env("groq", "openai/gpt-oss-20b", &["GROQ_API_KEY"])
});
unicode_suite!(
    cerebras,
    "needs CEREBRAS_API_KEY; run with --ignored",
    || Target::env("cerebras", "gpt-oss-120b", &["CEREBRAS_API_KEY"])
);
unicode_suite!(
    cloudflare_workers_ai,
    "needs CLOUDFLARE_API_KEY and CLOUDFLARE_ACCOUNT_ID; run with --ignored",
    || Target::env(
        "cloudflare-workers-ai",
        "@cf/moonshotai/kimi-k2.6",
        &["CLOUDFLARE_API_KEY", "CLOUDFLARE_ACCOUNT_ID"]
    )
);
unicode_suite!(
    cloudflare_ai_gateway,
    "needs CLOUDFLARE_API_KEY, CLOUDFLARE_ACCOUNT_ID and CLOUDFLARE_GATEWAY_ID; run with --ignored",
    || Target::env(
        "cloudflare-ai-gateway",
        "workers-ai/@cf/moonshotai/kimi-k2.6",
        &[
            "CLOUDFLARE_API_KEY",
            "CLOUDFLARE_ACCOUNT_ID",
            "CLOUDFLARE_GATEWAY_ID"
        ]
    )
);
unicode_suite!(hugging_face, "needs HF_TOKEN; run with --ignored", || {
    Target::env("huggingface", "moonshotai/Kimi-K2.5", &["HF_TOKEN"])
});
unicode_suite!(
    together_ai,
    "needs TOGETHER_API_KEY; run with --ignored",
    || Target::env("together", "moonshotai/Kimi-K3", &["TOGETHER_API_KEY"])
        .with_options(serde_json::json!({ "reasoningEffort": "high" }))
);
unicode_suite!(baseten, "needs BASETEN_API_KEY; run with --ignored", || {
    Target::env("baseten", "zai-org/GLM-5.2", &["BASETEN_API_KEY"])
        .with_options(serde_json::json!({ "reasoningEffort": "high" }))
});
unicode_suite!(
    zai,
    "needs ZAI_API_KEY; run with --ignored",
    || Target::env("zai", "glm-5.2", &["ZAI_API_KEY"])
);
unicode_suite!(mistral, "needs MISTRAL_API_KEY; run with --ignored", || {
    Target::env("mistral", "devstral-medium-latest", &["MISTRAL_API_KEY"])
});
unicode_suite!(minimax, "needs MINIMAX_API_KEY; run with --ignored", || {
    Target::env("minimax", "MiniMax-M2.7", &["MINIMAX_API_KEY"])
});
unicode_suite!(xiaomi, "needs XIAOMI_API_KEY; run with --ignored", || {
    Target::env("xiaomi", "mimo-v2.5-pro", &["XIAOMI_API_KEY"])
});
unicode_suite!(
    xiaomi_token_plan_cn,
    "needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored",
    || Target::env(
        "xiaomi-token-plan-cn",
        "mimo-v2.5-pro",
        &["XIAOMI_TOKEN_PLAN_CN_API_KEY"]
    )
);
unicode_suite!(
    xiaomi_token_plan_ams,
    "needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored",
    || Target::env(
        "xiaomi-token-plan-ams",
        "mimo-v2.5-pro",
        &["XIAOMI_TOKEN_PLAN_AMS_API_KEY"]
    )
);
unicode_suite!(
    xiaomi_token_plan_sgp,
    "needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored",
    || Target::env(
        "xiaomi-token-plan-sgp",
        "mimo-v2.5-pro",
        &["XIAOMI_TOKEN_PLAN_SGP_API_KEY"]
    )
);
unicode_suite!(
    qwen_token_plan,
    "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored",
    || Target::env(
        "qwen-token-plan",
        "qwen3.7-max",
        &["QWEN_TOKEN_PLAN_API_KEY"]
    )
);
unicode_suite!(
    qwen_token_plan_individual,
    "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored",
    || Target::env(
        "qwen-token-plan-individual",
        "qwen3.8-max",
        &["QWEN_TOKEN_PLAN_API_KEY"]
    )
);
unicode_suite!(
    qwen_token_plan_cn,
    "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored",
    || Target::env(
        "qwen-token-plan-cn",
        "qwen3.7-max",
        &["QWEN_TOKEN_PLAN_CN_API_KEY"]
    )
);
unicode_suite!(
    kimi_for_coding,
    "needs KIMI_API_KEY; run with --ignored",
    || Target::env("kimi-coding", "kimi-for-coding", &["KIMI_API_KEY"])
);
unicode_suite!(
    vercel_ai_gateway,
    "needs AI_GATEWAY_API_KEY; run with --ignored",
    || Target::env(
        "vercel-ai-gateway",
        "google/gemini-2.5-flash",
        &["AI_GATEWAY_API_KEY"]
    )
);
unicode_suite!(
    amazon_bedrock,
    "needs AWS_PROFILE, AWS_ACCESS_KEY_ID+AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored",
    super::bedrock_target
);
unicode_suite!(
    openai_codex_gpt_5_5,
    "needs OPENAI_CODEX_OAUTH_TOKEN; run with --ignored",
    || Target::oauth("openai-codex", "gpt-5.5", "OPENAI_CODEX_OAUTH_TOKEN")
);

/// The unpaired-surrogate fixture is the TS text with the lone surrogate
/// removed, as TS `sanitizeSurrogates` sends it.
#[test]
fn unpaired_surrogate_fixture_matches_the_sanitized_ts_text() {
    assert_eq!(
        unpaired_surrogate_text(),
        "Text with unpaired surrogate:  <- should be sanitized"
    );
}
