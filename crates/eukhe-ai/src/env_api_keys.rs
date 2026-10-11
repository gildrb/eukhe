//! Environment-variable API key discovery for the old global API and status
//! UIs. Port of `env-api-keys.ts`.

use std::path::Path;
use std::sync::{Mutex, PoisonError};

use crate::types::ProviderEnv;
use crate::utils::provider_env::get_provider_env_value;

pub const ANTHROPIC_AUTH_TOKEN_ENV: &str = "ANTHROPIC_AUTH_TOKEN";
pub const ANTHROPIC_OAUTH_TOKEN_ENV: &str = "ANTHROPIC_OAUTH_TOKEN";
pub const ANTHROPIC_API_KEY_ENV: &str = "ANTHROPIC_API_KEY";
pub const ANTHROPIC_FEDERATION_RULE_ID_ENV: &str = "ANTHROPIC_FEDERATION_RULE_ID";
pub const ANTHROPIC_ORGANIZATION_ID_ENV: &str = "ANTHROPIC_ORGANIZATION_ID";
pub const ANTHROPIC_SERVICE_ACCOUNT_ID_ENV: &str = "ANTHROPIC_SERVICE_ACCOUNT_ID";
pub const ANTHROPIC_IDENTITY_TOKEN_FILE_ENV: &str = "ANTHROPIC_IDENTITY_TOKEN_FILE";
pub const ANTHROPIC_WORKSPACE_ID_ENV: &str = "ANTHROPIC_WORKSPACE_ID";

/// Marker returned by [`get_env_api_key`] for providers configured through
/// ambient credentials (ADC files, AWS credential chains) rather than a key.
pub const AMBIENT_AUTHENTICATED_MARKER: &str = "<authenticated>";

/// Cached existence of the default Vertex ADC file (or the file named by
/// `GOOGLE_APPLICATION_CREDENTIALS` at first check). Explicit provider-env
/// paths bypass the cache.
static CACHED_VERTEX_ADC_CREDENTIALS_EXISTS: Mutex<Option<bool>> = Mutex::new(None);

fn has_vertex_adc_credentials(env: Option<&ProviderEnv>) -> bool {
    if let Some(explicit) = env
        .and_then(|env| env.get("GOOGLE_APPLICATION_CREDENTIALS"))
        .filter(|path| !path.is_empty())
    {
        return Path::new(explicit).exists();
    }

    let mut cached = CACHED_VERTEX_ADC_CREDENTIALS_EXISTS
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    *cached.get_or_insert_with(|| {
        // Check GOOGLE_APPLICATION_CREDENTIALS env var first (standard way),
        // then fall back to the default ADC path.
        if let Some(gac_path) = get_provider_env_value("GOOGLE_APPLICATION_CREDENTIALS", env) {
            Path::new(&gac_path).exists()
        } else {
            std::env::home_dir().is_some_and(|home| {
                home.join(".config")
                    .join("gcloud")
                    .join("application_default_credentials.json")
                    .exists()
            })
        }
    })
}

fn get_api_key_env_vars(provider: &str) -> Option<&'static [&'static str]> {
    match provider {
        "github-copilot" => Some(&["COPILOT_GITHUB_TOKEN"]),
        // ANTHROPIC_AUTH_TOKEN participates in env discovery/status, but
        // get_env_api_key() skips it because requests must pass it as
        // Authorization: Bearer.
        "anthropic" => Some(&[
            ANTHROPIC_AUTH_TOKEN_ENV,
            ANTHROPIC_OAUTH_TOKEN_ENV,
            ANTHROPIC_API_KEY_ENV,
        ]),
        "ant-ling" => Some(&["ANT_LING_API_KEY"]),
        "qwen-token-plan" | "qwen-token-plan-individual" => Some(&["QWEN_TOKEN_PLAN_API_KEY"]),
        "qwen-token-plan-cn" => Some(&["QWEN_TOKEN_PLAN_CN_API_KEY"]),
        "openai" => Some(&["OPENAI_API_KEY"]),
        "azure" => Some(&["AZURE_OPENAI_API_KEY"]),
        "nvidia" => Some(&["NVIDIA_API_KEY"]),
        "deepseek" => Some(&["DEEPSEEK_API_KEY"]),
        "google" => Some(&["GEMINI_API_KEY"]),
        "google-vertex" => Some(&["GOOGLE_CLOUD_API_KEY"]),
        "groq" => Some(&["GROQ_API_KEY"]),
        "cerebras" => Some(&["CEREBRAS_API_KEY"]),
        "xai" => Some(&["XAI_API_KEY"]),
        "typesafe" => Some(&["TYPESAFE_API_KEY"]),
        "radius" => Some(&["RADIUS_API_KEY"]),
        "openrouter" => Some(&["OPENROUTER_API_KEY"]),
        "vercel-ai-gateway" => Some(&["AI_GATEWAY_API_KEY"]),
        "zai" => Some(&["ZAI_API_KEY"]),
        "zai-coding-cn" => Some(&["ZAI_CODING_CN_API_KEY"]),
        "mistral" => Some(&["MISTRAL_API_KEY"]),
        "minimax" => Some(&["MINIMAX_API_KEY"]),
        "minimax-cn" => Some(&["MINIMAX_CN_API_KEY"]),
        "moonshotai" | "moonshotai-cn" => Some(&["MOONSHOT_API_KEY"]),
        "huggingface" => Some(&["HF_TOKEN"]),
        "fireworks" => Some(&["FIREWORKS_API_KEY"]),
        "together" => Some(&["TOGETHER_API_KEY"]),
        "baseten" => Some(&["BASETEN_API_KEY"]),
        "opencode" | "opencode-go" => Some(&["OPENCODE_API_KEY"]),
        "kimi-coding" => Some(&["KIMI_API_KEY"]),
        "meta" => Some(&["META_API_KEY"]),
        "cloudflare-workers-ai" | "cloudflare-ai-gateway" => Some(&["CLOUDFLARE_API_KEY"]),
        "xiaomi" => Some(&["XIAOMI_API_KEY"]),
        "xiaomi-token-plan-cn" => Some(&["XIAOMI_TOKEN_PLAN_CN_API_KEY"]),
        "xiaomi-token-plan-ams" => Some(&["XIAOMI_TOKEN_PLAN_AMS_API_KEY"]),
        "xiaomi-token-plan-sgp" => Some(&["XIAOMI_TOKEN_PLAN_SGP_API_KEY"]),
        // eukhe addition: the Prime Inference provider.
        "prime-inference" => Some(&["PRIME_API_KEY"]),
        _ => None,
    }
}

/// Find configured environment variables that can provide an API key for a
/// provider.
///
/// This only reports actual API key variables. It intentionally excludes
/// ambient credential sources such as AWS profiles, AWS IAM credentials, and
/// Google Application Default Credentials.
#[must_use]
pub fn find_env_keys(provider: &str, env: Option<&ProviderEnv>) -> Option<Vec<String>> {
    let env_vars = get_api_key_env_vars(provider)?;
    let found: Vec<String> = env_vars
        .iter()
        .filter(|env_var| get_provider_env_value(env_var, env).is_some())
        .map(|env_var| (*env_var).to_owned())
        .collect();
    (!found.is_empty()).then_some(found)
}

/// Get the API key for a provider from known environment variables, e.g.
/// `OPENAI_API_KEY`. Returns [`AMBIENT_AUTHENTICATED_MARKER`] for Vertex ADC
/// and AWS credential chains.
///
/// Will not return API keys for providers that require OAuth tokens.
#[must_use]
pub fn get_env_api_key(provider: &str, env: Option<&ProviderEnv>) -> Option<String> {
    if let Some(env_keys) = find_env_keys(provider, env) {
        let api_key_env = if provider == "anthropic" {
            env_keys
                .iter()
                .find(|key| key.as_str() != ANTHROPIC_AUTH_TOKEN_ENV)
        } else {
            env_keys.first()
        };
        if let Some(api_key_env) = api_key_env {
            return get_provider_env_value(api_key_env, env);
        }
    }

    // Vertex AI supports either an explicit API key or Application Default
    // Credentials. Auth is configured via
    // `gcloud auth application-default login`.
    if provider == "google-vertex" {
        let has_credentials = has_vertex_adc_credentials(env);
        let has_project = get_provider_env_value("GOOGLE_CLOUD_PROJECT", env).is_some()
            || get_provider_env_value("GCLOUD_PROJECT", env).is_some();
        let has_location = get_provider_env_value("GOOGLE_CLOUD_LOCATION", env).is_some();
        if has_credentials && has_project && has_location {
            return Some(AMBIENT_AUTHENTICATED_MARKER.to_owned());
        }
    }

    if provider == "amazon-bedrock" {
        // Amazon Bedrock supports multiple credential sources:
        // 1. AWS_PROFILE - named profile from ~/.aws/credentials
        // 2. AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY - standard IAM keys
        // 3. AWS_BEARER_TOKEN_BEDROCK - Bedrock bearer token
        // 4. AWS_CONTAINER_CREDENTIALS_RELATIVE_URI - ECS task roles
        // 5. AWS_CONTAINER_CREDENTIALS_FULL_URI - ECS task roles (full URI)
        // 6. AWS_WEB_IDENTITY_TOKEN_FILE - IRSA (IAM Roles for Service Accounts)
        let has = |name: &str| get_provider_env_value(name, env).is_some();
        if has("AWS_PROFILE")
            || (has("AWS_ACCESS_KEY_ID") && has("AWS_SECRET_ACCESS_KEY"))
            || has("AWS_BEARER_TOKEN_BEDROCK")
            || has("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI")
            || has("AWS_CONTAINER_CREDENTIALS_FULL_URI")
            || has("AWS_WEB_IDENTITY_TOKEN_FILE")
        {
            return Some(AMBIENT_AUTHENTICATED_MARKER.to_owned());
        }
    }

    None
}
