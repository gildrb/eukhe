//! Environment-variable API key discovery for auth status and resolution,
//! and the credential names no child of the host may inherit
//! ([`is_credential_env_var`]). Port of `env-api-keys.ts`.

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
pub const AWS_ACCESS_KEY_ID_ENV: &str = "AWS_ACCESS_KEY_ID";
pub const AWS_SECRET_ACCESS_KEY_ENV: &str = "AWS_SECRET_ACCESS_KEY";
pub const AWS_SESSION_TOKEN_ENV: &str = "AWS_SESSION_TOKEN";
pub const AWS_BEARER_TOKEN_BEDROCK_ENV: &str = "AWS_BEARER_TOKEN_BEDROCK";
pub const AWS_CONTAINER_AUTHORIZATION_TOKEN_ENV: &str = "AWS_CONTAINER_AUTHORIZATION_TOKEN";
pub const AWS_WEB_IDENTITY_TOKEN_FILE_ENV: &str = "AWS_WEB_IDENTITY_TOKEN_FILE";
pub const GEMINI_API_KEY_ENV: &str = "GEMINI_API_KEY";
pub const GOOGLE_API_KEY_ENV: &str = "GOOGLE_API_KEY";
pub const GOOGLE_APPLICATION_CREDENTIALS_ENV: &str = "GOOGLE_APPLICATION_CREDENTIALS";

/// The API key variables of each provider, in lookup order
/// ([`find_env_keys`]). [`credential_env_vars`] reads the same table.
///
/// `ANTHROPIC_AUTH_TOKEN` participates in env discovery/status, but
/// [`get_env_api_key`] skips it because requests must pass it as
/// `Authorization: Bearer`.
const PROVIDER_API_KEY_ENV_VARS: &[(&str, &[&str])] = &[
    ("github-copilot", &["COPILOT_GITHUB_TOKEN"]),
    (
        "anthropic",
        &[
            ANTHROPIC_AUTH_TOKEN_ENV,
            ANTHROPIC_OAUTH_TOKEN_ENV,
            ANTHROPIC_API_KEY_ENV,
        ],
    ),
    ("ant-ling", &["ANT_LING_API_KEY"]),
    ("qwen-token-plan", &["QWEN_TOKEN_PLAN_API_KEY"]),
    ("qwen-token-plan-individual", &["QWEN_TOKEN_PLAN_API_KEY"]),
    ("qwen-token-plan-cn", &["QWEN_TOKEN_PLAN_CN_API_KEY"]),
    ("openai", &["OPENAI_API_KEY"]),
    ("azure", &["AZURE_OPENAI_API_KEY"]),
    ("nvidia", &["NVIDIA_API_KEY"]),
    ("deepseek", &["DEEPSEEK_API_KEY"]),
    ("google", &[GEMINI_API_KEY_ENV]),
    ("google-vertex", &["GOOGLE_CLOUD_API_KEY"]),
    ("groq", &["GROQ_API_KEY"]),
    ("cerebras", &["CEREBRAS_API_KEY"]),
    ("xai", &["XAI_API_KEY"]),
    ("typesafe", &["TYPESAFE_API_KEY"]),
    ("radius", &["RADIUS_API_KEY"]),
    ("openrouter", &["OPENROUTER_API_KEY"]),
    ("vercel-ai-gateway", &["AI_GATEWAY_API_KEY"]),
    ("zai", &["ZAI_API_KEY"]),
    ("zai-coding-cn", &["ZAI_CODING_CN_API_KEY"]),
    ("mistral", &["MISTRAL_API_KEY"]),
    ("minimax", &["MINIMAX_API_KEY"]),
    ("minimax-cn", &["MINIMAX_CN_API_KEY"]),
    ("moonshotai", &["MOONSHOT_API_KEY"]),
    ("moonshotai-cn", &["MOONSHOT_API_KEY"]),
    ("huggingface", &["HF_TOKEN"]),
    ("fireworks", &["FIREWORKS_API_KEY"]),
    ("together", &["TOGETHER_API_KEY"]),
    ("baseten", &["BASETEN_API_KEY"]),
    ("opencode", &["OPENCODE_API_KEY"]),
    ("opencode-go", &["OPENCODE_API_KEY"]),
    ("kimi-coding", &["KIMI_API_KEY"]),
    ("meta", &["META_API_KEY"]),
    ("cloudflare-workers-ai", &["CLOUDFLARE_API_KEY"]),
    ("cloudflare-ai-gateway", &["CLOUDFLARE_API_KEY"]),
    ("xiaomi", &["XIAOMI_API_KEY"]),
    ("xiaomi-token-plan-cn", &["XIAOMI_TOKEN_PLAN_CN_API_KEY"]),
    ("xiaomi-token-plan-ams", &["XIAOMI_TOKEN_PLAN_AMS_API_KEY"]),
    ("xiaomi-token-plan-sgp", &["XIAOMI_TOKEN_PLAN_SGP_API_KEY"]),
    // eukhe addition: the Prime Inference provider.
    ("prime-inference", &["PRIME_API_KEY"]),
];

/// The other credentials the providers read from the environment: AWS
/// keys and tokens (Bedrock), the Google API key and the Application
/// Default Credentials file (Gemini, Vertex), and the Anthropic workload
/// identity token file.
const OTHER_CREDENTIAL_ENV_VARS: &[&str] = &[
    AWS_ACCESS_KEY_ID_ENV,
    AWS_SECRET_ACCESS_KEY_ENV,
    AWS_SESSION_TOKEN_ENV,
    AWS_BEARER_TOKEN_BEDROCK_ENV,
    AWS_CONTAINER_AUTHORIZATION_TOKEN_ENV,
    AWS_WEB_IDENTITY_TOKEN_FILE_ENV,
    GOOGLE_API_KEY_ENV,
    GOOGLE_APPLICATION_CREDENTIALS_ENV,
    ANTHROPIC_IDENTITY_TOKEN_FILE_ENV,
];

/// A name whose ASCII upper case contains one of these is a credential
/// ([`is_credential_env_var`]):
///
/// - `API_KEY`, `APIKEY`: API keys (`OPENAI_API_KEY`, `MY_APIKEY`).
/// - `TOKEN`: bearer, session, OAuth and access tokens, and token files
///   (`GITHUB_TOKEN`, `HF_TOKEN`, `AWS_WEB_IDENTITY_TOKEN_FILE`). It also
///   matches `TOKENIZERS_PARALLELISM`; a child does not get that switch.
/// - `SECRET`: client secrets and secret keys (`AWS_SECRET_ACCESS_KEY`).
/// - `PASSWORD`, `PASSWD`: passwords (`PGPASSWORD`, `DB_PASSWD`).
/// - `PASSPHRASE`: key passphrases (`GPG_PASSPHRASE`).
/// - `CREDENTIAL`: credentials and credential files
///   (`GOOGLE_APPLICATION_CREDENTIALS`, `AWS_SHARED_CREDENTIALS_FILE`).
/// - `PRIVATE_KEY`: private keys and key files (`TLS_PRIVATE_KEY`).
/// - `ACCESS_KEY`: access key pairs (`AWS_ACCESS_KEY_ID`, `S3_ACCESS_KEY`).
///
/// There is no `KEY`, `AUTH` or `PASS` pattern: these match names a child
/// needs and that hold no secret (`SSH_AUTH_SOCK`, `XAUTHORITY`,
/// `KEYTIMEOUT`, `SSH_ASKPASS`).
const SECRET_NAME_PATTERNS: &[&str] = &[
    "API_KEY",
    "APIKEY",
    "TOKEN",
    "SECRET",
    "PASSWORD",
    "PASSWD",
    "PASSPHRASE",
    "CREDENTIAL",
    "PRIVATE_KEY",
    "ACCESS_KEY",
];

/// Every variable the provider and auth code reads a credential from: the
/// API key variables of each provider, then the other credentials. All are
/// upper case; a name can come more than once.
pub fn credential_env_vars() -> impl Iterator<Item = &'static str> {
    PROVIDER_API_KEY_ENV_VARS
        .iter()
        .flat_map(|(_, names)| names.iter().copied())
        .chain(OTHER_CREDENTIAL_ENV_VARS.iter().copied())
}

/// True when the ASCII upper case of `name` is a variable the provider and
/// auth code reads a credential from ([`credential_env_vars`]): a provider
/// credential, which no child of the host gets.
#[must_use]
pub fn is_provider_credential_env_var(name: &str) -> bool {
    let upper = name.to_ascii_uppercase();
    credential_env_vars().any(|known| known == upper)
}

/// True when `name` names a credential: a provider credential
/// ([`is_provider_credential_env_var`]), or a name whose ASCII upper case
/// contains a secret pattern (`API_KEY`, `APIKEY`, `TOKEN`, `SECRET`,
/// `PASSWORD`, `PASSWD`, `PASSPHRASE`, `CREDENTIAL`, `PRIVATE_KEY`,
/// `ACCESS_KEY`). The host strips these from the environment of every
/// child it starts for an agent.
#[must_use]
pub fn is_credential_env_var(name: &str) -> bool {
    let upper = name.to_ascii_uppercase();
    credential_env_vars().any(|known| known == upper)
        || SECRET_NAME_PATTERNS
            .iter()
            .any(|pattern| upper.contains(pattern))
}

/// Marker returned by [`get_env_api_key`] for providers configured through
/// ambient credentials (ADC files, AWS credential chains) rather than a key.
pub const AMBIENT_AUTHENTICATED_MARKER: &str = "<authenticated>";

/// Cached existence of the default Vertex ADC file (or the file named by
/// `GOOGLE_APPLICATION_CREDENTIALS` at first check). Explicit provider-env
/// paths bypass the cache.
static CACHED_VERTEX_ADC_CREDENTIALS_EXISTS: Mutex<Option<bool>> = Mutex::new(None);

fn has_vertex_adc_credentials(env: Option<&ProviderEnv>) -> bool {
    if let Some(explicit) = env
        .and_then(|env| env.get(GOOGLE_APPLICATION_CREDENTIALS_ENV))
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
        if let Some(gac_path) = get_provider_env_value(GOOGLE_APPLICATION_CREDENTIALS_ENV, env) {
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

/// Find configured environment variables that can provide an API key for a
/// provider.
///
/// This only reports actual API key variables. It intentionally excludes
/// ambient credential sources such as AWS profiles, AWS IAM credentials, and
/// Google Application Default Credentials.
#[must_use]
pub fn find_env_keys(provider: &str, env: Option<&ProviderEnv>) -> Option<Vec<String>> {
    let (_, env_vars) = PROVIDER_API_KEY_ENV_VARS
        .iter()
        .find(|(id, _)| *id == provider)?;
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
            || (has(AWS_ACCESS_KEY_ID_ENV) && has(AWS_SECRET_ACCESS_KEY_ENV))
            || has(AWS_BEARER_TOKEN_BEDROCK_ENV)
            || has("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI")
            || has("AWS_CONTAINER_CREDENTIALS_FULL_URI")
            || has(AWS_WEB_IDENTITY_TOKEN_FILE_ENV)
        {
            return Some(AMBIENT_AUTHENTICATED_MARKER.to_owned());
        }
    }

    None
}
