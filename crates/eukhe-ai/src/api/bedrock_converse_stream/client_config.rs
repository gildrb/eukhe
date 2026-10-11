//! The Bedrock runtime client configuration `stream` builds (TS
//! `BedrockRuntimeClientConfig`): profile, endpoint pinning, region,
//! credentials, bearer token, and the request handler. Section of the port of
//! `api/bedrock-converse-stream.ts`.

use std::fmt;
use std::sync::LazyLock;

use eukhe_types::pi_ai::{Model, ProviderEnv};
use regex::Regex;

use super::BedrockOptions;
use crate::utils::node_http_proxy::{resolve_http_proxy_url_for_target, ProxyError};
use crate::utils::provider_env::get_provider_env_value;

/// Static AWS credentials (TS `AwsCredentialIdentity`).
#[derive(Clone, PartialEq, Eq)]
pub struct AwsCredentials {
    pub access_key_id: String,
    pub secret_access_key: String,
    pub session_token: Option<String>,
}

impl fmt::Debug for AwsCredentials {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AwsCredentials")
            .field("access_key_id", &self.access_key_id)
            .field("secret_access_key", &"<redacted>")
            .field(
                "session_token",
                &self.session_token.as_ref().map(|_| "<redacted>"),
            )
            .finish()
    }
}

/// The HTTP request handler the client uses (TS `config.requestHandler`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BedrockRequestHandler {
    /// The SDK default (`NodeHttp2Handler`).
    Default,
    /// `NodeHttpHandler` (HTTP/1.1), selected by `AWS_BEDROCK_FORCE_HTTP1=1`.
    Http1,
    /// `NodeHttpHandler` with HTTP(S) proxy agents for this proxy URL.
    Proxy(url::Url),
}

/// TS `BedrockRuntimeClientConfig` as `stream` builds it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BedrockClientConfig {
    /// `config.profile`.
    pub profile: Option<String>,
    /// `config.endpoint`: set only when the model's base URL is pinned.
    pub endpoint: Option<String>,
    /// `config.region`; `None` leaves the region to the SDK default chain.
    pub region: Option<String>,
    /// `config.credentials`; `None` leaves them to the SDK default chain.
    pub credentials: Option<AwsCredentials>,
    /// `config.token.token`: the Bedrock API key (bearer token).
    pub token: Option<String>,
    /// `config.authSchemePreference`.
    pub auth_scheme_preference: Option<Vec<String>>,
    /// `config.requestHandler`.
    pub request_handler: BedrockRequestHandler,
}

impl BedrockClientConfig {
    /// Whether requests authenticate with the bearer token instead of `SigV4`.
    pub(crate) fn uses_bearer_token(&self) -> bool {
        self.token.is_some()
            && self
                .auth_scheme_preference
                .as_ref()
                .is_some_and(|schemes| schemes.iter().any(|scheme| scheme == "httpBearerAuth"))
    }
}

/// `options.x || ...` over optional strings: empty counts as unset.
fn non_empty(value: Option<&str>) -> Option<String> {
    value.filter(|value| !value.is_empty()).map(str::to_owned)
}

/// TS `getConfiguredBedrockRegion`.
pub(crate) fn get_configured_bedrock_region(options: &BedrockOptions) -> Option<String> {
    let env = options.stream.request.env.as_ref();
    non_empty(options.region.as_deref())
        .or_else(|| get_provider_env_value("AWS_REGION", env))
        .or_else(|| get_provider_env_value("AWS_DEFAULT_REGION", env))
}

/// TS `getConfiguredBedrockCredentials`.
fn get_configured_bedrock_credentials(env: Option<&ProviderEnv>) -> Option<AwsCredentials> {
    let access_key_id = get_provider_env_value("AWS_ACCESS_KEY_ID", env)?;
    let secret_access_key = get_provider_env_value("AWS_SECRET_ACCESS_KEY", env)?;
    Some(AwsCredentials {
        access_key_id,
        secret_access_key,
        session_token: get_provider_env_value("AWS_SESSION_TOKEN", env),
    })
}

/// `/^bedrock-runtime(?:-fips)?\.([a-z0-9-]+)\.amazonaws\.com(?:\.cn)?$/`.
static STANDARD_ENDPOINT_HOST: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^bedrock-runtime(?:-fips)?\.([a-z0-9-]+)\.amazonaws\.com(?:\.cn)?$")
        .unwrap_or_else(|_| unreachable!("static regex"))
});

/// `/^arn:aws(?:-[a-z0-9-]+)?:bedrock:([a-z0-9-]+):/`.
static ARN_REGION: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^arn:aws(?:-[a-z0-9-]+)?:bedrock:([a-z0-9-]+):")
        .unwrap_or_else(|_| unreachable!("static regex"))
});

/// TS `getStandardBedrockEndpointRegion`.
pub(crate) fn get_standard_bedrock_endpoint_region(base_url: &str) -> Option<String> {
    if base_url.is_empty() {
        return None;
    }
    let url = url::Url::parse(base_url).ok()?;
    let hostname = url.host_str()?.to_lowercase();
    STANDARD_ENDPOINT_HOST
        .captures(&hostname)
        .and_then(|captures| captures.get(1))
        .map(|region| region.as_str().to_owned())
}

/// TS `shouldUseExplicitBedrockEndpoint`.
fn should_use_explicit_bedrock_endpoint(
    base_url: &str,
    configured_region: Option<&str>,
    has_ambient_configured_profile: bool,
) -> bool {
    if get_standard_bedrock_endpoint_region(base_url).is_none() {
        return true;
    }
    configured_region.is_none() && !has_ambient_configured_profile
}

/// The client configuration `stream` builds for `model` and `options` (the
/// TS `config` object up to `new BedrockRuntimeClient(config)`).
///
/// # Errors
///
/// Returns the [`ProxyError`] of an unusable proxy environment value.
pub(crate) fn resolve_client_config(
    model: &Model,
    options: &BedrockOptions,
) -> Result<BedrockClientConfig, ProxyError> {
    let env = options.stream.request.env.as_ref();
    // A profile explicitly configured through pi's auth flow (the `profile`
    // option or scoped `AWS_PROFILE` on the stored credential's env) must win
    // over ambient AWS_ACCESS_KEY_ID/AWS_SECRET_ACCESS_KEY.
    let options_profile = non_empty(options.profile.as_deref()).or_else(|| {
        non_empty(
            env.and_then(|env| env.get("AWS_PROFILE"))
                .map(String::as_str),
        )
    });
    let profile = options_profile
        .clone()
        .or_else(|| get_provider_env_value("AWS_PROFILE", env));
    let configured_region = get_configured_bedrock_region(options);
    let has_ambient_configured_profile = get_provider_env_value("AWS_PROFILE", None).is_some();
    let endpoint_region = get_standard_bedrock_endpoint_region(&model.base_url);
    let use_explicit_endpoint = should_use_explicit_bedrock_endpoint(
        &model.base_url,
        configured_region.as_deref(),
        has_ambient_configured_profile,
    );

    // Only pin standard AWS Bedrock runtime endpoints when no region or
    // ambient AWS_PROFILE is configured.
    let endpoint = use_explicit_endpoint.then(|| model.base_url.clone());

    let skip_auth = get_provider_env_value("AWS_BEDROCK_SKIP_AUTH", env).as_deref() == Some("1");
    let bearer_token = non_empty(options.bearer_token.as_deref())
        .or_else(|| non_empty(options.stream.request.api_key.as_deref()))
        .or_else(|| get_provider_env_value("AWS_BEARER_TOKEN_BEDROCK", env));
    let use_bearer_token = bearer_token.is_some() && !skip_auth;

    // Region resolution: ARN-embedded > explicit option > env vars > SDK
    // default chain.
    let region = if let Some(captures) = ARN_REGION.captures(&model.id) {
        captures.get(1).map(|region| region.as_str().to_owned())
    } else if configured_region.is_some() {
        configured_region
    } else if endpoint_region.is_some() && use_explicit_endpoint {
        endpoint_region
    } else if has_ambient_configured_profile {
        None
    } else {
        Some("us-east-1".to_owned())
    };

    let mut credentials = None;
    // Support proxies that don't need authentication.
    if skip_auth {
        credentials = Some(AwsCredentials {
            access_key_id: "dummy-access-key".to_owned(),
            secret_access_key: "dummy-secret-key".to_owned(),
            session_token: None,
        });
    }
    if !skip_auth && options_profile.is_none() {
        if let Some(configured) = get_configured_bedrock_credentials(env) {
            credentials = Some(configured);
        }
    }

    let request_handler = match resolve_http_proxy_url_for_target(&model.base_url, env)? {
        Some(proxy) => BedrockRequestHandler::Proxy(proxy),
        None if get_provider_env_value("AWS_BEDROCK_FORCE_HTTP1", env).as_deref() == Some("1") => {
            BedrockRequestHandler::Http1
        }
        None => BedrockRequestHandler::Default,
    };

    let (token, auth_scheme_preference) = if use_bearer_token {
        (bearer_token, Some(vec!["httpBearerAuth".to_owned()]))
    } else {
        (None, None)
    };

    Ok(BedrockClientConfig {
        profile,
        endpoint,
        region,
        credentials,
        token,
        auth_scheme_preference,
        request_handler,
    })
}
