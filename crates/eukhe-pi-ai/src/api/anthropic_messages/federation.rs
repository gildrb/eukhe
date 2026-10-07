//! Workload identity federation: the pi side (`getAnthropicFederation`, the
//! shared `federationClient`) and the SDK side it relies on (`config` with
//! `oidc_federation` authentication: `oidcFederationProvider`,
//! `identityTokenFromFile`, `TokenCache`, `requireSecureTokenEndpoint`,
//! `parseTokenResponse`, `redactSensitive` of `@anthropic-ai/sdk` 0.129.0).

use std::sync::{Arc, Mutex, PoisonError};
use std::time::{SystemTime, UNIX_EPOCH};

use eukhe_types::pi_ai::{JsonObject, JsonValue, Model, ProviderEnv, ProviderHeaders};
use serde::Serialize;

use super::client::SDK_VERSION;
use crate::env_api_keys::{
    ANTHROPIC_FEDERATION_RULE_ID_ENV, ANTHROPIC_IDENTITY_TOKEN_FILE_ENV,
    ANTHROPIC_ORGANIZATION_ID_ENV, ANTHROPIC_SERVICE_ACCOUNT_ID_ENV, ANTHROPIC_WORKSPACE_ID_ENV,
};
use crate::types::FetchFunction;
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::js::{js_trim, json_stringify, utf16_len, utf16_prefix};
use crate::utils::provider_env::get_provider_env_value;

/// TS `identity_token: { source: "file", path }`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct IdentityTokenSource {
    pub(crate) source: &'static str,
    pub(crate) path: String,
}

/// TS `authentication` of an `oidc_federation` config.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct FederationAuthentication {
    #[serde(rename = "type")]
    pub(crate) kind: &'static str,
    pub(crate) federation_rule_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) service_account_id: Option<String>,
    pub(crate) identity_token: IdentityTokenSource,
}

/// TS `AnthropicFederationConfig` (SDK `ClientOptions["config"]`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct AnthropicFederationConfig {
    pub(crate) organization_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) workspace_id: Option<String>,
    pub(crate) authentication: FederationAuthentication,
}

/// TS `hasHeader`.
pub(crate) fn has_header(headers: Option<&ProviderHeaders>, name: &str) -> bool {
    let Some(headers) = headers else {
        return false;
    };
    let expected = name.to_ascii_lowercase();
    headers.iter().any(|(key, value)| {
        key.to_ascii_lowercase() == expected
            && value
                .as_deref()
                .is_some_and(|value| !js_trim(value).is_empty())
    })
}

/// TS `hasRequestAuth`.
pub(crate) fn has_request_auth(api_key: Option<&str>, headers: Option<&ProviderHeaders>) -> bool {
    api_key.is_some_and(|key| !key.is_empty())
        || has_header(headers, "authorization")
        || has_header(headers, "x-api-key")
        || has_header(headers, "cf-aig-authorization")
}

/// TS `getAnthropicFederation`: only for the `anthropic` provider and only
/// when no key or auth header was resolved.
pub(crate) fn get_anthropic_federation(
    model: &Model,
    api_key: Option<&str>,
    headers: Option<&ProviderHeaders>,
    env: Option<&ProviderEnv>,
) -> Option<AnthropicFederationConfig> {
    if model.provider != "anthropic" || has_request_auth(api_key, headers) {
        return None;
    }
    let federation_rule_id = get_provider_env_value(ANTHROPIC_FEDERATION_RULE_ID_ENV, env)?;
    let organization_id = get_provider_env_value(ANTHROPIC_ORGANIZATION_ID_ENV, env)?;
    let identity_token_file = get_provider_env_value(ANTHROPIC_IDENTITY_TOKEN_FILE_ENV, env)?;
    Some(AnthropicFederationConfig {
        organization_id,
        workspace_id: get_provider_env_value(ANTHROPIC_WORKSPACE_ID_ENV, env),
        authentication: FederationAuthentication {
            kind: "oidc_federation",
            federation_rule_id,
            service_account_id: get_provider_env_value(ANTHROPIC_SERVICE_ACCOUNT_ID_ENV, env),
            identity_token: IdentityTokenSource {
                source: "file",
                path: identity_token_file,
            },
        },
    })
}

const GRANT_TYPE_JWT_BEARER: &str = "urn:ietf:params:oauth:grant-type:jwt-bearer";
const TOKEN_ENDPOINT: &str = "/v1/oauth/token";
const OAUTH_API_BETA_HEADER: &str = "oauth-2025-04-20";
const FEDERATION_BETA_HEADER: &str = "oidc-federation-2026-04-01";
const ADVISORY_REFRESH_THRESHOLD_IN_SECONDS: f64 = 120.0;
const MANDATORY_REFRESH_THRESHOLD_IN_SECONDS: f64 = 30.0;
const ADVISORY_REFRESH_BACKOFF_IN_SECONDS: f64 = 5.0;
const MAX_TOKEN_RESPONSE_BYTES: usize = 1 << 20;
const MAX_ERROR_BODY_CHARS: usize = 2000;
const SAFE_ERROR_KEYS: [&str; 3] = ["error", "error_description", "error_uri"];

fn now_as_seconds() -> f64 {
    let elapsed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    // TS `Math.floor(Date.now() / 1000)`.
    elapsed.as_secs_f64().floor()
}

/// SDK `WorkloadIdentityError` / `AnthropicError` (JS name `Error`).
fn identity_error(message: String) -> Thrown {
    ErrorObject::new(message).thrown()
}

/// SDK `requireSecureTokenEndpoint`.
fn require_secure_token_endpoint(base_url: &str) -> Result<(), Thrown> {
    if base_url.is_empty() {
        return Ok(());
    }
    let url = reqwest::Url::parse(base_url).map_err(|_| {
        identity_error(format!(
            "Invalid token endpoint base URL \"{base_url}\": TypeError: Invalid URL"
        ))
    })?;
    if url.scheme() == "https" {
        return Ok(());
    }
    let host = url
        .host_str()
        .unwrap_or("")
        .to_ascii_lowercase()
        .trim_start_matches('[')
        .trim_end_matches(']')
        .to_owned();
    if url.scheme() == "http" && matches!(host.as_str(), "localhost" | "127.0.0.1" | "::1") {
        return Ok(());
    }
    Err(identity_error(format!(
        "Refusing to send credential over non-https token endpoint \"{base_url}\""
    )))
}

/// SDK `redactSensitive` on a string body.
fn redact_text(body: &str) -> String {
    if let Ok(parsed) = serde_json::from_str::<JsonValue>(body) {
        return json_stringify(&redact_value(&parsed));
    }
    let length = utf16_len(body);
    if length <= MAX_ERROR_BODY_CHARS {
        body.to_owned()
    } else {
        format!(
            "{}... <{} more chars>",
            utf16_prefix(body, MAX_ERROR_BODY_CHARS),
            length - MAX_ERROR_BODY_CHARS
        )
    }
}

/// SDK `redactSensitive` on parsed data.
fn redact_value(value: &JsonValue) -> JsonValue {
    match value {
        JsonValue::String(text) => JsonValue::String(redact_text(text)),
        JsonValue::Object(object) => JsonValue::Object(
            object
                .iter()
                .filter(|(key, _)| SAFE_ERROR_KEYS.contains(&key.as_str()))
                .map(|(key, value)| (key.clone(), value.clone()))
                .collect::<JsonObject>(),
        ),
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::Array(_) => {
            JsonValue::Null
        }
    }
}

/// A token from the exchange (TS `{ token, expiresAt }`).
#[derive(Debug, Clone)]
struct AccessToken {
    token: String,
    expires_at: f64,
}

/// The `oidc_federation` provider settings (TS `oidcFederationProvider` config).
#[derive(Debug, Clone)]
struct ExchangeConfig {
    identity_token_file: String,
    federation_rule_id: String,
    organization_id: String,
    service_account_id: Option<String>,
    workspace_id: Option<String>,
    base_url: String,
}

/// SDK `identityTokenFromFile`: reads the JWT on every call.
async fn read_identity_token(path: &str) -> Result<String, Thrown> {
    let content = tokio::fs::read(path).await.map_err(|error| {
        identity_error(format!(
            "Failed to read identity token file at {path}: Error: {error}"
        ))
    })?;
    let content = String::from_utf8_lossy(&content);
    let token = js_trim(&content);
    if token.is_empty() {
        return Err(identity_error(format!(
            "Identity token file at {path} is empty"
        )));
    }
    Ok(token.to_owned())
}

static HTTP_CLIENT: std::sync::LazyLock<reqwest::Client> =
    std::sync::LazyLock::new(reqwest::Client::new);

/// SDK `oidcFederationProvider(config)()`: one jwt-bearer token exchange.
#[allow(clippy::too_many_lines)] // One linear port of the SDK provider body.
async fn exchange_token(
    config: &ExchangeConfig,
    fetch: Option<&FetchFunction>,
) -> Result<AccessToken, Thrown> {
    require_secure_token_endpoint(&config.base_url)?;
    let jwt = read_identity_token(&config.identity_token_file).await?;
    if utf16_len(&jwt) > 16 * 1024 {
        return Err(identity_error(format!(
            "Identity token is {} KiB, exceeds the 16 KiB assertion limit",
            utf16_len(&jwt).div_ceil(1024)
        )));
    }
    let mut body = JsonObject::new();
    body.insert("grant_type".into(), GRANT_TYPE_JWT_BEARER.into());
    body.insert("assertion".into(), jwt.into());
    body.insert(
        "federation_rule_id".into(),
        config.federation_rule_id.clone().into(),
    );
    body.insert(
        "organization_id".into(),
        config.organization_id.clone().into(),
    );
    if let Some(id) = config
        .service_account_id
        .as_ref()
        .filter(|id| !id.is_empty())
    {
        body.insert("service_account_id".into(), id.clone().into());
    }
    if let Some(id) = config.workspace_id.as_ref().filter(|id| !id.is_empty()) {
        body.insert("workspace_id".into(), id.clone().into());
    }
    let url = format!("{}{TOKEN_ENDPOINT}", config.base_url);
    let reach_error =
        |cause: String| identity_error(format!("Failed to reach token endpoint {url}: {cause}"));
    let parsed_url =
        reqwest::Url::parse(&url).map_err(|_| reach_error("TypeError: Invalid URL".to_owned()))?;
    let mut request = reqwest::Request::new(reqwest::Method::POST, parsed_url);
    let headers = request.headers_mut();
    headers.insert(
        reqwest::header::CONTENT_TYPE,
        reqwest::header::HeaderValue::from_static("application/json"),
    );
    headers.insert(
        "anthropic-beta",
        reqwest::header::HeaderValue::from_str(&format!(
            "{OAUTH_API_BETA_HEADER},{FEDERATION_BETA_HEADER}"
        ))
        .map_err(|error| reach_error(error.to_string()))?,
    );
    headers.insert(
        reqwest::header::USER_AGENT,
        reqwest::header::HeaderValue::from_str(&format!("Anthropic/JS {SDK_VERSION}"))
            .map_err(|error| reach_error(error.to_string()))?,
    );
    *request.body_mut() = Some(json_stringify(&JsonValue::Object(body)).into());
    let response = match fetch {
        Some(fetch) => fetch(request)
            .await
            .map_err(|error| reach_error(error.to_string()))?,
        None => HTTP_CLIENT
            .execute(request)
            .await
            .map_err(|error| reach_error(format!("TypeError: {error}")))?,
    };
    let status = response.status().as_u16();
    let request_id = response
        .headers()
        .get("request-id")
        .and_then(|value| value.to_str().ok())
        .map(str::to_owned);
    if !response.status().is_success() {
        let text = response.text().await.unwrap_or_default();
        let redacted = redact_text(&text);
        let hint = if status == 401 {
            let middle = if config
                .workspace_id
                .as_ref()
                .is_some_and(|id| !id.is_empty())
            {
                ""
            } else {
                "If your federation rule is scoped to multiple workspaces, set the ANTHROPIC_WORKSPACE_ID environment variable, the 'workspace_id' config key, or the `workspaceId` option. "
            };
            format!(" Ensure your federation rule matches your identity token. {middle}View your authentication events in the Workload identity page of Claude Console for more details.")
        } else {
            String::new()
        };
        let request_id = request_id
            .map(|id| format!(" (request-id {id})"))
            .unwrap_or_default();
        return Err(identity_error(format!(
            "Token exchange failed with status {status}{request_id}: {redacted}{hint}"
        )));
    }
    let data = parse_token_response(response, status).await?;
    let expires_in = match data.get("expires_in") {
        Some(JsonValue::Number(number)) => number.as_f64(),
        Some(JsonValue::String(text)) => js_trim(text)
            .parse::<f64>()
            .ok()
            .or_else(|| js_trim(text).is_empty().then_some(0.0)),
        Some(JsonValue::Bool(flag)) => Some(f64::from(u8::from(*flag))),
        Some(JsonValue::Null) => Some(0.0),
        _ => None,
    }
    .filter(|value| value.is_finite());
    let Some(expires_in) = expires_in else {
        return Err(identity_error(format!(
            "Token endpoint response missing required fields: {}",
            json_stringify(&redact_value(&data))
        )));
    };
    Ok(AccessToken {
        token: crate::utils::js::js_to_string(data.get("access_token").unwrap_or(&JsonValue::Null)),
        expires_at: now_as_seconds() + expires_in,
    })
}

/// SDK `parseTokenResponse` (reads at most 1 MiB).
async fn parse_token_response(
    mut response: reqwest::Response,
    status: u16,
) -> Result<JsonValue, Thrown> {
    let mut bytes: Vec<u8> = Vec::new();
    while let Ok(Some(chunk)) = response.chunk().await {
        if bytes.len() + chunk.len() > MAX_TOKEN_RESPONSE_BYTES {
            let remaining = MAX_TOKEN_RESPONSE_BYTES - bytes.len();
            bytes.extend_from_slice(&chunk[..remaining]);
            break;
        }
        bytes.extend_from_slice(&chunk);
    }
    let text = String::from_utf8_lossy(&bytes);
    let Ok(data) = serde_json::from_str::<JsonValue>(&text) else {
        return Err(identity_error(format!(
            "Token endpoint returned non-JSON response (status {status})"
        )));
    };
    let truthy_token = match data.get("access_token") {
        None | Some(JsonValue::Null) => false,
        Some(JsonValue::String(text)) => !text.is_empty(),
        Some(JsonValue::Bool(flag)) => *flag,
        Some(JsonValue::Number(number)) => number.as_f64().is_some_and(|n| n != 0.0),
        Some(JsonValue::Array(_) | JsonValue::Object(_)) => true,
    };
    if !truthy_token {
        return Err(identity_error(format!(
            "Token endpoint response missing access_token: {}",
            json_stringify(&redact_value(&data))
        )));
    }
    if let Some(JsonValue::String(token_type)) = data.get("token_type") {
        if !token_type.is_empty() && token_type.to_lowercase() != "bearer" {
            return Err(identity_error(format!(
                "Token endpoint response: unsupported token_type \"{token_type}\" (want Bearer)"
            )));
        }
    }
    Ok(data)
}

/// SDK `TokenCache` state.
#[derive(Debug, Default)]
struct TokenCacheState {
    cached: Option<AccessToken>,
    next_force: bool,
    last_advisory_error: f64,
    /// Bumped by every successful refresh, so callers that waited on the
    /// refresh lock join the refresh that just finished.
    generation: u64,
    refreshing: bool,
}

/// The token cache of a federated client (SDK `TokenCache` over
/// `oidcFederationProvider`): proactive refresh with deduplication.
#[derive(Debug)]
pub(crate) struct FederationAuth {
    config: ExchangeConfig,
    state: Mutex<TokenCacheState>,
    refresh_lock: tokio::sync::Mutex<()>,
}

impl FederationAuth {
    fn new(config: &AnthropicFederationConfig, base_url: &str) -> Self {
        Self {
            config: ExchangeConfig {
                identity_token_file: config.authentication.identity_token.path.clone(),
                federation_rule_id: config.authentication.federation_rule_id.clone(),
                organization_id: config.organization_id.clone(),
                service_account_id: config.authentication.service_account_id.clone(),
                workspace_id: config.workspace_id.clone(),
                base_url: base_url.trim_end_matches('/').to_owned(),
            },
            state: Mutex::new(TokenCacheState::default()),
            refresh_lock: tokio::sync::Mutex::new(()),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, TokenCacheState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// SDK `TokenCache.getToken`.
    pub(crate) async fn get_token(
        self: &Arc<Self>,
        fetch: Option<&FetchFunction>,
    ) -> Result<String, Thrown> {
        let (force, cached) = {
            let mut state = self.lock();
            let force = std::mem::take(&mut state.next_force);
            (force, state.cached.clone())
        };
        let cached = match cached {
            Some(cached) if !force => cached,
            _ => return self.refresh(force, fetch).await,
        };
        let remaining = cached.expires_at - now_as_seconds();
        if remaining > ADVISORY_REFRESH_THRESHOLD_IN_SECONDS {
            return Ok(cached.token);
        }
        if remaining > MANDATORY_REFRESH_THRESHOLD_IN_SECONDS {
            self.background_refresh(fetch.cloned());
            return Ok(cached.token);
        }
        self.refresh(false, fetch).await
    }

    /// SDK `TokenCache.invalidate`.
    pub(crate) fn invalidate(&self) {
        let mut state = self.lock();
        state.cached = None;
        state.next_force = true;
    }

    /// SDK `TokenCache.refresh`: joins an in-flight refresh unless forced.
    async fn refresh(&self, force: bool, fetch: Option<&FetchFunction>) -> Result<String, Thrown> {
        let generation = self.lock().generation;
        let _guard = self.refresh_lock.lock().await;
        if !force {
            let state = self.lock();
            if state.generation != generation {
                if let Some(cached) = &state.cached {
                    return Ok(cached.token.clone());
                }
            }
        }
        self.do_refresh(fetch).await
    }

    async fn do_refresh(&self, fetch: Option<&FetchFunction>) -> Result<String, Thrown> {
        self.lock().refreshing = true;
        let result = exchange_token(&self.config, fetch).await;
        let mut state = self.lock();
        state.refreshing = false;
        let token = result?;
        state.generation += 1;
        state.cached = Some(token.clone());
        Ok(token.token)
    }

    /// SDK `TokenCache.backgroundRefresh`: errors keep the stale token.
    fn background_refresh(self: &Arc<Self>, fetch: Option<FetchFunction>) {
        {
            let state = self.lock();
            if state.refreshing
                || now_as_seconds() - state.last_advisory_error
                    < ADVISORY_REFRESH_BACKOFF_IN_SECONDS
            {
                return;
            }
        }
        let this = Arc::clone(self);
        tokio::spawn(async move {
            let Ok(_guard) = this.refresh_lock.try_lock() else {
                return;
            };
            if this.do_refresh(fetch.as_ref()).await.is_err() {
                this.lock().last_advisory_error = now_as_seconds();
            }
        });
    }
}

/// TS module-level `federationClient`: one token cache for the current
/// federation config and fetch, shared across requests.
struct FederationClient {
    key: String,
    fetch: Option<FetchFunction>,
    auth: Arc<FederationAuth>,
}

static FEDERATION_CLIENT: Mutex<Option<FederationClient>> = Mutex::new(None);

fn same_fetch(left: Option<&FetchFunction>, right: Option<&FetchFunction>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => Arc::ptr_eq(left, right),
        (None, Some(_)) | (Some(_), None) => false,
    }
}

/// The shared federated auth for `base_url` + `config` + `fetch`, rebuilt
/// when any of them changes.
pub(crate) fn federation_auth(
    base_url: &str,
    config: &AnthropicFederationConfig,
    fetch: Option<&FetchFunction>,
) -> Arc<FederationAuth> {
    let key = json_stringify(&serde_json::json!([base_url, config]));
    let mut slot = FEDERATION_CLIENT
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    if let Some(client) = slot.as_ref() {
        if client.key == key && same_fetch(client.fetch.as_ref(), fetch) {
            return Arc::clone(&client.auth);
        }
    }
    let auth = Arc::new(FederationAuth::new(config, base_url));
    *slot = Some(FederationClient {
        key,
        fetch: fetch.cloned(),
        auth: Arc::clone(&auth),
    });
    auth
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn redacts_token_error_bodies() {
        assert_eq!(
            redact_text(r#"{"error":"invalid_grant","assertion":"secret"}"#),
            r#"{"error":"invalid_grant"}"#
        );
        assert_eq!(redact_text("plain"), "plain");
    }

    #[test]
    fn rejects_cleartext_token_endpoints() {
        assert!(require_secure_token_endpoint("https://api.anthropic.com").is_ok());
        assert!(require_secure_token_endpoint("http://localhost:8080").is_ok());
        assert!(require_secure_token_endpoint("http://[::1]:8080").is_ok());
        assert_eq!(
            require_secure_token_endpoint("http://example.com")
                .unwrap_err()
                .to_string(),
            "Refusing to send credential over non-https token endpoint \"http://example.com\""
        );
    }
}
