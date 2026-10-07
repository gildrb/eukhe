//! `OpenAI` Codex (`ChatGPT` OAuth) flow. Port of `auth/oauth/openai-codex.ts`.

use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use futures::future::BoxFuture;
use serde_json::Value;

use super::callback_server::{
    start_oauth_callback_server, wait_for_callback_or_manual_input, CallbackOrManual,
    OAuthCallbackServerOptions,
};
use super::device_code::{
    poll_oauth_device_code_flow, OAuthDeviceCodePollOptions, OAuthDeviceCodePollResult,
};
use super::http::{fetch, form_urlencode, FetchRequest, FetchResponse};
use super::pkce::{generate_pkce, random_bytes};
use super::{
    api_key_auth, decode_jwt_payload, js_number_from_string, parse_authorization_input, shared,
    truthy_str,
};
use crate::auth::errors::{date_now, js_error};
use crate::auth::types::{
    AuthEvent, AuthPrompt, AuthPromptKind, AuthSelectOption, LoginOptions, ModelAuth, OAuthAuth,
    OAuthCredential, ProviderAuthInteraction,
};
use crate::utils::diagnostics::Thrown;
use crate::utils::provider_env::get_provider_env_value;

const CLIENT_ID: &str = "app_EMoamEEZ73f0CkXaXp7hrann";
const AUTHORIZE_URL: &str = "https://auth.openai.com/oauth/authorize";
const TOKEN_URL: &str = "https://auth.openai.com/oauth/token";
const REDIRECT_URI: &str = "http://localhost:1455/auth/callback";
const DEVICE_USER_CODE_URL: &str = "https://auth.openai.com/api/accounts/deviceauth/usercode";
const DEVICE_TOKEN_URL: &str = "https://auth.openai.com/api/accounts/deviceauth/token";
const DEVICE_VERIFICATION_URI: &str = "https://auth.openai.com/codex/device";
const DEVICE_REDIRECT_URI: &str = "https://auth.openai.com/deviceauth/callback";
const DEVICE_CODE_TIMEOUT_SECONDS: f64 = 15.0 * 60.0;
const OPENAI_CODEX_BROWSER_LOGIN_METHOD: &str = "browser";
const OPENAI_CODEX_DEVICE_CODE_LOGIN_METHOD: &str = "device_code";
const SCOPE: &str = "openid profile email offline_access";
const JWT_CLAIM_PATH: &str = "https://api.openai.com/auth";

struct OAuthToken {
    access: String,
    refresh: String,
    expires: f64,
}

#[derive(Clone, Copy)]
enum TokenOperation {
    Exchange,
    Refresh,
}

impl TokenOperation {
    fn as_str(self) -> &'static str {
        match self {
            Self::Exchange => "exchange",
            Self::Refresh => "refresh",
        }
    }
}

fn get_callback_host() -> String {
    get_provider_env_value("PI_OAUTH_CALLBACK_HOST", None).unwrap_or_else(|| "127.0.0.1".to_owned())
}

struct DeviceAuthInfo {
    device_auth_id: String,
    user_code: String,
    interval_seconds: f64,
}

#[derive(Clone)]
struct DeviceTokenSuccess {
    authorization_code: String,
    code_verifier: String,
}

fn create_state() -> Result<String, Thrown> {
    Ok(hex::encode(random_bytes::<16>()?))
}

async fn fetch_with_login_cancellation(
    request: FetchRequest,
    signal: &AbortSignal,
) -> Result<FetchResponse, Thrown> {
    fetch(request, Some(signal)).await.map_err(|error| {
        if signal.aborted() {
            js_error("Login cancelled")
        } else {
            error
        }
    })
}

fn read_token_response(
    response: &FetchResponse,
    operation: TokenOperation,
) -> Result<OAuthToken, Thrown> {
    let operation = operation.as_str();
    if !response.ok() {
        let text = if response.body.is_empty() {
            &response.status_text
        } else {
            &response.body
        };
        return Err(js_error(format!(
            "OpenAI Codex token {operation} failed ({}): {text}",
            response.status
        )));
    }

    let json = response.json()?;
    match (
        truthy_str(&json, "access_token"),
        truthy_str(&json, "refresh_token"),
        json.get("expires_in").and_then(Value::as_f64),
    ) {
        (Some(access), Some(refresh), Some(expires_in)) => Ok(OAuthToken {
            access: access.to_owned(),
            refresh: refresh.to_owned(),
            expires: date_now() + expires_in * 1000.0,
        }),
        _ => Err(js_error(format!(
            "OpenAI Codex token {operation} response missing fields: {json}"
        ))),
    }
}

async fn exchange_authorization_code(
    code: &str,
    verifier: &str,
    redirect_uri: &str,
    signal: &AbortSignal,
) -> Result<OAuthToken, Thrown> {
    let response = fetch_with_login_cancellation(
        FetchRequest::post(TOKEN_URL)
            .header("Content-Type", "application/x-www-form-urlencoded")
            .form(&[
                ("grant_type", "authorization_code"),
                ("client_id", CLIENT_ID),
                ("code", code),
                ("code_verifier", verifier),
                ("redirect_uri", redirect_uri),
            ]),
        signal,
    )
    .await?;
    read_token_response(&response, TokenOperation::Exchange)
}

async fn refresh_access_token(
    refresh_token: &str,
    signal: &AbortSignal,
) -> Result<OAuthToken, Thrown> {
    let response = fetch(
        FetchRequest::post(TOKEN_URL)
            .header("Content-Type", "application/x-www-form-urlencoded")
            .form(&[
                ("grant_type", "refresh_token"),
                ("refresh_token", refresh_token),
                ("client_id", CLIENT_ID),
            ]),
        Some(signal),
    )
    .await
    .map_err(|error| js_error(format!("OpenAI Codex token refresh error: {error}")))?;
    read_token_response(&response, TokenOperation::Refresh)
}

async fn start_openai_codex_device_auth(signal: &AbortSignal) -> Result<DeviceAuthInfo, Thrown> {
    let response = fetch_with_login_cancellation(
        FetchRequest::post(DEVICE_USER_CODE_URL)
            .header("Content-Type", "application/json")
            .body(serde_json::json!({ "client_id": CLIENT_ID }).to_string()),
        signal,
    )
    .await?;

    if !response.ok() {
        if response.status == 404 {
            return Err(js_error(
                "OpenAI Codex device code login is not enabled for this server. Use browser login or verify the server URL.",
            ));
        }
        let suffix = if response.body.is_empty() {
            String::new()
        } else {
            format!(": {}", response.body)
        };
        return Err(js_error(format!(
            "OpenAI Codex device code request failed with status {}{suffix}",
            response.status
        )));
    }

    let json = response.json()?;
    let interval_seconds = match json.get("interval") {
        Some(Value::String(interval)) => Some(js_number_from_string(interval)),
        Some(Value::Number(interval)) => interval.as_f64(),
        _ => None,
    };
    match (
        truthy_str(&json, "device_auth_id"),
        truthy_str(&json, "user_code"),
        interval_seconds,
    ) {
        (Some(device_auth_id), Some(user_code), Some(interval_seconds))
            if interval_seconds.is_finite() && interval_seconds >= 0.0 =>
        {
            Ok(DeviceAuthInfo {
                device_auth_id: device_auth_id.to_owned(),
                user_code: user_code.to_owned(),
                interval_seconds,
            })
        }
        _ => Err(js_error(format!(
            "Invalid OpenAI Codex device code response: {json}"
        ))),
    }
}

async fn poll_device_token_once(
    device: &DeviceAuthInfo,
    signal: &AbortSignal,
) -> Result<OAuthDeviceCodePollResult<DeviceTokenSuccess>, Thrown> {
    let response = fetch_with_login_cancellation(
        FetchRequest::post(DEVICE_TOKEN_URL)
            .header("Content-Type", "application/json")
            .body(
                serde_json::json!({
                    "device_auth_id": device.device_auth_id,
                    "user_code": device.user_code,
                })
                .to_string(),
            ),
        signal,
    )
    .await?;

    if response.ok() {
        let json = response.json()?;
        return Ok(
            match (
                truthy_str(&json, "authorization_code"),
                truthy_str(&json, "code_verifier"),
            ) {
                (Some(authorization_code), Some(code_verifier)) => {
                    OAuthDeviceCodePollResult::Complete {
                        value: DeviceTokenSuccess {
                            authorization_code: authorization_code.to_owned(),
                            code_verifier: code_verifier.to_owned(),
                        },
                    }
                }
                _ => OAuthDeviceCodePollResult::Failed {
                    message: format!("Invalid OpenAI Codex device auth token response: {json}"),
                },
            },
        );
    }

    if response.status == 403 || response.status == 404 {
        return Ok(OAuthDeviceCodePollResult::Pending);
    }

    let response_body = &response.body;
    let error_code = serde_json::from_str::<Value>(response_body)
        .ok()
        .and_then(|json| match json.get("error") {
            Some(Value::String(code)) => Some(code.clone()),
            Some(Value::Object(error)) => {
                error.get("code").and_then(Value::as_str).map(str::to_owned)
            }
            _ => None,
        });

    match error_code.as_deref() {
        Some("deviceauth_authorization_pending") => Ok(OAuthDeviceCodePollResult::Pending),
        Some("slow_down") => Ok(OAuthDeviceCodePollResult::SlowDown {
            interval_seconds: None,
        }),
        _ => {
            let suffix = if response_body.is_empty() {
                String::new()
            } else {
                format!(": {response_body}")
            };
            Ok(OAuthDeviceCodePollResult::Failed {
                message: format!(
                    "OpenAI Codex device auth failed with status {}{suffix}",
                    response.status
                ),
            })
        }
    }
}

async fn poll_openai_codex_device_auth(
    device: &DeviceAuthInfo,
    signal: &AbortSignal,
) -> Result<DeviceTokenSuccess, Thrown> {
    poll_oauth_device_code_flow(
        OAuthDeviceCodePollOptions {
            interval_seconds: Some(device.interval_seconds),
            expires_in_seconds: Some(DEVICE_CODE_TIMEOUT_SECONDS),
            wait_before_first_poll: false,
            signal: signal.clone(),
        },
        || poll_device_token_once(device, signal),
    )
    .await
}

struct AuthorizationFlow {
    verifier: String,
    state: String,
    url: String,
}

fn create_authorization_flow(originator: &str) -> Result<AuthorizationFlow, Thrown> {
    let pkce = generate_pkce()?;
    let state = create_state()?;
    let query = form_urlencode(&[
        ("response_type", "code"),
        ("client_id", CLIENT_ID),
        ("redirect_uri", REDIRECT_URI),
        ("scope", SCOPE),
        ("code_challenge", &pkce.challenge),
        ("code_challenge_method", "S256"),
        ("state", &state),
        ("id_token_add_organizations", "true"),
        ("codex_cli_simplified_flow", "true"),
        ("originator", originator),
    ]);
    Ok(AuthorizationFlow {
        verifier: pkce.verifier,
        state,
        url: format!("{AUTHORIZE_URL}?{query}"),
    })
}

fn get_account_id(access_token: &str) -> Option<String> {
    let payload = decode_jwt_payload(access_token)?;
    payload
        .get(JWT_CLAIM_PATH)?
        .get("chatgpt_account_id")?
        .as_str()
        .filter(|id| !id.is_empty())
        .map(str::to_owned)
}

fn credentials_from_token(token: OAuthToken) -> Result<OAuthCredential, Thrown> {
    let account_id = get_account_id(&token.access)
        .ok_or_else(|| js_error("Failed to extract accountId from token"))?;
    let mut credential = OAuthCredential::new(token.refresh, token.access, token.expires);
    credential
        .extra
        .insert("accountId".to_owned(), Value::String(account_id));
    Ok(credential)
}

async fn exchange_authorization_code_for_credentials(
    code: &str,
    verifier: &str,
    redirect_uri: &str,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    credentials_from_token(exchange_authorization_code(code, verifier, redirect_uri, signal).await?)
}

async fn login_openai_codex_device_code(
    interaction: &ProviderAuthInteraction,
) -> Result<OAuthCredential, Thrown> {
    let device = start_openai_codex_device_auth(&interaction.signal).await?;
    interaction.notify(AuthEvent::DeviceCode {
        user_code: device.user_code.clone(),
        verification_uri: DEVICE_VERIFICATION_URI.to_owned(),
        interval_seconds: Some(device.interval_seconds),
        expires_in_seconds: Some(DEVICE_CODE_TIMEOUT_SECONDS),
    });
    let code = poll_openai_codex_device_auth(&device, &interaction.signal).await?;
    exchange_authorization_code_for_credentials(
        &code.authorization_code,
        &code.code_verifier,
        DEVICE_REDIRECT_URI,
        &interaction.signal,
    )
    .await
}

async fn login_openai_codex(
    interaction: &ProviderAuthInteraction,
) -> Result<OAuthCredential, Thrown> {
    let flow = create_authorization_flow("pi")?;
    // Port 1455 is shared with the Codex CLI; when it is taken, fall back to the pasted redirect URL.
    let callback = start_oauth_callback_server(OAuthCallbackServerOptions {
        provider_name: "OpenAI".to_owned(),
        host: get_callback_host(),
        port: 1455,
        path: "/auth/callback".to_owned(),
        redirect_host: None,
        state: Some(flow.state.clone()),
        complete: Arc::new(|code| Box::pin(async move { Ok(code) })),
        signal: Some(interaction.signal.clone()),
        timeout_ms: None,
    })
    .await
    .ok();

    interaction.notify(AuthEvent::AuthUrl {
        url: flow.url.clone(),
        instructions: Some("A browser window should open. Complete login to finish.".to_owned()),
    });

    let result = async {
        let result = wait_for_callback_or_manual_input(
            interaction,
            callback.as_ref(),
            "Complete login in your browser, or paste the authorization code / redirect URL here:",
            REDIRECT_URI,
        )
        .await?;
        let code = match result {
            CallbackOrManual::Callback { value } => Some(value),
            CallbackOrManual::Manual { input } => {
                let parsed = parse_authorization_input(&input);
                if parsed
                    .state
                    .as_ref()
                    .is_some_and(|state| !state.is_empty() && *state != flow.state)
                {
                    return Err(js_error("State mismatch"));
                }
                parsed.code
            }
        };

        let Some(code) = code.filter(|code| !code.is_empty()) else {
            return Err(js_error("Missing authorization code"));
        };
        exchange_authorization_code_for_credentials(
            &code,
            &flow.verifier,
            REDIRECT_URI,
            &interaction.signal,
        )
        .await
    }
    .await;
    if let Some(callback) = &callback {
        callback.close();
    }
    result
}

/// Refresh `OpenAI` Codex OAuth token.
async fn refresh_openai_codex_token(
    refresh_token: &str,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    credentials_from_token(refresh_access_token(refresh_token, signal).await?)
}

struct OpenAICodexOAuth;

impl OAuthAuth for OpenAICodexOAuth {
    fn name(&self) -> &'static str {
        "OpenAI (ChatGPT Plus/Pro)"
    }

    fn is_subscription(&self) -> Option<bool> {
        Some(true)
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        _options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move {
            let method = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Select {
                    message: "Select OpenAI Codex login method:".to_owned(),
                    options: vec![
                        AuthSelectOption::new(
                            OPENAI_CODEX_BROWSER_LOGIN_METHOD,
                            "Browser login (default)",
                        ),
                        AuthSelectOption::new(
                            OPENAI_CODEX_DEVICE_CODE_LOGIN_METHOD,
                            "Device code login (headless)",
                        ),
                    ],
                }))
                .await?;

            if method == OPENAI_CODEX_DEVICE_CODE_LOGIN_METHOD {
                return login_openai_codex_device_code(&interaction).await;
            }
            if method != OPENAI_CODEX_BROWSER_LOGIN_METHOD {
                return Err(js_error(format!(
                    "Unknown OpenAI Codex login method: {method}"
                )));
            }
            login_openai_codex(&interaction).await
        })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { refresh_openai_codex_token(&credential.refresh, &signal).await })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move { Ok(api_key_auth(&credential.access)) })
    }
}

/// The `OpenAI` Codex (`ChatGPT` Plus/Pro) OAuth flow (`openaiCodexOAuth`).
#[must_use]
pub fn openai_codex_oauth() -> Arc<dyn OAuthAuth> {
    shared(OpenAICodexOAuth)
}

#[cfg(test)]
#[path = "openai_codex_tests.rs"]
mod tests;
