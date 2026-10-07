//! Radius gateway OAuth flow. Port of `auth/oauth/radius.ts`.
//!
//! Radius is a pi-messages gateway. OAuth client APIs live on the configured
//! gateway; only the interactive browser authorization endpoint is discovered.
//! Model catalog loading is owned by the Radius provider.

use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use futures::future::BoxFuture;
use serde::Deserialize;
use serde_json::Value;

use super::callback_server::{start_oauth_callback_server, OAuthCallbackServerOptions};
use super::device_code::{
    poll_oauth_device_code_flow, OAuthDeviceCodePollOptions, OAuthDeviceCodePollResult,
};
use super::http::{fetch, form_urlencode, FetchRequest, FetchResponse};
use super::pkce::generate_pkce;
use super::{api_key_auth, string_field};
use crate::auth::errors::{date_now, js_error, named_error};
use crate::auth::types::{
    AuthEvent, AuthPrompt, AuthPromptKind, AuthSelectOption, LoginOptions, ModelAuth, OAuthAuth,
    OAuthCredential, ProviderAuthInteraction,
};
use crate::providers::radius_config::normalize_radius_gateway_url;
use crate::utils::diagnostics::Thrown;

const CALLBACK_HOST: &str = "127.0.0.1";
const CALLBACK_PORT: u16 = 1456;
const CALLBACK_PATH: &str = "/oauth/callback";
const REDIRECT_URI: &str = "http://127.0.0.1:1456/oauth/callback";
const TOKEN_EXPIRY_SKEW_MS: f64 = 60_000.0;
const LOGIN_METHOD_BROWSER: &str = "browser";
const LOGIN_METHOD_DEVICE_CODE: &str = "device-code";
const OAUTH_CLIENT_ID: &str = "pi-gateway";
const OAUTH_SCOPE: &str = "gateway offline_access";
const OAUTH_DEVICE_CODE_GRANT_TYPE: &str = "urn:ietf:params:oauth:grant-type:device_code";

struct DeviceAuthorizationResponse {
    device_code: String,
    user_code: String,
    verification_uri: String,
    expires_in: f64,
    interval: Option<f64>,
}

/// `new URL(path, gateway).toString()`.
fn gateway_url(gateway: &str, path: &str) -> Result<String, Thrown> {
    url::Url::parse(gateway)
        .and_then(|base| base.join(path))
        .map(|url| url.to_string())
        .map_err(|_| named_error("TypeError", "Invalid URL"))
}

async fn load_radius_oauth_discovery(
    gateway: &str,
    signal: &AbortSignal,
) -> Result<String, Thrown> {
    let response = fetch(
        FetchRequest::get(gateway_url(gateway, "/v1/oauth")?).header("accept", "application/json"),
        Some(signal),
    )
    .await?;

    if !response.ok() {
        return Err(js_error(format!(
            "Could not load Radius OAuth config from {gateway}: {} {}",
            response.status, response.body
        )));
    }

    let discovery = response.json()?;
    match string_field(&discovery, "authorizationEndpoint") {
        Some(endpoint) => Ok(endpoint.to_owned()),
        None => Err(js_error(format!(
            "Invalid Radius OAuth config from {gateway}"
        ))),
    }
}

/// An OAuth error response (`error` / `error_description`).
#[derive(Debug, Clone, thiserror::Error)]
#[error("{message}")]
struct OAuthResponseError {
    oauth_error: Option<String>,
    message: String,
}

impl OAuthResponseError {
    fn new(
        status: u16,
        oauth_error: Option<String>,
        description: Option<String>,
        message: &str,
    ) -> Self {
        let description = description.filter(|description| !description.is_empty());
        let detail = match (&oauth_error, description) {
            (Some(error), Some(description)) => format!("{error}: {description}"),
            (Some(error), None) => error.clone(),
            (None, Some(description)) => description,
            (None, None) => status.to_string(),
        };
        Self {
            oauth_error,
            message: format!("{message}: {detail}"),
        }
    }
}

fn read_oauth_response_error(response: &FetchResponse, message: &str) -> OAuthResponseError {
    let text = &response.body;
    let mut oauth_error = None;
    let mut description = None;
    if !text.is_empty() {
        match serde_json::from_str::<Value>(text) {
            Ok(data) => {
                oauth_error = string_field(&data, "error").map(str::to_owned);
                description = string_field(&data, "error_description").map(str::to_owned);
            }
            Err(_) => description = Some(text.clone()),
        }
    }
    OAuthResponseError::new(response.status, oauth_error, description, message)
}

#[derive(Deserialize)]
struct TokenData {
    access_token: String,
    refresh_token: String,
    expires_in: f64,
    scope: Option<String>,
}

async fn request_oauth_token(
    gateway: &str,
    fields: &[(&str, &str)],
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    let response = fetch(
        FetchRequest::post(gateway_url(gateway, "/v1/oauth/token")?)
            .header("accept", "application/json")
            .header("content-type", "application/x-www-form-urlencoded")
            .form(fields),
        Some(signal),
    )
    .await
    .map_err(|error| {
        if signal.aborted() {
            js_error("Login cancelled")
        } else {
            error
        }
    })?;

    if !response.ok() {
        return Err(Arc::new(read_oauth_response_error(
            &response,
            "Radius OAuth token request failed",
        )));
    }

    let data: TokenData = serde_json::from_str(&response.body)
        .map_err(|error| named_error("SyntaxError", error.to_string()))?;
    let mut credential = OAuthCredential::new(
        data.refresh_token,
        data.access_token,
        date_now() + data.expires_in * 1000.0 - TOKEN_EXPIRY_SKEW_MS,
    );
    if let Some(scope) = data.scope {
        credential
            .extra
            .insert("scope".to_owned(), Value::String(scope));
    }
    Ok(credential)
}

async fn login_with_browser(
    gateway: &str,
    authorization_endpoint: &str,
    interaction: &ProviderAuthInteraction,
) -> Result<OAuthCredential, Thrown> {
    let pkce = generate_pkce()?;
    let state = uuid::Uuid::new_v4().to_string();
    let mut authorize_url = url::Url::parse(authorization_endpoint)
        .map_err(|_| named_error("TypeError", "Invalid URL"))?;
    authorize_url.set_query(Some(&form_urlencode(&[
        ("response_type", "code"),
        ("client_id", OAUTH_CLIENT_ID),
        ("redirect_uri", REDIRECT_URI),
        ("scope", OAUTH_SCOPE),
        ("code_challenge", &pkce.challenge),
        ("code_challenge_method", "S256"),
        ("handoff", "url"),
        ("state", &state),
    ])));

    let complete_gateway = gateway.to_owned();
    let verifier = pkce.verifier.clone();
    let complete_signal = interaction.signal.clone();
    let callback = start_oauth_callback_server(OAuthCallbackServerOptions {
        provider_name: "Radius".to_owned(),
        host: CALLBACK_HOST.to_owned(),
        port: CALLBACK_PORT,
        path: CALLBACK_PATH.to_owned(),
        redirect_host: None,
        state: Some(state),
        complete: Arc::new(move |code| {
            let gateway = complete_gateway.clone();
            let verifier = verifier.clone();
            let signal = complete_signal.clone();
            Box::pin(async move {
                request_oauth_token(
                    &gateway,
                    &[
                        ("grant_type", "authorization_code"),
                        ("client_id", OAUTH_CLIENT_ID),
                        ("redirect_uri", REDIRECT_URI),
                        ("code", &code),
                        ("code_verifier", &verifier),
                    ],
                    &signal,
                )
                .await
            })
        }),
        signal: Some(interaction.signal.clone()),
        timeout_ms: None,
    })
    .await?;
    interaction.notify(AuthEvent::Progress {
        message: format!("Listening for OAuth callback on {REDIRECT_URI}"),
    });
    interaction.notify(AuthEvent::AuthUrl {
        url: authorize_url.to_string(),
        instructions: Some("Continue in your browser.".to_owned()),
    });

    let result = match callback.wait().await {
        Ok(Some(credential)) => Ok(credential),
        Ok(None) => Err(js_error("OAuth callback did not complete.")),
        Err(error) => Err(error),
    };
    callback.close();
    result
}

async fn request_device_authorization(
    gateway: &str,
    signal: &AbortSignal,
) -> Result<DeviceAuthorizationResponse, Thrown> {
    let response = fetch(
        FetchRequest::post(gateway_url(gateway, "/v1/oauth/device")?)
            .header("accept", "application/json")
            .header("content-type", "application/x-www-form-urlencoded")
            .form(&[("client_id", OAUTH_CLIENT_ID), ("scope", OAUTH_SCOPE)]),
        Some(signal),
    )
    .await
    .map_err(|error| {
        if signal.aborted() {
            js_error("Login cancelled")
        } else {
            error
        }
    })?;

    if !response.ok() {
        return Err(Arc::new(read_oauth_response_error(
            &response,
            "Radius OAuth device authorization failed",
        )));
    }

    let data = response.json()?;
    let truthy = |field: &str| super::truthy_str(&data, field).map(str::to_owned);
    let expires_in = data
        .get("expires_in")
        .and_then(Value::as_f64)
        .filter(|value| *value != 0.0 && !value.is_nan());
    match (
        truthy("device_code"),
        truthy("user_code"),
        truthy("verification_uri"),
        expires_in,
    ) {
        (Some(device_code), Some(user_code), Some(verification_uri), Some(expires_in)) => {
            Ok(DeviceAuthorizationResponse {
                device_code,
                user_code,
                verification_uri,
                expires_in,
                interval: data.get("interval").and_then(Value::as_f64),
            })
        }
        _ => Err(js_error(
            "Radius OAuth device authorization response is missing required fields",
        )),
    }
}

async fn poll_device_token(
    gateway: &str,
    device: &DeviceAuthorizationResponse,
    signal: &AbortSignal,
) -> Result<OAuthDeviceCodePollResult<OAuthCredential>, Thrown> {
    match request_oauth_token(
        gateway,
        &[
            ("grant_type", OAUTH_DEVICE_CODE_GRANT_TYPE),
            ("client_id", OAUTH_CLIENT_ID),
            ("device_code", &device.device_code),
        ],
        signal,
    )
    .await
    {
        Ok(credentials) => Ok(OAuthDeviceCodePollResult::Complete { value: credentials }),
        Err(error) => {
            let Some(response_error) = error.downcast_ref::<OAuthResponseError>() else {
                return Err(error);
            };
            match response_error.oauth_error.as_deref() {
                Some("authorization_pending") => Ok(OAuthDeviceCodePollResult::Pending),
                Some("slow_down") => Ok(OAuthDeviceCodePollResult::SlowDown {
                    interval_seconds: None,
                }),
                Some("expired_token") => Ok(OAuthDeviceCodePollResult::Failed {
                    message: "Device authorization expired.".to_owned(),
                }),
                Some("access_denied") => Ok(OAuthDeviceCodePollResult::Failed {
                    message: "Device authorization was denied.".to_owned(),
                }),
                _ => Err(error),
            }
        }
    }
}

async fn login_with_device_code(
    gateway: &str,
    interaction: &ProviderAuthInteraction,
) -> Result<OAuthCredential, Thrown> {
    let device = request_device_authorization(gateway, &interaction.signal).await?;
    interaction.notify(AuthEvent::DeviceCode {
        user_code: device.user_code.clone(),
        verification_uri: device.verification_uri.clone(),
        interval_seconds: device.interval,
        expires_in_seconds: Some(device.expires_in),
    });

    poll_oauth_device_code_flow(
        OAuthDeviceCodePollOptions {
            interval_seconds: device.interval,
            expires_in_seconds: Some(device.expires_in),
            wait_before_first_poll: false,
            signal: interaction.signal.clone(),
        },
        || poll_device_token(gateway, &device, &interaction.signal),
    )
    .await
}

/// Options of [`create_radius_oauth`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RadiusOAuthOptions {
    pub name: String,
    pub gateway: String,
}

struct RadiusOAuth {
    name: String,
    gateway: String,
}

impl OAuthAuth for RadiusOAuth {
    fn name(&self) -> &str {
        &self.name
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        _options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move {
            let login_method = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Select {
                    message: format!("Sign in to {}:", self.name),
                    options: vec![
                        AuthSelectOption::new(
                            LOGIN_METHOD_BROWSER,
                            "Sign in with browser (recommended)",
                        ),
                        AuthSelectOption::new(
                            LOGIN_METHOD_DEVICE_CODE,
                            "Sign in with device code (when signing in from another device)",
                        ),
                    ],
                }))
                .await?;

            if login_method == LOGIN_METHOD_DEVICE_CODE {
                return login_with_device_code(&self.gateway, &interaction).await;
            }
            if login_method == LOGIN_METHOD_BROWSER {
                let authorization_endpoint =
                    load_radius_oauth_discovery(&self.gateway, &interaction.signal).await?;
                return login_with_browser(&self.gateway, &authorization_endpoint, &interaction)
                    .await;
            }
            Err(js_error(format!(
                "Unknown {} sign-in method: {login_method}",
                self.name
            )))
        })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move {
            request_oauth_token(
                &self.gateway,
                &[
                    ("grant_type", "refresh_token"),
                    ("client_id", OAUTH_CLIENT_ID),
                    ("refresh_token", &credential.refresh),
                ],
                &signal,
            )
            .await
        })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move { Ok(api_key_auth(&credential.access)) })
    }
}

/// The Radius gateway OAuth flow for one gateway (`createRadiusOAuth`).
#[must_use]
pub fn create_radius_oauth(options: &RadiusOAuthOptions) -> Arc<dyn OAuthAuth> {
    Arc::new(RadiusOAuth {
        name: options.name.clone(),
        gateway: normalize_radius_gateway_url(&options.gateway),
    })
}

#[cfg(test)]
#[path = "radius_tests.rs"]
mod tests;
