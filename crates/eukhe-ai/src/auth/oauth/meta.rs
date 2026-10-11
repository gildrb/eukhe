//! Meta Model API OAuth flow. Port of `auth/oauth/meta.ts`.
//!
//! RFC 8628 device authorization grant against <https://auth.meta.com> (JSON
//! responses). Meta splits identity from API access: the resulting identity
//! token is not accepted for inference, so it is exchanged for a Model API
//! key via the Muse Code key-mint endpoint (minted keys live about a day).
//! The identity token is stored as `refresh` and the minted key as `access`,
//! so the standard OAuth scheduler re-mints the key when it expires. The
//! identity token itself is not renewable, so a 401/403 from mint means the
//! session is dead and the user must sign in again.

use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use futures::future::BoxFuture;
use serde_json::Value;

use super::device_code::{
    poll_oauth_device_code_flow, OAuthDeviceCodePollOptions, OAuthDeviceCodePollResult,
};
use super::http::{fetch, FetchRequest, FetchResponse};
use super::{api_key_auth, positive_number, shared, trusted_http_url};
use crate::auth::errors::{date_now, js_error, timeout_signal};
use crate::auth::types::{
    AuthEvent, LoginOptions, ModelAuth, OAuthAuth, OAuthCredential, ProviderAuthInteraction,
};
use crate::utils::diagnostics::Thrown;

/// Muse Code CLI client id.
const CLIENT_ID: &str = "1031625952748946";
const DEVICE_AUTHORIZATION_URL: &str = "https://auth.meta.com/oidc/device/authorization/";
const DEVICE_TOKEN_URL: &str = "https://auth.meta.com/oidc/device/token/";
const API_KEY_MINT_URL: &str = "https://api.meta.ai/muse-code/key";
const API_KEY_LIFETIME_MS: f64 = 24.0 * 60.0 * 60.0 * 1000.0;
const REQUEST_TIMEOUT_MS: u64 = 30 * 1000;

struct DeviceAuthorization {
    device_code: String,
    user_code: String,
    verification_uri: String,
    interval_seconds: Option<f64>,
    expires_in_seconds: Option<f64>,
}

fn request_signal(signal: &AbortSignal) -> AbortSignal {
    AbortSignal::any(&[timeout_signal(REQUEST_TIMEOUT_MS), signal.clone()])
}

/// The body as a JSON object/array, else `Null` (TS `readJson`).
fn read_json(response: &FetchResponse) -> Value {
    match response.json() {
        Ok(json @ (Value::Object(_) | Value::Array(_))) => json,
        _ => Value::Null,
    }
}

fn error_detail(json: &Value) -> String {
    for key in ["error_description", "detail", "message", "error"] {
        if let Some(value) = json.get(key).and_then(Value::as_str) {
            if !value.trim().is_empty() {
                return format!(": {}", value.trim());
            }
        }
    }
    String::new()
}

async fn post(request: FetchRequest, signal: &AbortSignal) -> Result<FetchResponse, Thrown> {
    fetch(request, Some(&request_signal(signal))).await
}

async fn start_device_authorization(signal: &AbortSignal) -> Result<DeviceAuthorization, Thrown> {
    let response = post(
        FetchRequest::post(DEVICE_AUTHORIZATION_URL)
            .header("Content-Type", "application/x-www-form-urlencoded")
            .header("Accept", "application/json")
            .form(&[("client_id", CLIENT_ID)]),
        signal,
    )
    .await?;
    let json = read_json(&response);
    if !response.ok() {
        return Err(js_error(format!(
            "Meta device authorization failed with status {}{}",
            response.status,
            error_detail(&json)
        )));
    }
    let verification_uri = trusted_http_url(json.get("verification_uri_complete"))
        .or_else(|| trusted_http_url(json.get("verification_uri")));
    match (
        super::truthy_str(&json, "device_code"),
        super::truthy_str(&json, "user_code"),
        verification_uri,
    ) {
        (Some(device_code), Some(user_code), Some(verification_uri)) => Ok(DeviceAuthorization {
            device_code: device_code.to_owned(),
            user_code: user_code.to_owned(),
            verification_uri,
            interval_seconds: positive_number(&json, "interval"),
            expires_in_seconds: positive_number(&json, "expires_in"),
        }),
        _ => Err(js_error(format!(
            "Invalid Meta device authorization response: {json}"
        ))),
    }
}

async fn poll_once(
    device: &DeviceAuthorization,
    signal: &AbortSignal,
) -> Result<OAuthDeviceCodePollResult<String>, Thrown> {
    let response = post(
        FetchRequest::post(DEVICE_TOKEN_URL)
            .header("Content-Type", "application/x-www-form-urlencoded")
            .header("Accept", "application/json")
            .form(&[
                ("grant_type", "urn:ietf:params:oauth:grant-type:device_code"),
                ("device_code", &device.device_code),
                ("client_id", CLIENT_ID),
            ]),
        signal,
    )
    .await?;
    let json = read_json(&response);
    if response.ok() {
        if let Some(access_token) = super::truthy_str(&json, "access_token") {
            return Ok(OAuthDeviceCodePollResult::Complete {
                value: access_token.to_owned(),
            });
        }
    }
    Ok(match json.get("error").and_then(Value::as_str) {
        Some("authorization_pending") => OAuthDeviceCodePollResult::Pending,
        Some("slow_down") => OAuthDeviceCodePollResult::SlowDown {
            interval_seconds: positive_number(&json, "interval"),
        },
        Some("access_denied") => OAuthDeviceCodePollResult::Failed {
            message: "Meta login was denied.".to_owned(),
        },
        Some("expired_token") => OAuthDeviceCodePollResult::Failed {
            message: "Meta device authorization expired. Please restart login.".to_owned(),
        },
        _ => OAuthDeviceCodePollResult::Failed {
            message: format!(
                "Meta device token request failed with status {}{}",
                response.status,
                error_detail(&json)
            ),
        },
    })
}

async fn poll_for_identity_token(
    device: &DeviceAuthorization,
    signal: &AbortSignal,
) -> Result<String, Thrown> {
    poll_oauth_device_code_flow(
        OAuthDeviceCodePollOptions {
            interval_seconds: device.interval_seconds,
            expires_in_seconds: device.expires_in_seconds,
            wait_before_first_poll: true,
            signal: signal.clone(),
        },
        || poll_once(device, signal),
    )
    .await
}

/// Exchange an identity token for a Model API key. Keys are valid for about a day.
async fn mint_api_key(
    identity_token: &str,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    let response = post(
        FetchRequest::post(API_KEY_MINT_URL)
            .header("Accept", "application/json")
            .header("Authorization", format!("Bearer {identity_token}"))
            .header("Content-Type", "application/json")
            .header("x-api-version", "1.0.0")
            .body("{}"),
        signal,
    )
    .await?;
    let json = read_json(&response);
    if response.status == 401 || response.status == 403 {
        // Identity token is not renewable (see module docs); only a fresh device flow helps.
        return Err(js_error(format!(
            "Meta session expired (status {}). Run `/login meta` to sign in again.{}",
            response.status,
            error_detail(&json)
        )));
    }
    if !response.ok() {
        return Err(js_error(format!(
            "Meta API key mint failed with status {}{}",
            response.status,
            error_detail(&json)
        )));
    }
    let Some(api_key) = super::truthy_str(&json, "api_key") else {
        let setup = trusted_http_url(json.get("action_url"))
            .map(|url| format!(" Complete setup at {url}"))
            .unwrap_or_default();
        return Err(js_error(format!("Meta did not issue an API key.{setup}")));
    };
    Ok(OAuthCredential::new(
        identity_token,
        api_key,
        date_now() + API_KEY_LIFETIME_MS,
    ))
}

async fn login_meta(interaction: &ProviderAuthInteraction) -> Result<OAuthCredential, Thrown> {
    let result = async {
        let device = start_device_authorization(&interaction.signal).await?;
        interaction.notify(AuthEvent::DeviceCode {
            user_code: device.user_code.clone(),
            verification_uri: device.verification_uri.clone(),
            interval_seconds: device.interval_seconds,
            expires_in_seconds: device.expires_in_seconds,
        });
        let identity_token = poll_for_identity_token(&device, &interaction.signal).await?;
        interaction.notify(AuthEvent::Progress {
            message: "Enabling Meta Model API access...".to_owned(),
        });
        mint_api_key(&identity_token, &interaction.signal).await
    }
    .await;
    // An in-flight fetch fails with the abort reason; the login UI matches on this message.
    result.map_err(|error| {
        if interaction.signal.aborted() {
            js_error("Login cancelled")
        } else {
            error
        }
    })
}

struct MetaOAuth;

impl OAuthAuth for MetaOAuth {
    fn name(&self) -> &'static str {
        "Meta (Muse subscription)"
    }

    fn is_subscription(&self) -> Option<bool> {
        Some(true)
    }

    fn login_label(&self) -> Option<&'static str> {
        Some("Sign in with Meta")
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        _options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { login_meta(&interaction).await })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { mint_api_key(&credential.refresh, &signal).await })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move { Ok(api_key_auth(&credential.access)) })
    }
}

/// The Meta (Muse subscription) OAuth flow (`metaOAuth`).
#[must_use]
pub fn meta_oauth() -> Arc<dyn OAuthAuth> {
    shared(MetaOAuth)
}

#[cfg(test)]
#[path = "meta_tests.rs"]
mod tests;
