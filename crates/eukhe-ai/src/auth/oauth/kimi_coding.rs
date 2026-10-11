//! Kimi Code (subscription) OAuth flow. Port of `auth/oauth/kimi-coding.ts`.
//!
//! RFC 8628 device authorization grant against <https://auth.kimi.com> with
//! JSON responses. The access token authenticates requests to
//! <https://api.kimi.com/coding> as an `Authorization: Bearer` header.

use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::ProviderHeaders;
use futures::future::BoxFuture;
use serde_json::Value;

use super::device_code::{
    poll_oauth_device_code_flow, OAuthDeviceCodePollOptions, OAuthDeviceCodePollResult,
};
use super::http::{fetch, FetchRequest, FetchResponse};
use super::{positive_number, shared, string_field, trusted_http_url};
use crate::auth::errors::{date_now, js_error, timeout_signal};
use crate::auth::types::{
    AuthEvent, LoginOptions, ModelAuth, OAuthAuth, OAuthCredential, ProviderAuthInteraction,
};
use crate::utils::diagnostics::Thrown;
use crate::utils::provider_env::get_provider_env_value;
use crate::utils::sleep::sleep;

const CLIENT_ID: &str = "17e5f671-d194-4dfb-9706-5516cb48c098";
const DEFAULT_OAUTH_HOST: &str = "https://auth.kimi.com";
const DEVICE_CODE_TIMEOUT_SECONDS: f64 = 15.0 * 60.0;
const DEFAULT_POLL_INTERVAL_SECONDS: f64 = 5.0;
const REQUEST_TIMEOUT_MS: u64 = 30 * 1000;
const REFRESH_MAX_RETRIES: u32 = 3;

struct DeviceAuthorization {
    device_code: String,
    user_code: String,
    verification_uri_complete: String,
    interval_seconds: f64,
    expires_in_seconds: f64,
}

struct TokenResponse {
    access: String,
    refresh: String,
    expires: f64,
}

fn get_oauth_host() -> String {
    let host = get_provider_env_value("KIMI_CODE_OAUTH_HOST", None)
        .or_else(|| get_provider_env_value("KIMI_OAUTH_HOST", None))
        .unwrap_or_else(|| DEFAULT_OAUTH_HOST.to_owned());
    host.trim_end_matches('/').to_owned()
}

fn request_signal(signal: &AbortSignal) -> AbortSignal {
    AbortSignal::any(&[timeout_signal(REQUEST_TIMEOUT_MS), signal.clone()])
}

/// The body as a JSON object/array, else `Null`.
fn read_json(response: &FetchResponse) -> Value {
    match response.json() {
        Ok(json @ (Value::Object(_) | Value::Array(_))) => json,
        _ => Value::Null,
    }
}

fn form_request(url: String, fields: &[(&str, &str)]) -> FetchRequest {
    FetchRequest::post(url)
        .header("Content-Type", "application/x-www-form-urlencoded")
        .header("Accept", "application/json")
        .form(fields)
}

fn text_suffix(text: &str) -> String {
    if text.is_empty() {
        String::new()
    } else {
        format!(": {text}")
    }
}

async fn start_device_authorization(
    oauth_host: &str,
    signal: &AbortSignal,
) -> Result<DeviceAuthorization, Thrown> {
    let response = fetch(
        form_request(
            format!("{oauth_host}/api/oauth/device_authorization"),
            &[("client_id", CLIENT_ID)],
        ),
        Some(&request_signal(signal)),
    )
    .await?;

    if !response.ok() {
        return Err(js_error(format!(
            "Kimi Code device authorization failed with status {}{}",
            response.status,
            text_suffix(&response.body)
        )));
    }

    let json = read_json(&response);
    let parsed = match (
        string_field(&json, "device_code"),
        string_field(&json, "user_code"),
        string_field(&json, "verification_uri"),
        string_field(&json, "verification_uri_complete"),
    ) {
        (Some(device_code), Some(user_code), Some(_), Some(complete))
            if trusted_http_url(json.get("verification_uri_complete")).is_some()
                && trusted_http_url(json.get("verification_uri")).is_some() =>
        {
            Some((device_code, user_code, complete))
        }
        _ => None,
    };
    let Some((device_code, user_code, verification_uri_complete)) = parsed else {
        return Err(js_error(format!(
            "Invalid Kimi Code device authorization response: {json}"
        )));
    };

    Ok(DeviceAuthorization {
        device_code: device_code.to_owned(),
        user_code: user_code.to_owned(),
        verification_uri_complete: verification_uri_complete.to_owned(),
        interval_seconds: positive_number(&json, "interval")
            .unwrap_or(DEFAULT_POLL_INTERVAL_SECONDS),
        expires_in_seconds: positive_number(&json, "expires_in")
            .unwrap_or(DEVICE_CODE_TIMEOUT_SECONDS),
    })
}

fn parse_token_response(json: &Value, operation: &str) -> Result<TokenResponse, Thrown> {
    match (
        super::truthy_str(json, "access_token"),
        super::truthy_str(json, "refresh_token"),
        positive_number(json, "expires_in"),
    ) {
        (Some(access), Some(refresh), Some(expires_in)) => Ok(TokenResponse {
            access: access.to_owned(),
            refresh: refresh.to_owned(),
            expires: date_now() + expires_in * 1000.0,
        }),
        _ => Err(js_error(format!(
            "Kimi Code token {operation} response missing fields: {json}"
        ))),
    }
}

async fn poll_once(
    oauth_host: &str,
    device: &DeviceAuthorization,
    signal: &AbortSignal,
) -> Result<OAuthDeviceCodePollResult<TokenResponse>, Thrown> {
    let response = fetch(
        form_request(
            format!("{oauth_host}/api/oauth/token"),
            &[
                ("client_id", CLIENT_ID),
                ("device_code", &device.device_code),
                ("grant_type", "urn:ietf:params:oauth:grant-type:device_code"),
            ],
        ),
        Some(&request_signal(signal)),
    )
    .await?;

    if response.status >= 500 {
        return Ok(OAuthDeviceCodePollResult::Failed {
            message: format!(
                "Kimi Code device token request failed with status {}{}",
                response.status,
                text_suffix(&response.body)
            ),
        });
    }

    let json = read_json(&response);
    if response.ok() && string_field(&json, "access_token").is_some() {
        return Ok(match parse_token_response(&json, "poll") {
            Ok(value) => OAuthDeviceCodePollResult::Complete { value },
            Err(error) => OAuthDeviceCodePollResult::Failed {
                message: error.to_string(),
            },
        });
    }

    let error = json.get("error");
    let description = string_field(&json, "error_description")
        .map(|description| format!(": {description}"))
        .unwrap_or_default();
    Ok(match error.and_then(Value::as_str) {
        Some("authorization_pending") => OAuthDeviceCodePollResult::Pending,
        Some("slow_down") => OAuthDeviceCodePollResult::SlowDown {
            interval_seconds: json
                .get("interval")
                .and_then(Value::as_f64)
                .filter(|interval| *interval > 0.0),
        },
        Some("expired_token") => OAuthDeviceCodePollResult::Failed {
            message: "Kimi Code device authorization expired. Please restart login.".to_owned(),
        },
        Some("access_denied") => OAuthDeviceCodePollResult::Failed {
            message: "Kimi Code login was denied.".to_owned(),
        },
        other => OAuthDeviceCodePollResult::Failed {
            message: format!(
                "Kimi Code device token request failed (status {}){}",
                response.status,
                other
                    .map(|error| format!(": {error}{description}"))
                    .unwrap_or_default()
            ),
        },
    })
}

async fn poll_for_token(
    oauth_host: &str,
    device: &DeviceAuthorization,
    signal: &AbortSignal,
) -> Result<TokenResponse, Thrown> {
    poll_oauth_device_code_flow(
        OAuthDeviceCodePollOptions {
            interval_seconds: Some(device.interval_seconds),
            expires_in_seconds: Some(device.expires_in_seconds),
            wait_before_first_poll: true,
            signal: signal.clone(),
        },
        || poll_once(oauth_host, device, signal),
    )
    .await
}

fn is_retryable_refresh_failure(response: &FetchResponse) -> bool {
    response.status == 429 || response.status >= 500
}

async fn refresh_token(
    oauth_host: &str,
    refresh_token_value: &str,
    signal: &AbortSignal,
) -> Result<TokenResponse, Thrown> {
    let mut last_error: Option<Thrown> = None;
    for attempt in 0..=REFRESH_MAX_RETRIES {
        if attempt > 0 {
            sleep(1000.0 * f64::from(1_u32 << (attempt - 1)), signal).await?;
        }
        if signal.aborted() {
            return Err(js_error("Kimi Code token refresh aborted"));
        }

        let response = match fetch(
            form_request(
                format!("{oauth_host}/api/oauth/token"),
                &[
                    ("client_id", CLIENT_ID),
                    ("grant_type", "refresh_token"),
                    ("refresh_token", refresh_token_value),
                ],
            ),
            Some(&request_signal(signal)),
        )
        .await
        {
            Ok(response) => response,
            Err(error) => {
                last_error = Some(error);
                continue;
            }
        };

        let json = read_json(&response);
        if response.ok() {
            return parse_token_response(&json, "refresh");
        }

        // Unauthorized: the stored credential is dead; Models clears it and prompts re-login.
        if response.status == 401
            || response.status == 403
            || json.get("error").and_then(Value::as_str) == Some("invalid_grant")
        {
            let description = string_field(&json, "error_description")
                .map(|description| format!(": {description}"))
                .unwrap_or_default();
            return Err(js_error(format!(
                "Kimi Code token refresh unauthorized (status {}){description}",
                response.status
            )));
        }

        if is_retryable_refresh_failure(&response) && attempt < REFRESH_MAX_RETRIES {
            last_error = Some(js_error(format!(
                "Kimi Code token refresh failed with status {}",
                response.status
            )));
            continue;
        }

        return Err(js_error(format!(
            "Kimi Code token refresh failed with status {}: {json}",
            response.status
        )));
    }

    Err(last_error.unwrap_or_else(|| js_error("Kimi Code token refresh failed")))
}

async fn login_kimi_coding(
    interaction: &ProviderAuthInteraction,
) -> Result<OAuthCredential, Thrown> {
    let oauth_host = get_oauth_host();
    let device = start_device_authorization(&oauth_host, &interaction.signal).await?;
    interaction.notify(AuthEvent::DeviceCode {
        user_code: device.user_code.clone(),
        verification_uri: device.verification_uri_complete.clone(),
        interval_seconds: Some(device.interval_seconds),
        expires_in_seconds: Some(device.expires_in_seconds),
    });
    let token = poll_for_token(&oauth_host, &device, &interaction.signal).await?;
    Ok(OAuthCredential::new(
        token.refresh,
        token.access,
        token.expires,
    ))
}

struct KimiCodingOAuth;

impl OAuthAuth for KimiCodingOAuth {
    fn name(&self) -> &'static str {
        "Kimi Code (subscription)"
    }

    fn is_subscription(&self) -> Option<bool> {
        Some(true)
    }

    fn login_label(&self) -> Option<&'static str> {
        Some("Sign in with Kimi Code")
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        _options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { login_kimi_coding(&interaction).await })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move {
            let token = refresh_token(&get_oauth_host(), &credential.refresh, &signal).await?;
            Ok(OAuthCredential::new(
                token.refresh,
                token.access,
                token.expires,
            ))
        })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move {
            let mut headers = ProviderHeaders::new();
            headers.insert(
                "Authorization".to_owned(),
                Some(format!("Bearer {}", credential.access)),
            );
            Ok(ModelAuth {
                headers: Some(headers),
                ..ModelAuth::default()
            })
        })
    }
}

/// The Kimi Code (subscription) OAuth flow (`kimiCodingOAuth`).
#[must_use]
pub fn kimi_coding_oauth() -> Arc<dyn OAuthAuth> {
    shared(KimiCodingOAuth)
}

#[cfg(test)]
#[path = "kimi_coding_tests.rs"]
mod tests;
