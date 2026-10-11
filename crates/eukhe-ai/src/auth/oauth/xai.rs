//! xAI OAuth device-code flow. Port of `auth/oauth/xai.ts`.

use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use futures::future::BoxFuture;
use serde_json::{Map, Value};

use super::device_code::{
    poll_oauth_device_code_flow, OAuthDeviceCodePollOptions, OAuthDeviceCodePollResult,
};
use super::http::{fetch, FetchRequest};
use super::{api_key_auth, shared};
use crate::auth::errors::{date_now, js_error};
use crate::auth::types::{
    AuthEvent, LoginOptions, ModelAuth, OAuthAuth, OAuthCredential, ProviderAuthInteraction,
};
use crate::utils::diagnostics::Thrown;

const XAI_CLIENT_ID: &str = "b1a00492-073a-47ea-816f-4c329264a828";
const XAI_SCOPE: &str = "openid profile email offline_access grok-cli:access api:access";
const XAI_DEVICE_CODE_URL: &str = "https://auth.x.ai/oauth2/device/code";
const XAI_TOKEN_URL: &str = "https://auth.x.ai/oauth2/token";
/// Refresh slightly before the reported expiry to avoid using a token that dies mid-request.
const REFRESH_SKEW_MS: f64 = 5.0 * 60.0 * 1000.0;
const DEFAULT_TOKEN_LIFETIME_SECONDS: f64 = 3600.0;

struct OAuthHttpResponse {
    ok: bool,
    status: u16,
    body: Map<String, Value>,
}

struct XaiDeviceCode {
    device_code: String,
    user_code: String,
    verification_uri: String,
    verification_uri_complete: Option<String>,
    interval_seconds: Option<f64>,
    expires_in_seconds: f64,
}

fn required_string(body: &Map<String, Value>, field: &str) -> Result<String, Thrown> {
    match body.get(field) {
        Some(Value::String(value)) if !value.is_empty() => Ok(value.clone()),
        _ => Err(js_error(format!(
            "Invalid xAI OAuth response field: {field}"
        ))),
    }
}

fn positive_number(body: &Map<String, Value>, field: &str) -> Result<f64, Thrown> {
    body.get(field)
        .and_then(Value::as_f64)
        .filter(|value| value.is_finite() && *value > 0.0)
        .ok_or_else(|| js_error(format!("Invalid xAI OAuth response field: {field}")))
}

/// The verification URI is opened in the user's browser; force it to be an
/// https URL so a malicious response cannot make `open` launch something else.
fn validate_verification_uri(raw: &str) -> Result<String, Thrown> {
    let untrusted = || js_error("Untrusted verification URI in xAI OAuth response");
    let url = url::Url::parse(raw).map_err(|_| untrusted())?;
    if url.scheme() != "https" {
        return Err(untrusted());
    }
    Ok(url.to_string())
}

async fn post_form(
    url: &str,
    fields: &[(&str, &str)],
    signal: &AbortSignal,
) -> Result<OAuthHttpResponse, Thrown> {
    let response = fetch(
        FetchRequest::post(url)
            .header("Accept", "application/json")
            .header("Content-Type", "application/x-www-form-urlencoded")
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

    let body = match response.json() {
        Ok(Value::Object(body)) => body,
        Ok(_) => Map::new(),
        Err(_) => {
            if signal.aborted() {
                return Err(js_error("Login cancelled"));
            }
            return Err(js_error(format!(
                "xAI OAuth returned invalid JSON (HTTP {})",
                response.status
            )));
        }
    };
    Ok(OAuthHttpResponse {
        ok: response.ok(),
        status: response.status,
        body,
    })
}

fn request_failure(action: &str, response: &OAuthHttpResponse) -> Thrown {
    let parts: Vec<&str> = ["error", "error_description"]
        .iter()
        .filter_map(|field| response.body.get(*field).and_then(Value::as_str))
        .filter(|value| !value.is_empty())
        .collect();
    let detail = parts.join(": ");
    let suffix = if detail.is_empty() {
        String::new()
    } else {
        format!(": {detail}")
    };
    js_error(format!(
        "xAI OAuth {action} failed (HTTP {}){suffix}",
        response.status
    ))
}

fn parse_device_code(body: &Map<String, Value>) -> Result<XaiDeviceCode, Thrown> {
    // RFC 8628 allows interval 0 (no minimum wait); fall back to the poller's
    // default instead of failing on non-positive or malformed values.
    let interval_seconds = body
        .get("interval")
        .and_then(Value::as_f64)
        .filter(|interval| interval.is_finite() && *interval > 0.0);
    let verification_uri_complete = match body.get("verification_uri_complete") {
        Some(Value::String(uri)) if !uri.is_empty() => Some(validate_verification_uri(uri)?),
        _ => None,
    };
    Ok(XaiDeviceCode {
        device_code: required_string(body, "device_code")?,
        user_code: required_string(body, "user_code")?,
        verification_uri: validate_verification_uri(&required_string(body, "verification_uri")?)?,
        verification_uri_complete,
        interval_seconds,
        expires_in_seconds: positive_number(body, "expires_in")?,
    })
}

fn credentials_from_token_response(
    body: &Map<String, Value>,
    previous_refresh_token: Option<&str>,
) -> Result<OAuthCredential, Thrown> {
    let access = required_string(body, "access_token")?;
    // xAI may omit refresh_token on refresh when the token is not rotated.
    let refresh = match previous_refresh_token {
        Some(previous) if !body.contains_key("refresh_token") && !previous.is_empty() => {
            previous.to_owned()
        }
        _ => required_string(body, "refresh_token")?,
    };
    let expires_in_seconds = if body.contains_key("expires_in") {
        positive_number(body, "expires_in")?
    } else {
        DEFAULT_TOKEN_LIFETIME_SECONDS
    };
    Ok(OAuthCredential::new(
        refresh,
        access,
        date_now() + expires_in_seconds * 1000.0 - REFRESH_SKEW_MS,
    ))
}

async fn request_device_code(signal: &AbortSignal) -> Result<XaiDeviceCode, Thrown> {
    let response = post_form(
        XAI_DEVICE_CODE_URL,
        &[
            ("client_id", XAI_CLIENT_ID),
            ("scope", XAI_SCOPE),
            ("referrer", "pi"),
        ],
        signal,
    )
    .await?;
    if !response.ok {
        return Err(request_failure("device authorization", &response));
    }
    parse_device_code(&response.body)
}

async fn poll_once(
    device: &XaiDeviceCode,
    signal: &AbortSignal,
) -> Result<OAuthDeviceCodePollResult<OAuthCredential>, Thrown> {
    let response = post_form(
        XAI_TOKEN_URL,
        &[
            ("grant_type", "urn:ietf:params:oauth:grant-type:device_code"),
            ("client_id", XAI_CLIENT_ID),
            ("device_code", &device.device_code),
        ],
        signal,
    )
    .await?;

    if response.ok {
        return Ok(OAuthDeviceCodePollResult::Complete {
            value: credentials_from_token_response(&response.body, None)?,
        });
    }

    Ok(match response.body.get("error").and_then(Value::as_str) {
        Some("authorization_pending") => OAuthDeviceCodePollResult::Pending,
        Some("slow_down") => OAuthDeviceCodePollResult::SlowDown {
            interval_seconds: response.body.get("interval").and_then(Value::as_f64),
        },
        Some("access_denied" | "authorization_denied") => OAuthDeviceCodePollResult::Failed {
            message: "xAI device authorization was denied".to_owned(),
        },
        Some("expired_token") => OAuthDeviceCodePollResult::Failed {
            message: "xAI device code expired".to_owned(),
        },
        _ => OAuthDeviceCodePollResult::Failed {
            message: request_failure("device token polling", &response).to_string(),
        },
    })
}

async fn poll_for_tokens(
    device: &XaiDeviceCode,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    poll_oauth_device_code_flow(
        OAuthDeviceCodePollOptions {
            interval_seconds: device.interval_seconds,
            expires_in_seconds: Some(device.expires_in_seconds),
            wait_before_first_poll: true,
            signal: signal.clone(),
        },
        || poll_once(device, signal),
    )
    .await
}

async fn login_xai(interaction: &ProviderAuthInteraction) -> Result<OAuthCredential, Thrown> {
    let device = request_device_code(&interaction.signal).await?;
    interaction.notify(AuthEvent::DeviceCode {
        user_code: device.user_code.clone(),
        verification_uri: device
            .verification_uri_complete
            .clone()
            .unwrap_or_else(|| device.verification_uri.clone()),
        interval_seconds: device.interval_seconds,
        expires_in_seconds: Some(device.expires_in_seconds),
    });
    poll_for_tokens(&device, &interaction.signal).await
}

async fn refresh_xai_token(
    refresh_token: &str,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    let response = post_form(
        XAI_TOKEN_URL,
        &[
            ("grant_type", "refresh_token"),
            ("client_id", XAI_CLIENT_ID),
            ("refresh_token", refresh_token),
        ],
        signal,
    )
    .await?;
    if !response.ok {
        return Err(request_failure("token refresh", &response));
    }
    credentials_from_token_response(&response.body, Some(refresh_token))
}

struct XaiOAuth;

impl OAuthAuth for XaiOAuth {
    fn name(&self) -> &'static str {
        "xAI (Grok/X subscription)"
    }

    fn is_subscription(&self) -> Option<bool> {
        Some(true)
    }

    fn login_label(&self) -> Option<&'static str> {
        Some("Sign in with SuperGrok or X Premium")
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        _options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { login_xai(&interaction).await })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { refresh_xai_token(&credential.refresh, &signal).await })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move { Ok(api_key_auth(&credential.access)) })
    }
}

/// The xAI (Grok/X subscription) OAuth flow (`xaiOAuth`).
#[must_use]
pub fn xai_oauth() -> Arc<dyn OAuthAuth> {
    shared(XaiOAuth)
}

#[cfg(test)]
#[path = "xai_tests.rs"]
mod tests;
