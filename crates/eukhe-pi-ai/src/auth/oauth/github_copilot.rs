//! `GitHub` Copilot OAuth flow. Port of `auth/oauth/github-copilot.ts`.

use std::sync::{Arc, LazyLock};
use std::time::Duration;

use base64::Engine as _;
use eukhe_chord::context::AbortSignal;
use futures::future::BoxFuture;
use serde_json::Value;
use tokio::time::Instant;

use super::device_code::{
    poll_oauth_device_code_flow, OAuthDeviceCodePollOptions, OAuthDeviceCodePollResult,
};
use super::http::{fetch, FetchRequest, FetchResponse};
use super::{shared, string_field};
use crate::auth::errors::{js_error, timeout_signal};
use crate::auth::types::{
    AuthEvent, AuthPrompt, AuthPromptKind, LoginOptions, ModelAuth, OAuthAuth, OAuthCredential,
    ProviderAuthInteraction,
};
use crate::providers::github_copilot_models::GITHUB_COPILOT_MODELS;
use crate::utils::diagnostics::Thrown;
use crate::utils::sleep::sleep;

static CLIENT_ID: LazyLock<String> = LazyLock::new(|| {
    let bytes = base64::engine::general_purpose::STANDARD
        .decode("SXYxLmI1MDdhMDhjODdlY2ZlOTg=")
        .unwrap_or_default();
    String::from_utf8(bytes).unwrap_or_default()
});

const COPILOT_HEADERS: [(&str, &str); 4] = [
    ("User-Agent", "GitHubCopilotChat/0.35.0"),
    ("Editor-Version", "vscode/1.107.0"),
    ("Editor-Plugin-Version", "copilot-chat/0.35.0"),
    ("Copilot-Integration-Id", "vscode-chat"),
];
const COPILOT_API_VERSION: &str = "2026-06-01";
const INDIVIDUAL_BASE_URL: &str = "https://api.individual.githubcopilot.com";

struct DeviceCodeResponse {
    device_code: String,
    user_code: String,
    verification_uri: String,
    interval: Option<f64>,
    expires_in: f64,
}

#[derive(Clone, Copy)]
struct RetryPolicy {
    max_retries: u32,
    max_elapsed_ms: u64,
}

fn normalize_domain(input: &str) -> Option<String> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return None;
    }
    let candidate = if trimmed.contains("://") {
        trimmed.to_owned()
    } else {
        format!("https://{trimmed}")
    };
    url::Url::parse(&candidate)
        .ok()
        .and_then(|url| url.host_str().map(str::to_owned))
}

struct Urls {
    device_code: String,
    access_token: String,
    copilot_token: String,
}

fn get_urls(domain: &str) -> Urls {
    Urls {
        device_code: format!("https://{domain}/login/device/code"),
        access_token: format!("https://{domain}/login/oauth/access_token"),
        copilot_token: format!("https://api.{domain}/copilot_internal/v2/token"),
    }
}

/// Parse the proxy-ep from a Copilot token and convert to API base URL.
/// Token format: `tid=...;exp=...;proxy-ep=proxy.individual.githubcopilot.com;...`
/// Returns an API URL like `https://api.individual.githubcopilot.com`.
fn get_base_url_from_token(token: &str) -> Option<String> {
    let start = token.find("proxy-ep=")? + "proxy-ep=".len();
    let proxy_host = token[start..]
        .split(';')
        .next()
        .filter(|host| !host.is_empty())?;
    let api_host = proxy_host
        .strip_prefix("proxy.")
        .map_or_else(|| proxy_host.to_owned(), |rest| format!("api.{rest}"));
    Some(format!("https://{api_host}"))
}

fn get_github_copilot_base_url(token: Option<&str>, enterprise_domain: Option<&str>) -> String {
    // If we have a token, extract the base URL from proxy-ep.
    if let Some(url) = token
        .filter(|token| !token.is_empty())
        .and_then(get_base_url_from_token)
    {
        return url;
    }
    // Fallback for enterprise or if token parsing fails.
    match enterprise_domain.filter(|domain| !domain.is_empty()) {
        Some(domain) => format!("https://copilot-api.{domain}"),
        None => INDIVIDUAL_BASE_URL.to_owned(),
    }
}

struct ModelCatalog {
    available_model_ids: Vec<String>,
    policy_model_ids: Vec<String>,
}

struct AccountModel {
    id: String,
    picker_enabled: bool,
    policy_state: Option<Value>,
}

fn parse_github_copilot_model_catalog(
    raw: &Value,
    allow_policy_fallback: bool,
) -> Result<ModelCatalog, Thrown> {
    let Some(data) = raw.get("data").and_then(Value::as_array) else {
        return Err(js_error("Invalid Copilot models response"));
    };

    let account_models: Vec<AccountModel> = data
        .iter()
        .filter_map(|item| {
            let id = item.get("id")?.as_str()?;
            let supports = item
                .get("capabilities")
                .and_then(|capabilities| capabilities.get("supports"));
            if supports.and_then(|supports| supports.get("tool_calls")) == Some(&Value::Bool(false))
            {
                return None;
            }
            Some(AccountModel {
                id: id.to_owned(),
                picker_enabled: item.get("model_picker_enabled") == Some(&Value::Bool(true)),
                policy_state: item
                    .get("policy")
                    .and_then(|policy| policy.get("state"))
                    .cloned(),
            })
        })
        .collect();
    let state_is = |model: &AccountModel, state: &str| {
        model.policy_state.as_ref().and_then(Value::as_str) == Some(state)
    };

    let picker_model_ids: Vec<String> = account_models
        .iter()
        .filter(|model| model.picker_enabled && !state_is(model, "disabled"))
        .map(|model| model.id.clone())
        .collect();
    let use_policy_fallback = allow_policy_fallback && picker_model_ids.is_empty();
    let available_model_ids = if !picker_model_ids.is_empty() || !allow_policy_fallback {
        picker_model_ids
    } else {
        account_models
            .iter()
            .filter(|model| state_is(model, "enabled"))
            .map(|model| model.id.clone())
            .collect()
    };
    let policy_model_ids = account_models
        .iter()
        .filter(|model| {
            state_is(model, "unconfigured")
                && GITHUB_COPILOT_MODELS.contains_key(&model.id)
                && (model.picker_enabled || use_policy_fallback)
        })
        .map(|model| model.id.clone())
        .collect();
    Ok(ModelCatalog {
        available_model_ids,
        policy_model_ids,
    })
}

/// JS `Number.parseFloat`: the longest numeric prefix after leading
/// whitespace, else NaN.
fn js_parse_float(value: &str) -> f64 {
    let text = value.trim_start();
    let bytes = text.as_bytes();
    let mut end = 0;
    if matches!(bytes.first(), Some(b'+' | b'-')) {
        end = 1;
    }
    if text[end..].starts_with("Infinity") {
        let sign = if bytes.first() == Some(&b'-') {
            -1.0
        } else {
            1.0
        };
        return sign * f64::INFINITY;
    }
    let digits_start = end;
    while bytes.get(end).is_some_and(u8::is_ascii_digit) {
        end += 1;
    }
    let mut mantissa_digits = end - digits_start;
    if bytes.get(end) == Some(&b'.') {
        let mut fraction_end = end + 1;
        while bytes.get(fraction_end).is_some_and(u8::is_ascii_digit) {
            fraction_end += 1;
        }
        mantissa_digits += fraction_end - end - 1;
        if mantissa_digits > 0 {
            end = fraction_end;
        }
    }
    if mantissa_digits == 0 {
        return f64::NAN;
    }
    if matches!(bytes.get(end), Some(b'e' | b'E')) {
        let mut exponent_end = end + 1;
        if matches!(bytes.get(exponent_end), Some(b'+' | b'-')) {
            exponent_end += 1;
        }
        let exponent_digits_start = exponent_end;
        while bytes.get(exponent_end).is_some_and(u8::is_ascii_digit) {
            exponent_end += 1;
        }
        if exponent_end > exponent_digits_start {
            end = exponent_end;
        }
    }
    text[..end].parse().unwrap_or(f64::NAN)
}

/// JS `Date.parse` for the HTTP-date (IMF-fixdate) form of `Retry-After`,
/// e.g. `Sun, 06 Nov 1994 08:49:37 GMT`; NaN for anything else.
fn parse_http_date_ms(value: &str) -> f64 {
    const MONTHS: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    let parts: Vec<&str> = value.split_whitespace().collect();
    let [_, day, month, year, time, "GMT"] = parts.as_slice() else {
        return f64::NAN;
    };
    let (Ok(day), Some(month), Ok(year)) = (
        day.parse::<i64>(),
        MONTHS.iter().position(|name| name == month),
        year.parse::<i64>(),
    ) else {
        return f64::NAN;
    };
    let clock: Vec<i64> = time
        .split(':')
        .filter_map(|part| part.parse().ok())
        .collect();
    let [hour, minute, second] = clock.as_slice() else {
        return f64::NAN;
    };
    // Days from civil (Howard Hinnant's algorithm).
    let month = i64::try_from(month).unwrap_or_default() + 1;
    let shifted_year = if month <= 2 { year - 1 } else { year };
    let era = shifted_year.div_euclid(400);
    let year_of_era = shifted_year - era * 400;
    let day_of_year = (153 * (month + if month > 2 { -3 } else { 9 }) + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    let days = era * 146_097 + day_of_era - 719_468;
    let seconds = days * 86_400 + hour * 3600 + minute * 60 + second;
    // Realistic dates stay far below 2^53 milliseconds.
    #[allow(clippy::cast_precision_loss)] // see comment above
    let ms = (seconds * 1000) as f64;
    ms
}

async fn fetch_with_rate_limit_retry(
    request: FetchRequest,
    signal: &AbortSignal,
    retry_policy: RetryPolicy,
) -> Result<FetchResponse, Thrown> {
    let has_budget = retry_policy.max_retries > 0 && retry_policy.max_elapsed_ms > 0;
    let request_signal = if has_budget {
        AbortSignal::any(&[signal.clone(), timeout_signal(retry_policy.max_elapsed_ms)])
    } else {
        signal.clone()
    };
    let retry_deadline =
        has_budget.then(|| Instant::now() + Duration::from_millis(retry_policy.max_elapsed_ms));
    let mut retry = 0_u32;
    loop {
        let response = fetch(
            request.clone(),
            Some(&AbortSignal::any(&[
                request_signal.clone(),
                timeout_signal(5000),
            ])),
        )
        .await?;
        if response.status != 429 || retry == retry_policy.max_retries {
            return Ok(response);
        }

        let mut delay_ms = 500.0 * f64::from(2_u32.pow(retry));
        if let Some(retry_after) = response
            .header("retry-after")
            .filter(|value| !value.is_empty())
        {
            let seconds = js_parse_float(retry_after);
            delay_ms = if seconds.is_nan() {
                parse_http_date_ms(retry_after) - crate::auth::errors::date_now()
            } else {
                seconds * 1000.0
            };
            if !delay_ms.is_finite() {
                return Ok(response);
            }
        }
        delay_ms = delay_ms.max(0.0);
        if let Some(deadline) = retry_deadline {
            let remaining_ms = deadline
                .saturating_duration_since(Instant::now())
                .as_secs_f64()
                * 1000.0;
            if delay_ms >= remaining_ms {
                return Ok(response);
            }
        }
        sleep(delay_ms, &request_signal).await?;
        retry += 1;
    }
}

fn copilot_request(request: FetchRequest) -> FetchRequest {
    COPILOT_HEADERS
        .iter()
        .fold(request, |request, (name, value)| {
            request.header(name, *value)
        })
}

async fn fetch_github_copilot_models(
    copilot_token: &str,
    enterprise_domain: Option<&str>,
    signal: &AbortSignal,
    retry_policy: RetryPolicy,
) -> Result<ModelCatalog, Thrown> {
    let base_url = get_github_copilot_base_url(Some(copilot_token), enterprise_domain);
    // Some Individual accounts return false for every picker flag despite explicit enabled
    // policies. Limit the fallback to that endpoint so other account types keep strict
    // picker semantics.
    let allow_policy_fallback = base_url == INDIVIDUAL_BASE_URL;
    let request = copilot_request(
        FetchRequest::get(format!("{base_url}/models"))
            .header("Accept", "application/json")
            .header("Authorization", format!("Bearer {copilot_token}")),
    )
    .header("X-GitHub-Api-Version", COPILOT_API_VERSION);
    let response = fetch_with_rate_limit_retry(request, signal, retry_policy).await?;
    if !response.ok() {
        return Err(js_error(format!(
            "{} {}: {}",
            response.status, response.status_text, response.body
        )));
    }
    parse_github_copilot_model_catalog(&response.json()?, allow_policy_fallback)
}

async fn fetch_json(request: FetchRequest, signal: &AbortSignal) -> Result<Value, Thrown> {
    let response = fetch(request, Some(signal)).await?;
    if !response.ok() {
        return Err(js_error(format!(
            "{} {}: {}",
            response.status, response.status_text, response.body
        )));
    }
    response.json()
}

async fn start_device_flow(
    domain: &str,
    signal: &AbortSignal,
) -> Result<DeviceCodeResponse, Thrown> {
    let urls = get_urls(domain);
    let data = fetch_json(
        FetchRequest::post(urls.device_code)
            .header("Accept", "application/json")
            .header("Content-Type", "application/x-www-form-urlencoded")
            .header("User-Agent", "GitHubCopilotChat/0.35.0")
            .form(&[("client_id", &CLIENT_ID), ("scope", "read:user")]),
        signal,
    )
    .await?;

    if !data.is_object() {
        return Err(js_error("Invalid device code response"));
    }

    let interval = data.get("interval");
    let fields = (
        string_field(&data, "device_code"),
        string_field(&data, "user_code"),
        string_field(&data, "verification_uri"),
        data.get("expires_in").and_then(Value::as_f64),
    );
    let (Some(device_code), Some(user_code), Some(verification_uri), Some(expires_in)) = fields
    else {
        return Err(js_error("Invalid device code response fields"));
    };
    let interval = match interval {
        None => None,
        Some(Value::Number(number)) => number.as_f64(),
        Some(_) => return Err(js_error("Invalid device code response fields")),
    };

    // The verification URI is opened in the user's browser and to prevent `open` from
    // opening an executable or similar, we force it to be a URL.
    let untrusted = || js_error("Untrusted verification_uri in device code response");
    let parsed_uri = url::Url::parse(verification_uri).map_err(|_| untrusted())?;
    if parsed_uri.scheme() != "https" && parsed_uri.scheme() != "http" {
        return Err(untrusted());
    }

    Ok(DeviceCodeResponse {
        device_code: device_code.to_owned(),
        user_code: user_code.to_owned(),
        verification_uri: parsed_uri.to_string(),
        interval,
        expires_in,
    })
}

async fn poll_access_token_once(
    urls: &Urls,
    device: &DeviceCodeResponse,
    signal: &AbortSignal,
) -> Result<OAuthDeviceCodePollResult<String>, Thrown> {
    let raw = fetch_json(
        FetchRequest::post(urls.access_token.clone())
            .header("Accept", "application/json")
            .header("Content-Type", "application/x-www-form-urlencoded")
            .header("User-Agent", "GitHubCopilotChat/0.35.0")
            .form(&[
                ("client_id", &CLIENT_ID),
                ("device_code", &device.device_code),
                ("grant_type", "urn:ietf:params:oauth:grant-type:device_code"),
            ]),
        signal,
    )
    .await?;

    if let Some(access_token) = string_field(&raw, "access_token") {
        return Ok(OAuthDeviceCodePollResult::Complete {
            value: access_token.to_owned(),
        });
    }

    if let Some(error) = string_field(&raw, "error") {
        return Ok(match error {
            "authorization_pending" => OAuthDeviceCodePollResult::Pending,
            "slow_down" => OAuthDeviceCodePollResult::SlowDown {
                interval_seconds: raw.get("interval").and_then(Value::as_f64),
            },
            _ => {
                let description_suffix = string_field(&raw, "error_description")
                    .filter(|description| !description.is_empty())
                    .map(|description| format!(": {description}"))
                    .unwrap_or_default();
                OAuthDeviceCodePollResult::Failed {
                    message: format!("Device flow failed: {error}{description_suffix}"),
                }
            }
        });
    }

    Ok(OAuthDeviceCodePollResult::Failed {
        message: "Invalid device token response".to_owned(),
    })
}

async fn poll_for_github_access_token(
    domain: &str,
    device: &DeviceCodeResponse,
    signal: &AbortSignal,
) -> Result<String, Thrown> {
    let urls = get_urls(domain);
    poll_oauth_device_code_flow(
        OAuthDeviceCodePollOptions {
            interval_seconds: device.interval,
            expires_in_seconds: Some(device.expires_in),
            wait_before_first_poll: true,
            signal: signal.clone(),
        },
        || poll_access_token_once(&urls, device, signal),
    )
    .await
}

async fn refresh_github_copilot_access_token(
    refresh_token: &str,
    enterprise_domain: Option<&str>,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    let domain = enterprise_domain
        .filter(|domain| !domain.is_empty())
        .unwrap_or("github.com");
    let urls = get_urls(domain);

    let raw = fetch_json(
        copilot_request(
            FetchRequest::get(urls.copilot_token)
                .header("Accept", "application/json")
                .header("Authorization", format!("Bearer {refresh_token}")),
        ),
        signal,
    )
    .await?;

    if !raw.is_object() {
        return Err(js_error("Invalid Copilot token response"));
    }

    let (Some(token), Some(expires_at)) = (
        string_field(&raw, "token"),
        raw.get("expires_at").and_then(Value::as_f64),
    ) else {
        return Err(js_error("Invalid Copilot token response fields"));
    };

    let mut credential = OAuthCredential::new(
        refresh_token,
        token,
        expires_at * 1000.0 - 5.0 * 60.0 * 1000.0,
    );
    if let Some(domain) = enterprise_domain {
        credential
            .extra
            .insert("enterpriseUrl".to_owned(), Value::String(domain.to_owned()));
    }
    Ok(credential)
}

fn with_available_model_ids(mut credential: OAuthCredential, ids: Vec<String>) -> OAuthCredential {
    credential.extra.insert(
        "availableModelIds".to_owned(),
        Value::Array(ids.into_iter().map(Value::String).collect()),
    );
    credential
}

/// Refresh `GitHub` Copilot token.
async fn refresh_github_copilot_token(
    refresh_token: &str,
    enterprise_domain: Option<&str>,
    signal: &AbortSignal,
) -> Result<OAuthCredential, Thrown> {
    let credentials =
        refresh_github_copilot_access_token(refresh_token, enterprise_domain, signal).await?;
    let catalog = fetch_github_copilot_models(
        &credentials.access,
        enterprise_domain,
        signal,
        RetryPolicy {
            max_retries: 0,
            max_elapsed_ms: 0,
        },
    )
    .await?;
    Ok(with_available_model_ids(
        credentials,
        catalog.available_model_ids,
    ))
}

/// Enable a model for the user's `GitHub` Copilot account. This is required
/// for some models (like Claude, Grok) before they can be used.
async fn enable_github_copilot_model(
    token: &str,
    model_id: &str,
    enterprise_domain: Option<&str>,
    signal: &AbortSignal,
) -> Result<bool, Thrown> {
    let base_url = get_github_copilot_base_url(Some(token), enterprise_domain);
    let request = copilot_request(
        FetchRequest::post(format!("{base_url}/models/{model_id}/policy"))
            .header("Content-Type", "application/json")
            .header("Authorization", format!("Bearer {token}")),
    )
    .header("openai-intent", "chat-policy")
    .header("x-interaction-type", "chat-policy")
    .body(serde_json::json!({ "state": "enabled" }).to_string());

    let response = match fetch_with_rate_limit_retry(
        request,
        signal,
        RetryPolicy {
            max_retries: 2,
            max_elapsed_ms: 5000,
        },
    )
    .await
    {
        Ok(response) => response,
        Err(error) => {
            if signal.aborted() {
                return Err(error);
            }
            return Ok(false);
        }
    };
    if response.status == 429 {
        return Err(js_error(format!(
            "{} {}: {}",
            response.status, response.status_text, response.body
        )));
    }
    Ok(response.ok())
}

/// Enable the requested `GitHub` Copilot models and return the successful IDs.
/// Policy updates are best effort; exhausted rate limiting stops the batch.
async fn enable_github_copilot_models(
    token: &str,
    model_ids: &[String],
    enterprise_domain: Option<&str>,
    signal: &AbortSignal,
) -> Result<Vec<String>, Thrown> {
    let mut enabled_model_ids = Vec::new();
    for model_id in model_ids {
        match enable_github_copilot_model(token, model_id, enterprise_domain, signal).await {
            Ok(true) => enabled_model_ids.push(model_id.clone()),
            Ok(false) => {}
            Err(error) => {
                if signal.aborted() {
                    return Err(error);
                }
                break;
            }
        }
    }
    Ok(enabled_model_ids)
}

async fn login_github_copilot(
    interaction: &ProviderAuthInteraction,
) -> Result<OAuthCredential, Thrown> {
    let input = interaction
        .prompt(AuthPrompt::new(AuthPromptKind::Text {
            message: "GitHub Enterprise URL/domain (blank for github.com)".to_owned(),
            placeholder: Some("company.ghe.com".to_owned()),
        }))
        .await?;
    if interaction.signal.aborted() {
        return Err(js_error("Login cancelled"));
    }

    let trimmed = input.trim();
    let enterprise_domain = normalize_domain(&input);
    if !trimmed.is_empty() && enterprise_domain.is_none() {
        return Err(js_error("Invalid GitHub Enterprise URL/domain"));
    }
    let enterprise_domain = enterprise_domain.as_deref();
    let domain = enterprise_domain.unwrap_or("github.com");

    let device = start_device_flow(domain, &interaction.signal).await?;
    interaction.notify(AuthEvent::DeviceCode {
        user_code: device.user_code.clone(),
        verification_uri: device.verification_uri.clone(),
        interval_seconds: device.interval,
        expires_in_seconds: Some(device.expires_in),
    });

    let github_access_token =
        poll_for_github_access_token(domain, &device, &interaction.signal).await?;
    let credentials = refresh_github_copilot_access_token(
        &github_access_token,
        enterprise_domain,
        &interaction.signal,
    )
    .await?;
    let models = fetch_github_copilot_models(
        &credentials.access,
        enterprise_domain,
        &interaction.signal,
        RetryPolicy {
            max_retries: 2,
            max_elapsed_ms: 5000,
        },
    )
    .await?;
    let mut enabled_model_ids = Vec::new();
    if !models.policy_model_ids.is_empty() {
        interaction.notify(AuthEvent::Progress {
            message: "Enabling models...".to_owned(),
        });
        enabled_model_ids = enable_github_copilot_models(
            &credentials.access,
            &models.policy_model_ids,
            enterprise_domain,
            &interaction.signal,
        )
        .await?;
    }
    let mut available = Vec::new();
    for id in models
        .available_model_ids
        .into_iter()
        .chain(enabled_model_ids)
    {
        if !available.contains(&id) {
            available.push(id);
        }
    }
    Ok(with_available_model_ids(credentials, available))
}

fn copilot_enterprise_domain(credential: &OAuthCredential) -> Option<String> {
    credential
        .extra_str("enterpriseUrl")
        .filter(|url| !url.is_empty())
        .and_then(normalize_domain)
}

struct GitHubCopilotOAuth;

impl OAuthAuth for GitHubCopilotOAuth {
    fn name(&self) -> &'static str {
        "GitHub Copilot"
    }

    fn is_subscription(&self) -> Option<bool> {
        Some(true)
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        _options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { login_github_copilot(&interaction).await })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move {
            let domain = copilot_enterprise_domain(&credential);
            refresh_github_copilot_token(&credential.refresh, domain.as_deref(), &signal).await
        })
    }

    /// Derive the credential-specific proxy endpoint for each request.
    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move {
            let domain = copilot_enterprise_domain(credential);
            Ok(ModelAuth {
                api_key: Some(credential.access.clone()),
                headers: None,
                base_url: Some(get_github_copilot_base_url(
                    Some(&credential.access),
                    domain.as_deref(),
                )),
            })
        })
    }
}

/// The `GitHub` Copilot OAuth flow (`githubCopilotOAuth`).
#[must_use]
pub fn github_copilot_oauth() -> Arc<dyn OAuthAuth> {
    shared(GitHubCopilotOAuth)
}

#[cfg(test)]
#[path = "github_copilot_tests.rs"]
mod tests;
