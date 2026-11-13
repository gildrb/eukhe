//! `ChatGPT` plan (Codex login) quota: the `x-codex-{primary,secondary}-*`
//! headers of an SSE response, the `codex.rate_limits` frame of a response
//! stream, and the usage endpoint `chatgpt.com/backend-api/wham/usage`.

use reqwest::header::HeaderMap;
use serde_json::Value;

use super::parse::{epoch_ms, get_json, header_number, minutes, number, permille, window_label};
use super::{CredentialId, CredentialKind, PlanCredential, PlanQuota, QuotaBoard, QuotaError};
use super::{QuotaSource, QuotaWindow};
use crate::api::openai_codex_responses::extract_account_id;
use crate::auth::oauth::http::FetchRequest;
use crate::utils::pi_user_agent::get_pi_user_agent;

pub(super) const PROVIDER: &str = "openai-codex";
const USAGE_URL: &str = "https://chatgpt.com/backend-api/wham/usage";
const SLOTS: [&str; 2] = ["primary", "secondary"];

/// Record the rate-limit headers of a response to `provider`'s request.
pub(crate) fn record_headers(provider: &str, token: &str, headers: &HeaderMap) {
    if let Some(reading) = parse_headers(provider, headers, crate::utils::now_ms()) {
        QuotaBoard::record(&CredentialId::of(token), reading);
    }
}

/// Record a stream event of `provider`'s response when it is a
/// `codex.rate_limits` frame.
pub(crate) fn record_frame(provider: &str, credential: &CredentialId, event: &Value) {
    if let Some(reading) = parse_frame(provider, event, crate::utils::now_ms()) {
        QuotaBoard::record(credential, reading);
    }
}

/// The rate-limit headers as a reading; `None` without any.
pub(super) fn parse_headers(provider: &str, headers: &HeaderMap, now_ms: u64) -> Option<PlanQuota> {
    let windows: Vec<QuotaWindow> = SLOTS
        .iter()
        .filter_map(|slot| {
            let used = header_number(headers, &format!("x-codex-{slot}-used-percent"))?;
            let window_minutes =
                header_number(headers, &format!("x-codex-{slot}-window-minutes")).and_then(minutes);
            Some(QuotaWindow {
                label: window_minutes.map_or_else(|| (*slot).to_owned(), window_label),
                window_minutes,
                used_permille: permille(used)?,
                resets_at_ms: header_number(headers, &format!("x-codex-{slot}-reset-at"))
                    .and_then(epoch_ms),
            })
        })
        .collect();
    reading(provider, None, windows, now_ms, QuotaSource::Headers)
}

/// A `codex.rate_limits` frame as a reading; `None` for any other event.
pub(super) fn parse_frame(provider: &str, event: &Value, now_ms: u64) -> Option<PlanQuota> {
    if event.get("type").and_then(Value::as_str) != Some("codex.rate_limits") {
        return None;
    }
    let limits = event.get("rate_limits")?;
    let windows = SLOTS
        .iter()
        .filter_map(|slot| {
            let window = limits.get(*slot)?;
            let window_minutes = number(window.get("window_minutes")).and_then(minutes);
            frame_window(slot, window, window_minutes, now_ms)
        })
        .collect();
    reading(
        provider,
        plan_name(event),
        windows,
        now_ms,
        QuotaSource::StreamFrame,
    )
}

/// Read the plan usage endpoint. `None` for an API key.
pub(super) async fn fetch(
    credential: &PlanCredential<'_>,
) -> Result<Option<PlanQuota>, QuotaError> {
    if credential.kind == CredentialKind::ApiKey {
        return Ok(None);
    }
    let account_id = match credential.account_id {
        Some(account_id) => account_id.to_owned(),
        None => extract_account_id(credential.access).map_err(|_| QuotaError::Unreadable)?,
    };
    let request = FetchRequest::get(USAGE_URL)
        .header("Authorization", format!("Bearer {}", credential.access))
        .header("chatgpt-account-id", account_id)
        .header("originator", "pi")
        .header("User-Agent", get_pi_user_agent())
        .header("Accept", "application/json");
    let body = get_json(request).await?;
    Ok(parse_usage(&body, crate::utils::now_ms()))
}

/// The usage endpoint's body as a reading; `None` when it meters no window.
pub(super) fn parse_usage(body: &Value, now_ms: u64) -> Option<PlanQuota> {
    let mut windows: Vec<QuotaWindow> = endpoint_windows(body.get("rate_limit"), None, now_ms);
    for extra in body
        .get("additional_rate_limits")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        let name = ["limit_name", "metered_feature"]
            .iter()
            .find_map(|key| extra.get(*key).and_then(Value::as_str))
            .map(str::trim)
            .filter(|name| !name.is_empty())
            .map(str::to_lowercase);
        windows.extend(endpoint_windows(
            extra.get("rate_limit"),
            Some(name.as_deref().unwrap_or("additional")),
            now_ms,
        ));
    }
    reading(
        PROVIDER,
        plan_name(body),
        windows,
        now_ms,
        QuotaSource::UsageEndpoint,
    )
}

/// The `primary_window` / `secondary_window` of one `rate_limit` object,
/// labelled "<length> <name>" for a named extra limit.
fn endpoint_windows(
    rate_limit: Option<&Value>,
    name: Option<&str>,
    now_ms: u64,
) -> Vec<QuotaWindow> {
    let Some(rate_limit) = rate_limit else {
        return Vec::new();
    };
    SLOTS
        .iter()
        .filter_map(|slot| {
            let window = rate_limit.get(format!("{slot}_window"))?;
            let window_minutes = number(window.get("limit_window_seconds"))
                .and_then(|seconds| minutes(seconds / 60.0));
            let mut window = frame_window(slot, window, window_minutes, now_ms)?;
            if let Some(name) = name {
                window.label = format!("{} {name}", window.label);
            }
            Some(window)
        })
        .collect()
}

/// One window object: `used_percent` plus `reset_at` (epoch seconds) or
/// `reset_after_seconds`.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "non-negative and finite, checked before the cast"
)]
fn frame_window(
    slot: &str,
    window: &Value,
    window_minutes: Option<u64>,
    now_ms: u64,
) -> Option<QuotaWindow> {
    let used = number(window.get("used_percent"))?;
    let resets_at_ms = number(window.get("reset_at"))
        .and_then(epoch_ms)
        .or_else(|| {
            number(window.get("reset_after_seconds"))
                .filter(|seconds| *seconds >= 0.0)
                .map(|seconds| now_ms + (seconds * 1000.0) as u64)
        });
    Some(QuotaWindow {
        label: window_minutes.map_or_else(|| slot.to_owned(), window_label),
        window_minutes,
        used_permille: permille(used)?,
        resets_at_ms,
    })
}

fn plan_name(body: &Value) -> Option<String> {
    body.get("plan_type")
        .and_then(Value::as_str)
        .filter(|plan| !plan.is_empty())
        .map(str::to_owned)
}

fn reading(
    provider: &str,
    plan: Option<String>,
    windows: Vec<QuotaWindow>,
    now_ms: u64,
    source: QuotaSource,
) -> Option<PlanQuota> {
    (!windows.is_empty()).then(|| PlanQuota {
        provider: provider.to_owned(),
        plan,
        windows,
        read_at_ms: now_ms,
        source,
    })
}
