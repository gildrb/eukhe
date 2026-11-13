//! Anthropic plan (Claude Pro/Max login) quota: the
//! `anthropic-ratelimit-unified-<window>-*` headers of every model response
//! and the OAuth usage endpoint `api.anthropic.com/api/oauth/usage`.

use reqwest::header::HeaderMap;
use serde_json::Value;

use super::parse::{epoch_ms, get_json, header_number, iso_ms, number, permille};
use super::{CredentialId, CredentialKind, PlanCredential, PlanQuota, QuotaBoard, QuotaError};
use super::{QuotaSource, QuotaWindow};
use crate::api::anthropic_messages::{is_oauth_token, CLAUDE_CODE_VERSION};
use crate::auth::oauth::http::FetchRequest;

pub(super) const PROVIDER: &str = "anthropic";
const USAGE_URL: &str = "https://api.anthropic.com/api/oauth/usage";
const OAUTH_BETA: &str = "oauth-2025-04-20";

/// The header windows: header infix, label, length in minutes.
const HEADER_WINDOWS: [(&str, &str, u64); 3] = [
    ("5h", "5h", 300),
    ("7d", "7d", 10_080),
    ("7d_oi", "7d fable", 10_080),
];

/// Record the unified rate-limit headers of a response to a plan login's
/// request of `provider` on the board.
pub(crate) fn record_headers(provider: &str, token: &str, headers: &HeaderMap) {
    if let Some(reading) = parse_headers(provider, headers, crate::utils::now_ms()) {
        QuotaBoard::record(&CredentialId::of(token), reading);
    }
}

/// The unified rate-limit headers as a reading; `None` without any.
pub(super) fn parse_headers(provider: &str, headers: &HeaderMap, now_ms: u64) -> Option<PlanQuota> {
    let windows: Vec<QuotaWindow> = HEADER_WINDOWS
        .iter()
        .filter_map(|(infix, label, minutes)| {
            let prefix = format!("anthropic-ratelimit-unified-{infix}-");
            let used = header_number(headers, &format!("{prefix}utilization"))?;
            Some(QuotaWindow {
                label: (*label).to_owned(),
                window_minutes: Some(*minutes),
                used_permille: permille(used * 100.0)?,
                resets_at_ms: header_number(headers, &format!("{prefix}reset")).and_then(epoch_ms),
            })
        })
        .collect();
    (!windows.is_empty()).then(|| PlanQuota {
        provider: provider.to_owned(),
        plan: None,
        windows,
        read_at_ms: now_ms,
        source: QuotaSource::Headers,
    })
}

/// Read the plan usage endpoint. `None` for an API key.
pub(super) async fn fetch(
    credential: &PlanCredential<'_>,
) -> Result<Option<PlanQuota>, QuotaError> {
    let plan_login = match credential.kind {
        CredentialKind::OAuth => true,
        CredentialKind::ApiKey => is_oauth_token(credential.access),
    };
    if !plan_login {
        return Ok(None);
    }
    let request = FetchRequest::get(USAGE_URL)
        .header("accept", "application/json")
        .header("anthropic-beta", OAUTH_BETA)
        .header(
            "user-agent",
            format!("claude-cli/{CLAUDE_CODE_VERSION} (external, cli)"),
        )
        .header("authorization", format!("Bearer {}", credential.access));
    let body = get_json(request).await?;
    Ok(parse_usage(&body, crate::utils::now_ms()))
}

/// One `{utilization, resets_at}` bucket (utilization in percent) as a
/// window.
fn bucket(
    label: &str,
    minutes: u64,
    used: Option<&Value>,
    resets: Option<&Value>,
) -> Option<QuotaWindow> {
    Some(QuotaWindow {
        label: label.to_owned(),
        window_minutes: Some(minutes),
        used_permille: permille(number(used)?)?,
        resets_at_ms: iso_ms(resets),
    })
}

/// The usage endpoint's body as a reading; `None` when it meters no window.
pub(super) fn parse_usage(body: &Value, now_ms: u64) -> Option<PlanQuota> {
    let limits: &[Value] = body
        .get("limits")
        .and_then(Value::as_array)
        .map_or(&[], Vec::as_slice);
    let limit_of = |kind: &str| {
        limits
            .iter()
            .find(|entry| entry.get("kind").and_then(Value::as_str) == Some(kind))
    };
    let legacy = |field: &str, label: &str, kind: Option<&str>| {
        let from_field = body
            .get(field)
            .and_then(|b| bucket(label, 10_080, b.get("utilization"), b.get("resets_at")));
        from_field.or_else(|| {
            let entry = limit_of(kind?)?;
            bucket(label, 10_080, entry.get("percent"), entry.get("resets_at"))
        })
    };
    let mut windows: Vec<QuotaWindow> = [
        legacy("five_hour", "5h", Some("session")).map(|w| QuotaWindow {
            window_minutes: Some(300),
            ..w
        }),
        legacy("seven_day", "7d", Some("weekly_all")),
        legacy("seven_day_opus", "7d opus", None),
        legacy("seven_day_sonnet", "7d sonnet", None),
    ]
    .into_iter()
    .flatten()
    .collect();
    for entry in limits {
        if entry.get("kind").and_then(Value::as_str) != Some("weekly_scoped") {
            continue;
        }
        let Some(name) = entry
            .pointer("/scope/model/display_name")
            .and_then(Value::as_str)
            .map(str::trim)
            .filter(|name| !name.is_empty())
        else {
            continue;
        };
        let label = format!("7d {}", name.to_lowercase());
        if windows.iter().any(|window| window.label == label) {
            continue;
        }
        if let Some(window) = bucket(&label, 10_080, entry.get("percent"), entry.get("resets_at")) {
            windows.push(window);
        }
    }
    (!windows.is_empty()).then(|| PlanQuota {
        provider: PROVIDER.to_owned(),
        plan: None,
        windows,
        read_at_ms: now_ms,
        source: QuotaSource::UsageEndpoint,
    })
}
