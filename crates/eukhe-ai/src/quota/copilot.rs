//! GitHub Copilot plan quota: the quota snapshots of
//! `api.<domain>/copilot_internal/user`, read with the login's GitHub token
//! on the host its Copilot token exchange already uses.

use serde_json::Value;

use super::parse::{get_json, iso_ms, number, permille};
use super::{CredentialKind, PlanCredential, PlanQuota, QuotaError, QuotaSource, QuotaWindow};
use crate::auth::oauth::github_copilot::{copilot_request, normalize_domain};
use crate::auth::oauth::http::FetchRequest;

pub(super) const PROVIDER: &str = "github-copilot";

/// The metered snapshots: field, window label.
const SNAPSHOTS: [(&str, &str); 3] = [
    ("premium_interactions", "month premium"),
    ("chat", "month chat"),
    ("completions", "month completions"),
];

/// Read the plan usage endpoint. `None` for an API key.
pub(super) async fn fetch(
    credential: &PlanCredential<'_>,
) -> Result<Option<PlanQuota>, QuotaError> {
    if credential.kind == CredentialKind::ApiKey {
        return Ok(None);
    }
    let github_token = credential.refresh.unwrap_or(credential.access);
    let domain = credential
        .enterprise_url
        .and_then(normalize_domain)
        .unwrap_or_else(|| "github.com".to_owned());
    let request = copilot_request(
        FetchRequest::get(format!("https://api.{domain}/copilot_internal/user"))
            .header("Accept", "application/json")
            .header("Authorization", format!("Bearer {github_token}")),
    );
    let body = get_json(request).await?;
    Ok(parse_usage(&body, crate::utils::now_ms()))
}

/// The endpoint's body as a reading; `None` when every snapshot is
/// unlimited or missing.
pub(super) fn parse_usage(body: &Value, now_ms: u64) -> Option<PlanQuota> {
    let resets_at_ms = iso_ms(body.get("quota_reset_date"));
    let windows: Vec<QuotaWindow> = SNAPSHOTS
        .iter()
        .filter_map(|(field, label)| {
            let snapshot = body.pointer(&format!("/quota_snapshots/{field}"))?;
            if snapshot.get("unlimited").and_then(Value::as_bool) != Some(false) {
                return None;
            }
            let entitlement = number(snapshot.get("entitlement")).filter(|e| *e > 0.0)?;
            let remaining = number(snapshot.get("remaining"))?;
            Some(QuotaWindow {
                label: (*label).to_owned(),
                window_minutes: None,
                used_permille: permille((entitlement - remaining) / entitlement * 100.0)?,
                resets_at_ms,
            })
        })
        .collect();
    (!windows.is_empty()).then(|| PlanQuota {
        provider: PROVIDER.to_owned(),
        plan: body
            .get("copilot_plan")
            .and_then(Value::as_str)
            .filter(|plan| !plan.is_empty())
            .map(str::to_owned),
        windows,
        read_at_ms: now_ms,
        source: QuotaSource::UsageEndpoint,
    })
}
