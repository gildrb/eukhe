//! Recorded headers, frames and usage endpoint bodies of each provider.

use std::sync::{Arc, Mutex, PoisonError};

use reqwest::header::{HeaderMap, HeaderName, HeaderValue};
use serde_json::json;

use super::*;
use crate::auth::oauth::http::{mock, FetchRequest, FetchResponse};

const NOW: u64 = 1_785_000_000_000;

fn headers(pairs: &[(&str, &str)]) -> HeaderMap {
    pairs
        .iter()
        .map(|(name, value)| {
            (
                HeaderName::from_bytes(name.as_bytes()).expect("name"),
                HeaderValue::from_str(value).expect("value"),
            )
        })
        .collect()
}

fn window(label: &str, minutes: Option<u64>, permille: u32, resets: Option<u64>) -> QuotaWindow {
    QuotaWindow {
        label: label.to_owned(),
        window_minutes: minutes,
        used_permille: permille,
        resets_at_ms: resets,
    }
}

fn oauth(access: &str) -> PlanCredential<'_> {
    PlanCredential {
        kind: CredentialKind::OAuth,
        access,
        refresh: None,
        account_id: None,
        enterprise_url: None,
    }
}

/// Stub the usage endpoint with `body`; the requests it saw.
async fn stub(body: serde_json::Value) -> (mock::FetchMockGuard, Arc<Mutex<Vec<FetchRequest>>>) {
    let seen = Arc::new(Mutex::new(Vec::new()));
    let log = Arc::clone(&seen);
    let guard = mock::install(move |request| {
        log.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(request);
        let body = body.clone();
        async move { Ok(FetchResponse::json_response(&body, 200)) }
    })
    .await;
    (guard, seen)
}

#[test]
fn anthropic_unified_headers_are_the_plan_windows() {
    let reading = anthropic::parse_headers(
        "anthropic",
        &headers(&[
            ("anthropic-ratelimit-unified-status", "allowed"),
            ("anthropic-ratelimit-unified-5h-status", "allowed"),
            ("anthropic-ratelimit-unified-5h-utilization", "0.42"),
            ("anthropic-ratelimit-unified-5h-reset", "1785003600"),
            ("anthropic-ratelimit-unified-7d-utilization", "0.815"),
            ("anthropic-ratelimit-unified-7d-reset", "1785400000"),
            (
                "anthropic-ratelimit-unified-representative-claim",
                "five_hour",
            ),
        ]),
        NOW,
    );
    assert_eq!(
        reading,
        Some(PlanQuota {
            provider: "anthropic".to_owned(),
            plan: None,
            windows: vec![
                window("5h", Some(300), 420, Some(1_785_003_600_000)),
                window("7d", Some(10_080), 815, Some(1_785_400_000_000)),
            ],
            read_at_ms: NOW,
            source: QuotaSource::Headers,
        })
    );
}

/// The unified headers of a plan login's Haiku response (recorded
/// 2026-11-13): only the 7-day window reported.
#[test]
fn recorded_plan_response_headers_read_the_seven_day_window() {
    let recorded = headers(&[
        ("anthropic-ratelimit-unified-overage-status", "rejected"),
        (
            "anthropic-ratelimit-unified-representative-claim",
            "seven_day",
        ),
        ("anthropic-ratelimit-unified-upgrade-paths", "overage"),
        ("anthropic-ratelimit-unified-reset", "1794625200"),
        ("anthropic-ratelimit-unified-7d-surpassed-threshold", "0.75"),
        ("anthropic-ratelimit-unified-7d-reset", "1794625200"),
        ("anthropic-ratelimit-unified-7d-status", "allowed_warning"),
        ("anthropic-ratelimit-unified-fallback-percentage", "0.5"),
        (
            "anthropic-ratelimit-unified-overage-disabled-reason",
            "out_of_credits",
        ),
        ("anthropic-ratelimit-unified-7d-utilization", "0.95"),
        ("anthropic-ratelimit-unified-status", "allowed_warning"),
    ]);
    assert_eq!(
        anthropic::parse_headers("anthropic", &recorded, NOW).map(|reading| reading.windows),
        Some(vec![window(
            "7d",
            Some(10_080),
            950,
            Some(1_794_625_200_000)
        )])
    );
}

#[test]
fn a_response_without_unified_headers_is_no_reading() {
    let api_key_response = headers(&[
        ("anthropic-ratelimit-requests-limit", "4000"),
        ("anthropic-ratelimit-requests-remaining", "3999"),
    ]);
    assert_eq!(
        anthropic::parse_headers("anthropic", &api_key_response, NOW),
        None
    );
}

fn anthropic_usage_body() -> serde_json::Value {
    json!({
        "five_hour": { "utilization": 37.0, "resets_at": "2026-07-25T18:00:00.512345+00:00" },
        "seven_day": { "utilization": 81.5, "resets_at": "2026-07-29T09:00:00+00:00" },
        "seven_day_opus": null,
        "seven_day_sonnet": null,
        "limits": [
            { "kind": "session", "percent": 37, "resets_at": "2026-07-25T18:00:00Z", "is_active": true },
            { "kind": "weekly_scoped", "percent": 5, "resets_at": "2026-07-29T09:00:00Z",
              "scope": { "model": { "display_name": "Opus" } }, "is_active": false },
        ],
        "extra_usage": { "is_enabled": false, "monthly_limit": null, "used_credits": null },
    })
}

#[test]
fn anthropic_usage_endpoint_buckets_and_scoped_limits_are_windows() {
    assert_eq!(
        anthropic::parse_usage(&anthropic_usage_body(), NOW),
        Some(PlanQuota {
            provider: "anthropic".to_owned(),
            plan: None,
            windows: vec![
                window("5h", Some(300), 370, Some(1_785_002_400_512)),
                window("7d", Some(10_080), 815, Some(1_785_315_600_000)),
                window("7d opus", Some(10_080), 50, Some(1_785_315_600_000)),
            ],
            read_at_ms: NOW,
            source: QuotaSource::UsageEndpoint,
        })
    );
}

#[test]
fn anthropic_usage_falls_back_to_the_limit_kinds() {
    let body = json!({
        "five_hour": null,
        "seven_day": null,
        "limits": [
            { "kind": "session", "percent": 12, "resets_at": "2026-07-25T18:00:00Z" },
            { "kind": "weekly_all", "percent": 64, "resets_at": "2026-07-29T09:00:00Z" },
        ],
    });
    let reading = anthropic::parse_usage(&body, NOW).expect("reading");
    assert_eq!(
        reading.windows,
        vec![
            window("5h", Some(300), 120, Some(1_785_002_400_000)),
            window("7d", Some(10_080), 640, Some(1_785_315_600_000)),
        ]
    );
}

#[tokio::test]
async fn anthropic_fetch_reads_the_oauth_usage_endpoint_onto_the_board() {
    let (_guard, seen) = stub(anthropic_usage_body()).await;
    let token = "sk-ant-oat01-test";
    let reading = fetch_plan_quota("anthropic", &oauth(token))
        .await
        .expect("read")
        .expect("reading");
    let requests = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    assert_eq!(requests.len(), 1);
    assert_eq!(requests[0].url, "https://api.anthropic.com/api/oauth/usage");
    assert_eq!(
        requests[0].header_value("authorization"),
        Some("Bearer sk-ant-oat01-test")
    );
    assert_eq!(
        requests[0].header_value("anthropic-beta"),
        Some("oauth-2025-04-20")
    );
    assert_eq!(
        QuotaBoard::latest_for("anthropic", &CredentialId::of(token)),
        Some(reading.clone())
    );
    assert_eq!(QuotaBoard::latest("anthropic"), Some(reading));
}

#[tokio::test]
async fn an_api_key_has_no_plan_quota_and_sends_nothing() {
    let (_guard, seen) = stub(anthropic_usage_body()).await;
    let key = PlanCredential {
        kind: CredentialKind::ApiKey,
        ..oauth("sk-ant-api03-test")
    };
    for provider in ["anthropic", "openai-codex", "github-copilot", "openai"] {
        assert_eq!(fetch_plan_quota(provider, &key).await, Ok(None));
    }
    assert!(seen
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .is_empty());
}

#[tokio::test]
async fn a_refused_usage_read_names_the_status() {
    let _guard = mock::install(|_| async {
        Ok(FetchResponse::json_response(
            &json!({ "error": { "type": "authentication_error" } }),
            401,
        ))
    })
    .await;
    assert_eq!(
        fetch_plan_quota("anthropic", &oauth("sk-ant-oat01-expired")).await,
        Err(QuotaError::Status { status: 401 })
    );
}

#[test]
fn codex_rate_limit_headers_are_the_plan_windows() {
    let reading = codex::parse_headers(
        "openai-codex",
        &headers(&[
            ("x-codex-primary-used-percent", "23"),
            ("x-codex-primary-window-minutes", "300"),
            ("x-codex-primary-reset-at", "1785010000"),
            ("x-codex-secondary-used-percent", "7.5"),
            ("x-codex-secondary-window-minutes", "10080"),
            ("x-codex-secondary-reset-at", "1785269351"),
        ]),
        NOW,
    );
    assert_eq!(
        reading,
        Some(PlanQuota {
            provider: "openai-codex".to_owned(),
            plan: None,
            windows: vec![
                window("5h", Some(300), 230, Some(1_785_010_000_000)),
                window("7d", Some(10_080), 75, Some(1_785_269_351_000)),
            ],
            read_at_ms: NOW,
            source: QuotaSource::Headers,
        })
    );
}

/// The frame the Codex websocket sends before a response (recorded).
fn codex_frame() -> serde_json::Value {
    json!({
        "type": "codex.rate_limits",
        "plan_type": "plus",
        "rate_limits": {
            "allowed": true,
            "limit_reached": false,
            "primary": { "used_percent": 7, "window_minutes": 10080, "reset_after_seconds": 556_112, "reset_at": 1_785_269_351 },
            "secondary": null,
        },
        "code_review_rate_limits": null,
        "additional_rate_limits": null,
        "credits": { "has_credits": false, "unlimited": false, "balance": "0" },
        "promo": null,
    })
}

#[test]
fn the_codex_rate_limits_frame_is_a_reading() {
    assert_eq!(
        codex::parse_frame("openai-codex", &codex_frame(), NOW),
        Some(PlanQuota {
            provider: "openai-codex".to_owned(),
            plan: Some("plus".to_owned()),
            windows: vec![window("7d", Some(10_080), 70, Some(1_785_269_351_000))],
            read_at_ms: NOW,
            source: QuotaSource::StreamFrame,
        })
    );
    let other = json!({ "type": "response.created", "response": { "id": "resp_1" } });
    assert_eq!(codex::parse_frame("openai-codex", &other, NOW), None);
}

#[test]
fn a_codex_window_without_reset_at_resets_after_its_seconds() {
    let frame = json!({
        "type": "codex.rate_limits",
        "rate_limits": { "primary": { "used_percent": 50, "window_minutes": 300, "reset_after_seconds": 60 } },
    });
    let reading = codex::parse_frame("openai-codex", &frame, NOW).expect("reading");
    assert_eq!(
        reading.windows,
        vec![window("5h", Some(300), 500, Some(NOW + 60_000))]
    );
}

fn codex_usage_body() -> serde_json::Value {
    json!({
        "plan_type": "pro",
        "rate_limit": {
            "allowed": true,
            "limit_reached": false,
            "primary_window": { "used_percent": 12, "limit_window_seconds": 18000, "reset_after_seconds": 9000, "reset_at": 1_785_009_000 },
            "secondary_window": { "used_percent": 81, "limit_window_seconds": 604_800, "reset_after_seconds": 300_000, "reset_at": 1_785_300_000 },
        },
        "additional_rate_limits": [{
            "limit_name": "Spark",
            "metered_feature": "codex_spark",
            "rate_limit": {
                "primary_window": { "used_percent": 3, "limit_window_seconds": 18000, "reset_at": 1_785_009_000 },
                "secondary_window": null,
            },
        }],
        "credits": { "has_credits": false, "unlimited": false, "balance": "0" },
    })
}

#[test]
fn codex_usage_endpoint_windows_include_the_named_limits() {
    assert_eq!(
        codex::parse_usage(&codex_usage_body(), NOW),
        Some(PlanQuota {
            provider: "openai-codex".to_owned(),
            plan: Some("pro".to_owned()),
            windows: vec![
                window("5h", Some(300), 120, Some(1_785_009_000_000)),
                window("7d", Some(10_080), 810, Some(1_785_300_000_000)),
                window("5h spark", Some(300), 30, Some(1_785_009_000_000)),
            ],
            read_at_ms: NOW,
            source: QuotaSource::UsageEndpoint,
        })
    );
}

#[tokio::test]
async fn codex_fetch_sends_the_account_of_the_login() {
    let (_guard, seen) = stub(codex_usage_body()).await;
    let credential = PlanCredential {
        account_id: Some("acct-1"),
        ..oauth("codex-access-token")
    };
    let reading = fetch_plan_quota("openai-codex", &credential)
        .await
        .expect("read")
        .expect("reading");
    assert_eq!(reading.plan.as_deref(), Some("pro"));
    let requests = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    assert_eq!(
        requests[0].url,
        "https://chatgpt.com/backend-api/wham/usage"
    );
    assert_eq!(
        requests[0].header_value("chatgpt-account-id"),
        Some("acct-1")
    );
    assert_eq!(
        requests[0].header_value("authorization"),
        Some("Bearer codex-access-token")
    );
}

fn copilot_usage_body() -> serde_json::Value {
    json!({
        "copilot_plan": "individual_pro",
        "quota_reset_date": "2026-08-01",
        "quota_snapshots": {
            "chat": { "entitlement": 0, "remaining": 0, "percent_remaining": 100, "unlimited": true, "overage_count": 0, "overage_permitted": false, "quota_id": "chat" },
            "completions": { "entitlement": 0, "remaining": 0, "percent_remaining": 100, "unlimited": true, "overage_count": 0, "overage_permitted": false, "quota_id": "completions" },
            "premium_interactions": { "entitlement": 300, "remaining": 54, "percent_remaining": 18.0, "unlimited": false, "overage_count": 0, "overage_permitted": true, "quota_id": "premium_interactions" },
        },
    })
}

#[test]
fn copilot_metered_snapshots_are_monthly_windows() {
    assert_eq!(
        copilot::parse_usage(&copilot_usage_body(), NOW),
        Some(PlanQuota {
            provider: "github-copilot".to_owned(),
            plan: Some("individual_pro".to_owned()),
            windows: vec![window("month premium", None, 820, Some(1_785_542_400_000))],
            read_at_ms: NOW,
            source: QuotaSource::UsageEndpoint,
        })
    );
}

#[tokio::test]
async fn copilot_fetch_uses_the_github_token_on_the_enterprise_host() {
    let (_guard, seen) = stub(copilot_usage_body()).await;
    let credential = PlanCredential {
        refresh: Some("gho_github"),
        enterprise_url: Some("https://ghe.example.com/"),
        ..oauth("tid=copilot;proxy-ep=proxy.example")
    };
    fetch_plan_quota("github-copilot", &credential)
        .await
        .expect("read")
        .expect("reading");
    let requests = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    assert_eq!(
        requests[0].url,
        "https://api.ghe.example.com/copilot_internal/user"
    );
    assert_eq!(
        requests[0].header_value("authorization"),
        Some("Bearer gho_github")
    );
}

#[test]
fn the_board_keeps_the_newest_reading_per_credential() {
    let reading = |at: u64, permille: u32| PlanQuota {
        provider: "board-test".to_owned(),
        plan: None,
        windows: vec![window("5h", Some(300), permille, None)],
        read_at_ms: at,
        source: QuotaSource::Headers,
    };
    let first = CredentialId::of("token-a");
    let second = CredentialId::of("token-b");
    let mut updates = QuotaBoard::subscribe();
    QuotaBoard::record(&first, reading(NOW + 10, 100));
    QuotaBoard::record(&first, reading(NOW, 900));
    QuotaBoard::record(&second, reading(NOW + 5, 300));
    assert_eq!(
        QuotaBoard::latest_for("board-test", &first),
        Some(reading(NOW + 10, 100))
    );
    assert_eq!(
        QuotaBoard::latest("board-test"),
        Some(reading(NOW + 10, 100))
    );
    assert_eq!(QuotaBoard::latest("board-none"), None);
    assert_eq!(updates.try_recv(), Ok(reading(NOW + 10, 100)));
    assert_eq!(updates.try_recv(), Ok(reading(NOW + 5, 300)));
}

#[test]
fn a_credential_id_keeps_no_token() {
    let token = "sk-ant-oat01-secret-token";
    let id = CredentialId::of(token);
    assert!(!format!("{id:?}").contains("secret"));
    assert_eq!(id, CredentialId::of(token));
    assert_ne!(id, CredentialId::of("sk-ant-oat01-other"));
}
