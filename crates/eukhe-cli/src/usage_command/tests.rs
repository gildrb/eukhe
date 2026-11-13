use eukhe_ai::quota::{PlanQuota, QuotaError, QuotaSource, QuotaWindow};
use eukhe_core::platform::LocalTime;
use serde_json::json;

use super::{render_json, render_text, Answer};

/// Sat 2026-07-25 17:20:00 UTC.
const NOW: u64 = 1_785_000_000_000;
const HOUR: u64 = 3_600_000;

/// The test zone: UTC+2. Each instant the tests use, broken down.
fn clock(epoch_ms: u64) -> Option<LocalTime> {
    let at = |day: u32, hour: u32, minute: u32| LocalTime {
        year: 2026,
        month: if day > 31 { 8 } else { 7 },
        day: if day > 31 { day - 31 } else { day },
        hour,
        minute,
        second: 0,
        millisecond: 0,
        offset_seconds: 7_200,
    };
    match epoch_ms {
        NOW => Some(at(25, 19, 20)),
        ms if ms == NOW + 2 * HOUR + 15 * 60_000 => Some(at(25, 21, 35)),
        ms if ms == NOW + 51 * HOUR => Some(at(27, 22, 20)),
        ms if ms == NOW + 240 * HOUR => Some(at(35, 19, 20)),
        _ => None,
    }
}

fn window(label: &str, minutes: Option<u64>, permille: u32, resets: Option<u64>) -> QuotaWindow {
    QuotaWindow {
        label: label.to_owned(),
        window_minutes: minutes,
        used_permille: permille,
        resets_at_ms: resets,
    }
}

fn answers() -> Vec<(String, Answer)> {
    vec![
        (
            "anthropic".to_owned(),
            Answer::Quota(PlanQuota {
                provider: "anthropic".to_owned(),
                plan: None,
                windows: vec![
                    window("5h", Some(300), 370, Some(NOW + 2 * HOUR + 15 * 60_000)),
                    window("7d", Some(10_080), 640, Some(NOW + 51 * HOUR)),
                    window("7d opus", Some(10_080), 815, None),
                ],
                read_at_ms: NOW,
                source: QuotaSource::UsageEndpoint,
            }),
        ),
        (
            "github-copilot".to_owned(),
            Answer::Quota(PlanQuota {
                provider: "github-copilot".to_owned(),
                plan: Some("individual_pro".to_owned()),
                windows: vec![window("month premium", None, 820, Some(NOW + 240 * HOUR))],
                read_at_ms: NOW,
                source: QuotaSource::UsageEndpoint,
            }),
        ),
        ("openai".to_owned(), Answer::ApiKey),
        ("xai".to_owned(), Answer::NoQuota),
        (
            "openai-codex".to_owned(),
            Answer::Failed(QuotaError::Status { status: 401 }),
        ),
    ]
}

#[test]
fn text_lists_each_window_with_its_share_and_local_reset() {
    assert_eq!(
        render_text(&answers(), NOW, &clock),
        [
            "anthropic",
            "  5h       37% used, resets 21:35 (in 2h 15m)",
            "  7d       64% used, resets Mon 22:20 (in 2d 3h)",
            "  7d opus  81.5% used",
            "github-copilot (plan individual_pro)",
            "  month premium  82% used, resets 2026-08-04 19:20 (in 10d)",
            "openai: API key, no plan quota",
            "xai: no readable plan quota",
            "openai-codex: usage endpoint answered HTTP 401",
        ]
        .join("\n")
    );
}

#[test]
fn a_past_reset_reads_as_done() {
    let answers = vec![(
        "anthropic".to_owned(),
        Answer::Quota(PlanQuota {
            provider: "anthropic".to_owned(),
            plan: None,
            windows: vec![window("5h", Some(300), 1000, Some(NOW))],
            read_at_ms: NOW,
            source: QuotaSource::Headers,
        }),
    )];
    assert_eq!(
        render_text(&answers, NOW, &clock),
        "anthropic\n  5h  100% used, reset 19:20"
    );
}

#[test]
fn json_carries_each_reading_with_utc_resets_or_why_there_is_none() {
    let printed: serde_json::Value =
        serde_json::from_str(&render_json(&answers()[2..])).expect("json");
    assert_eq!(
        printed,
        json!({ "providers": [
            { "provider": "openai", "quota": null, "credential": "api_key" },
            { "provider": "xai", "quota": null },
            { "provider": "openai-codex", "quota": null, "error": "usage endpoint answered HTTP 401" },
        ] })
    );
    let printed: serde_json::Value =
        serde_json::from_str(&render_json(&answers()[..1])).expect("json");
    assert_eq!(
        printed,
        json!({ "providers": [
            { "provider": "anthropic", "quota": {
                "provider": "anthropic",
                "windows": [
                    { "label": "5h", "windowMinutes": 300, "usedPermille": 370,
                      "resetsAtMs": NOW + 8_100_000, "resetsAt": "2026-07-25T19:35:00.000Z" },
                    { "label": "7d", "windowMinutes": 10_080, "usedPermille": 640,
                      "resetsAtMs": NOW + 51 * HOUR, "resetsAt": "2026-07-27T20:20:00.000Z" },
                    { "label": "7d opus", "windowMinutes": 10_080, "usedPermille": 815 },
                ],
                "readAtMs": NOW,
                "source": "usage_endpoint",
            } },
        ] })
    );
}

#[test]
fn no_stored_login_says_so() {
    assert_eq!(render_text(&[], NOW, &clock), "No stored logins.");
}
