//! The `model.backups` chain's decisions: the trigger reads the dead ends
//! and skips the transient, the quota reading reads the window resets,
//! and the pick takes the first usable entry in chain order.

use super::super::resolve_model_backup_references;
use super::*;
use crate::settings::SettingsManager;
use eukhe_types::cvar::Command;
use eukhe_types::pi_ai::{AssistantMessageDiagnostic, JsonObject, Modality, ModelCost, Usage};
use eukhe_types::quota::{QuotaSource, QuotaWindow};

fn model(provider: &str, id: &str) -> Model {
    Model {
        id: id.to_owned(),
        name: format!("{provider} {id}"),
        api: "faux".to_owned(),
        provider: provider.to_owned(),
        base_url: String::new(),
        input: vec![Modality::Text],
        input_limits: None,
        cost: ModelCost::default(),
        headers: None,
        model_type: None,
        reasoning: false,
        thinking_level_map: None,
        prompt_cache: None,
        context_window: 100_000,
        max_tokens: 4_096,
        sampling_params: None,
        sampling_params_by_thinking_level: None,
        compat: None,
        featured: None,
    }
}

fn failed(error: &str, details: JsonObject) -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: "faux".to_owned(),
        provider: "faux".into(),
        model: "faux-1".into(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: Some(vec![AssistantMessageDiagnostic {
            kind: "provider_stream_failure".to_owned(),
            timestamp: 0,
            error: None,
            details: Some(details),
        }]),
        usage: Usage::default(),
        stop_reason: StopReason::Error,
        deferred: None,
        error_message: Some(error.to_owned()),
        raw_stop_reason: None,
        end_turn: None,
        timestamp: 0,
        duration_ms: None,
        timing: None,
    }
}

fn failure_of_kind(error: &str, kind: &str, status: u16) -> AssistantMessage {
    let mut details = JsonObject::new();
    details.insert("kind".to_owned(), serde_json::json!(kind));
    details.insert("status".to_owned(), serde_json::json!(status));
    failed(error, details)
}

/// A usage-limit error (the known `subscription_sharing_usage_limit_exceeded`
/// wording, a known dead-end text) triggers; a plain 429 rate limit, a
/// 5xx, and a timeout never do; 401 and 403 auth rejections and a 404
/// model gone each trigger their own cause; a spent payment balance is a
/// usage limit; the account book's verdict triggers on its own.
#[test]
fn the_trigger_reads_the_dead_ends_and_skips_the_transient() {
    let limit = {
        let mut details = JsonObject::new();
        details.insert("kind".to_owned(), serde_json::json!("rate_limit"));
        failed(
            r#"OpenAI API error (429): {"code":"subscription_sharing_usage_limit_exceeded","message":"Usage limit reached."}"#,
            details,
        )
    };
    assert_eq!(trigger(&limit, None), Some(Trigger::UsageLimit));
    assert_eq!(
        trigger(
            &failure_of_kind("403 oauth_not_allowed_for_organization", "permission", 403),
            None
        ),
        Some(Trigger::AuthRejected)
    );
    assert_eq!(
        trigger(&failure_of_kind("401 invalid x-api-key", "auth", 401), None),
        Some(Trigger::AuthRejected)
    );
    assert_eq!(
        trigger(
            &failure_of_kind("model_not_found: no such model", "invalid_request", 404),
            None
        ),
        Some(Trigger::ModelGone)
    );
    assert_eq!(
        trigger(
            &failure_of_kind("429 rate limit exceeded, retry later", "rate_limit", 429),
            None
        ),
        None
    );
    assert_eq!(
        trigger(
            &failure_of_kind("503 Service Unavailable", "server_error", 503),
            None
        ),
        None
    );
    assert_eq!(
        trigger(
            &failure_of_kind("Request timed out after 30000ms", "unknown", 0),
            None
        ),
        None
    );
    let payment = failure_of_kind(
        "billing: available balance is empty",
        "payment_required",
        402,
    );
    assert_eq!(trigger(&payment, None), Some(Trigger::UsageLimit));
    assert_eq!(
        trigger(
            &failure_of_kind("429 rate limit", "rate_limit", 429),
            Some(&Why::Quota { until_ms: 7 })
        ),
        Some(Trigger::UsageLimit)
    );
    assert_eq!(
        trigger(
            &failure_of_kind("429 rate limit", "rate_limit", 429),
            Some(&Why::Login)
        ),
        Some(Trigger::AuthRejected)
    );
}

/// A window at its full thousand permille is spent while its reset
/// holds; a reading with room left, and a spent window whose reset
/// passed, are not.
#[test]
fn quota_exhausted_reads_the_windows_resets() {
    let window = |used_permille: u32, resets_at_ms: Option<u64>| QuotaWindow {
        label: "5h".to_owned(),
        window_minutes: Some(300),
        used_permille,
        resets_at_ms,
    };
    let reading = |windows: Vec<QuotaWindow>| PlanQuota {
        provider: "p".to_owned(),
        plan: None,
        windows,
        read_at_ms: 0,
        source: QuotaSource::Headers,
    };
    let now = 1_000;
    assert!(quota_exhausted(
        Some(&reading(vec![window(1_000, Some(2_000))])),
        now
    ));
    assert!(!quota_exhausted(
        Some(&reading(vec![window(999, Some(2_000))])),
        now
    ));
    assert!(!quota_exhausted(
        Some(&reading(vec![window(1_000, Some(500))])),
        now
    ));
    assert!(!quota_exhausted(None, now));
}

/// The pick takes the first usable entry in chain order: the session
/// model and tried entries never; a dead one, one without credentials, a
/// text-only one for an image request, and one with a spent quota window
/// each skip; all dead: no pick.
#[test]
fn the_pick_takes_the_first_usable_entry_in_chain_order() {
    fn entry(model: &Model, tried: bool, dead: bool, credentialed: bool) -> Entry<'_> {
        Entry {
            model,
            tried,
            dead,
            credentialed,
            allowed: true,
            images: true,
            exhausted: false,
        }
    }
    let [primary, first, second, third] = [
        model("p", "primary"),
        model("b", "first"),
        model("c", "second"),
        model("d", "third"),
    ];
    // Backup 1 on a dead end of the session model.
    assert_eq!(
        pick(&[
            entry(&primary, true, false, true),
            entry(&first, false, false, true),
            entry(&second, false, false, true),
        ]),
        Some(&first)
    );
    // A backup with no credential skips to the next.
    assert_eq!(
        pick(&[
            entry(&primary, true, false, true),
            entry(&first, false, false, false),
            entry(&second, false, false, true),
        ]),
        Some(&second)
    );
    // Dead, image-less and quota-spent entries skip; all dead: none.
    let unusable = entry(&first, false, true, true);
    let mut no_images = entry(&second, false, false, true);
    no_images.images = false;
    let mut spent = entry(&third, false, false, true);
    spent.exhausted = true;
    assert_eq!(
        pick(&[
            entry(&primary, true, false, true),
            unusable,
            no_images,
            spent,
        ]),
        None
    );
    let dead_first = entry(&first, false, true, true);
    assert_eq!(
        pick(&[entry(&primary, true, false, true), dead_first]),
        None
    );
}

/// The notice is one line in the switch's shape.
#[test]
fn the_notice_is_one_line() {
    assert_eq!(
        switch_notice(&model("zai", "glm-5.3-flash"), Trigger::UsageLimit),
        "switched to glm-5.3-flash (zai) because its usage limit was exhausted"
    );
    assert_eq!(
        switch_notice(&model("zai", "glm-5.3-flash"), Trigger::AuthRejected),
        "switched to glm-5.3-flash (zai) because the provider rejected the sign-in"
    );
}

/// The chain references read the setting against the catalog: an entry
/// that names no catalog model, that is the session model, or that
/// repeats an earlier entry drops with a diagnostic each; the rest keep
/// the listed order; the unset setting is empty.
#[test]
fn the_references_resolve_against_the_catalog() {
    let dir = tempfile::tempdir().expect("tempdir");
    let cwd = dir.path().join("work");
    let agent = dir.path().join("agent");
    std::fs::create_dir_all(&cwd).expect("cwd");
    std::fs::create_dir_all(&agent).expect("agent");
    let mut settings = SettingsManager::create(&cwd, &agent);
    let all = [
        model("p", "primary"),
        model("b", "first"),
        model("c", "second"),
    ];

    let (references, diagnostics) =
        resolve_model_backup_references(&settings, &all, Some(("p", "primary")));
    assert!(references.is_empty());
    assert!(diagnostics.is_empty());

    settings
        .run_global(&[Command::Set {
            id: "model.backups".to_owned(),
            value: "b/first, missing/nope, p/primary, b/first, c/second".to_owned(),
        }])
        .expect("set model.backups");
    let (references, diagnostics) =
        resolve_model_backup_references(&settings, &all, Some(("p", "primary")));
    assert_eq!(references, ["b/first".to_owned(), "c/second".to_owned()]);
    assert_eq!(
        diagnostics,
        [
            "model.backups: no model \"missing/nope\" in the catalog; entry dropped".to_owned(),
            "model.backups: \"p/primary\" is the session model; entry dropped".to_owned(),
            "model.backups: \"b/first\" repeats an earlier entry; entry dropped".to_owned(),
        ]
    );
}
