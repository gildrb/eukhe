//! Provider quota park on the durable path: the pure decision logic of the
//! old engine's `session_engine/provider_park.rs` (TS #2375 park mechanism)
//! over the pi-ai assistant message, plus the durable park state document.
//!
//! A quota failure (the `provider_stream_failure` diagnostic's `rate_limit`
//! kind) whose provider-reported reset exceeds the bounded wait ends the
//! chain cleanly and parks the session until the reset: the durable
//! `eukhe.quota_park` document on the root conversation holds the park, a
//! one-shot cron job (the scheduled-jobs path) wakes the session at the
//! reset, and the park/resume transitions land in the transcript as the old
//! engine's `provider_quota_park` / `provider_quota_resume` rows.
//!
//! The decision logic stays pure and clock-free (ported verbatim from the
//! old engine); the provider runtime owns the clock, the document, and the
//! wake job.

use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::types::LatestFork;
use eukhe_types::pi_ai::{AssistantMessage, AssistantMessageDiagnostic};
use serde::{Deserialize, Serialize};

/// Parks wake slightly after the reported reset so the window has actually
/// rolled over (TS `PROVIDER_RESUME_GRACE_MS`).
pub const PROVIDER_RESUME_GRACE_MS: u64 = 30_000;

/// Upper clamp for the configured park bound: one week per park, so
/// long-horizon resets still get probed (TS `MAX_PROVIDER_PAUSE_MS`).
pub const MAX_PROVIDER_PAUSE_MS: u64 = 7 * 86_400_000;

/// Transcript row recorded when a quota-blocked session parks until the
/// provider reset (TS `QUOTA_PARK_CUSTOM_ENTRY_TYPE`).
pub const PROVIDER_QUOTA_PARK_ENTRY: &str = "provider_quota_park";

/// Transcript row recorded when a parked session resumes (or when a wake had
/// to be dropped) (TS `QUOTA_RESUME_CUSTOM_ENTRY_TYPE`).
pub const PROVIDER_QUOTA_RESUME_ENTRY: &str = "provider_quota_resume";

/// Label for the durable one-shot wake that resumes a parked session (TS
/// `QUOTA_RESUME_CRON_LABEL`).
pub const QUOTA_RESUME_CRON_LABEL: &str = "quota-resume";

/// In-context marker delivered on resume (TS `QUOTA_RESUME_MARKER_TEXT`):
/// tells the model the pause happened and that it should continue the
/// interrupted task. The same text is the durable wake job's prompt, so
/// scheduler-delivered resumes read identically.
pub const QUOTA_RESUME_MARKER_TEXT: &str = "<provider_quota_resumed>\nThe provider usage limit that paused this session has been reported as reset; this resume is automatic (retry.provider.waitForUsage.pauseUntilReset). Continue the interrupted task from where it stopped.\n</provider_quota_resumed>";

/// The quota-park policy (TS `ProviderWaitPolicy`'s park keys, settings
/// `retry.provider.waitForUsage`): whether resets beyond the bounded wait
/// park the session, the per-park ceiling, and the per-episode park budget.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProviderParkPolicy {
    /// Park sessions for provider-reported resets beyond the bounded wait.
    /// Default true; `false` restores the pre-park immediate abort.
    pub pause_until_reset: bool,
    /// Abort bound: maximum single park duration. Default 24h; values above
    /// [`MAX_PROVIDER_PAUSE_MS`] are clamped so long-horizon resets still
    /// get probed.
    pub max_pause_ms: u64,
    /// Abort bound: maximum parks per quota episode (a successful model call
    /// while parked resets the episode). Default 8, the same anchor as the
    /// TS `maxParks`.
    pub max_parks: u32,
}

/// Default policy (TS `DEFAULT_PROVIDER_WAIT_POLICY`'s park keys): park on,
/// 24h per park, 8 parks per episode.
pub const DEFAULT_PROVIDER_PARK_POLICY: ProviderParkPolicy = ProviderParkPolicy {
    pause_until_reset: true,
    max_pause_ms: 86_400_000,
    max_parks: 8,
};

/// Why no park happened (TS `ProviderParkDecision`'s `none` reasons).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NoParkReason {
    /// `pauseUntilReset: false`: the pre-park immediate abort.
    Disabled,
    /// The episode's park budget is spent: abort exactly like the bounded
    /// wait the park replaced.
    ParkBudget,
    /// No provider-reported reset: the bounded wait keeps its abort behavior
    /// (a blind park would guess a wake time).
    NoReset,
}

/// Resolution of one park decision (TS `ProviderParkDecision`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProviderParkDecision {
    /// Park, then wake `resume_after_ms` from now.
    Park { resume_after_ms: u64 },
    /// No park; the give-up it would have replaced stands.
    None { reason: NoParkReason },
}

/// Park decision after a quota failure whose provider-reported reset exceeds
/// the bounded wait (TS `providerParkDecision`): pure and clock-free — the
/// caller owns the clock at the seam.
#[must_use]
pub fn provider_park_decision(
    parks_used: u32,
    reset_ms: Option<u64>,
    policy: &ProviderParkPolicy,
) -> ProviderParkDecision {
    if !policy.pause_until_reset {
        return ProviderParkDecision::None {
            reason: NoParkReason::Disabled,
        };
    }
    if parks_used >= policy.max_parks {
        return ProviderParkDecision::None {
            reason: NoParkReason::ParkBudget,
        };
    }
    let Some(reset_ms) = reset_ms else {
        return ProviderParkDecision::None {
            reason: NoParkReason::NoReset,
        };
    };
    let max_pause_ms = policy.max_pause_ms.min(MAX_PROVIDER_PAUSE_MS);
    ProviderParkDecision::Park {
        resume_after_ms: reset_ms
            .saturating_add(PROVIDER_RESUME_GRACE_MS)
            .min(max_pause_ms),
    }
}

/// The `provider_stream_failure` diagnostic of a failed assistant message,
/// when it carries one.
fn stream_failure_diagnostic(message: &AssistantMessage) -> Option<&AssistantMessageDiagnostic> {
    message
        .diagnostics
        .as_ref()?
        .iter()
        .find(|diagnostic| diagnostic.kind == "provider_stream_failure")
}

/// Whether a failed assistant message is quota-classified (the TS wait class
/// `usage`: 429 / usage-limit rejections): the `provider_stream_failure`
/// diagnostic's `rate_limit` kind.
#[must_use]
pub fn is_quota_block_failure(message: &AssistantMessage) -> bool {
    stream_failure_diagnostic(message)
        .and_then(|diagnostic| diagnostic.details.as_ref())
        .and_then(|details| details.get("kind"))
        .and_then(serde_json::Value::as_str)
        == Some("rate_limit")
}

/// The provider-reported reset of a quota failure, in milliseconds
/// (`retryAfterMs` on the stream-failure diagnostic — the codex usage-limit
/// parse and the `Retry-After` header both land there).
#[must_use]
pub fn quota_failure_reset_ms(message: &AssistantMessage) -> Option<u64> {
    stream_failure_diagnostic(message)?
        .details
        .as_ref()?
        .get("retryAfterMs")
        .and_then(serde_json::Value::as_u64)
}

fn iso_ms(resume_at_ms: u64) -> String {
    crate::session::manager::format_iso(i64::try_from(resume_at_ms).unwrap_or(i64::MAX))
}

/// The parked status text surfaced as the chain's final error (TS
/// `_parkForQuotaReset`: `"<abort>. Session parked until <time> and will
/// resume automatically (…): <error>"`): the give-up sentence stays this
/// port's own (the TS abort names the wait loop this port lacks), the parked
/// sentence is the TS wording.
#[must_use]
pub fn quota_parked_final_error(abort: &str, resume_at_ms: u64, error: &str) -> String {
    format!(
        "{abort}. Session parked until {} and will resume automatically (retry.provider.waitForUsage.pauseUntilReset): {error}",
        iso_ms(resume_at_ms)
    )
}

/// The already-parked status of a live park this failure re-hit (the old
/// engine's already-parked arm): the turn ends without a retry.
#[must_use]
pub fn quota_already_parked_final_error(resume_at_ms: u64, error: &str) -> String {
    format!(
        "Session is parked until {} waiting for the provider usage reset; this turn ended without a retry: {error}",
        iso_ms(resume_at_ms)
    )
}

/// The park state of one conversation: the durable `eukhe.quota_park`
/// document (the old engine's in-memory `QuotaParkState`, persisted). A
/// fork starts unparked.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ParkDocState {
    /// Wall-clock wake time of the park (epoch ms).
    pub resume_at_ms: u64,
    /// Parks consumed in the episode when it parked.
    pub park_count: u32,
    /// Id of the durable one-shot wake job.
    pub job_id: Option<String>,
    /// The provider whose quota blocked the episode.
    pub provider: Option<String>,
    /// Wake re-arms spent by a park whose wake fired without resuming and
    /// without a reported reset (TS `_recoverQuotaParkWake`).
    pub wake_retries: u32,
}

/// The durable quota-park document of the root conversation. The default
/// state is "no park"; the runtime clears a park by resetting the document
/// to the default.
pub static PARK_DOC: ConversationDoc<ParkDocState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.quota_park",
        version: 1,
        initial: ParkDocState::default,
        migrate: None,
        checkpoint_when: Some(|_, _, _| false),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.quota_park has a valid version"),
};

/// The transcript row data of one park transition (the old
/// `provider_quota_park` entry's payload, same keys).
#[must_use]
pub fn park_entry_data(
    resume_at_ms: u64,
    park_count: u32,
    job_id: Option<&str>,
    provider: Option<&str>,
) -> serde_json::Value {
    serde_json::json!({
        "resumeAt": iso_ms(resume_at_ms),
        "parkCount": park_count,
        "jobId": job_id,
        "provider": provider,
    })
}

/// The transcript row data of one resume (or drop) transition (the old
/// `provider_quota_resume` entry's payload, same keys).
#[must_use]
pub fn resume_entry_data(outcome: &str) -> serde_json::Value {
    serde_json::json!({ "outcome": outcome })
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::pi_ai::{JsonObject, StopReason, Usage};

    /// A failed assistant message with one `provider_stream_failure`
    /// diagnostic whose `details` are the recorded payload.
    fn failure_with_details(details: JsonObject) -> AssistantMessage {
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
            error_message: Some("429 rate limit".to_owned()),
            raw_stop_reason: None,
            end_turn: None,
            timestamp: 0,
        }
    }

    fn quota_failure(reset_ms: Option<u64>) -> AssistantMessage {
        let mut details = JsonObject::new();
        details.insert("kind".to_owned(), serde_json::json!("rate_limit"));
        if let Some(reset_ms) = reset_ms {
            details.insert("retryAfterMs".to_owned(), serde_json::json!(reset_ms));
        }
        failure_with_details(details)
    }

    fn overload_failure() -> AssistantMessage {
        let mut details = JsonObject::new();
        details.insert("kind".to_owned(), serde_json::json!("overloaded"));
        let mut message = failure_with_details(details);
        message.error_message = Some("503 overloaded".to_owned());
        message
    }

    #[test]
    fn parks_until_the_reported_reset_plus_grace() {
        assert_eq!(
            provider_park_decision(0, Some(3_600_000), &DEFAULT_PROVIDER_PARK_POLICY),
            ProviderParkDecision::Park {
                resume_after_ms: 3_600_000 + PROVIDER_RESUME_GRACE_MS
            }
        );
    }

    #[test]
    fn clamps_a_long_horizon_reset_to_the_pause_ceiling() {
        assert_eq!(
            provider_park_decision(0, Some(90 * 86_400_000), &DEFAULT_PROVIDER_PARK_POLICY),
            ProviderParkDecision::Park {
                resume_after_ms: DEFAULT_PROVIDER_PARK_POLICY.max_pause_ms
            }
        );
    }

    #[test]
    fn declines_when_disabled_spent_or_resetless() {
        assert_eq!(
            provider_park_decision(
                0,
                Some(1000),
                &ProviderParkPolicy {
                    pause_until_reset: false,
                    ..DEFAULT_PROVIDER_PARK_POLICY
                }
            ),
            ProviderParkDecision::None {
                reason: NoParkReason::Disabled
            }
        );
        assert_eq!(
            provider_park_decision(
                DEFAULT_PROVIDER_PARK_POLICY.max_parks,
                Some(1000),
                &DEFAULT_PROVIDER_PARK_POLICY
            ),
            ProviderParkDecision::None {
                reason: NoParkReason::ParkBudget
            }
        );
        assert_eq!(
            provider_park_decision(0, None, &DEFAULT_PROVIDER_PARK_POLICY),
            ProviderParkDecision::None {
                reason: NoParkReason::NoReset
            }
        );
    }

    #[test]
    fn classifies_quota_failures_by_diagnostic_kind() {
        assert!(is_quota_block_failure(&quota_failure(Some(1000))));
        assert!(!is_quota_block_failure(&overload_failure()));
        assert_eq!(
            quota_failure_reset_ms(&quota_failure(Some(1000))),
            Some(1000)
        );
        assert_eq!(quota_failure_reset_ms(&quota_failure(None)), None);
        assert_eq!(quota_failure_reset_ms(&overload_failure()), None);
    }

    #[test]
    fn parked_sentences_name_the_resume_time() {
        let parked =
            quota_parked_final_error("Provider requested a wait", 1_768_000_000_000, "429");
        assert!(
            parked.contains("Session parked until 2026-01-09T23:06:40.000Z and will resume automatically (retry.provider.waitForUsage.pauseUntilReset): 429"),
            "{parked}"
        );
        let already = quota_already_parked_final_error(1_768_000_000_000, "429");
        assert!(
            already.contains("Session is parked until 2026-01-09T23:06:40.000Z waiting for the provider usage reset"),
            "{already}"
        );
    }

    #[test]
    fn entry_data_keeps_the_old_row_keys() {
        assert_eq!(
            park_entry_data(1_768_000_000_000, 2, Some("job-7"), Some("prime-inference")),
            serde_json::json!({
                "resumeAt": "2026-01-09T23:06:40.000Z",
                "parkCount": 2,
                "jobId": "job-7",
                "provider": "prime-inference",
            })
        );
        assert_eq!(
            resume_entry_data("wake"),
            serde_json::json!({ "outcome": "wake" })
        );
    }
}
