//! The `model.backups` chain (settings `model.backups`): the models a
//! dead end hands the session to, in the order the user listed them.
//!
//! A dead end is a model error no retry on the same model+credential
//! cures: a usage limit spent ([`Trigger::UsageLimit`], the known
//! usage-limit error texts, or the account book's every-account-limited
//! verdict), a sign-in the provider rejected ([`Trigger::AuthRejected`],
//! 401/403 and expired logins), or a model gone ([`Trigger::ModelGone`],
//! 404 / not found). Transient failures (a plain rate limit, timeouts,
//! 5xx) never trigger: the existing retry and park behaviors keep them.
//!
//! The pick ([`pick`]) walks the session model then the backups in order
//! and takes the first entry that is not tried, not dead, credentialed,
//! allowlisted, image-capable, and without a spent quota reading. All
//! dead: no pick, the existing error stands. A pick moves the session for
//! the rest of it (sticky) until `/model` resets the choice.
//!
//! The decision is this module's pure functions with Rust tests pinning
//! them (`trigger`, `quota_exhausted`, `pick`); the compiled fallback
//! core (`bend/fallback.bend`) still owns the generic walk past the
//! configured work models, which this chain preempts only for its own
//! triggers.

use eukhe_ai::auth::CREDENTIAL_STORE_FAILED;
use eukhe_ai::utils::retry::{is_budget_refusal, FailureFacts};
use eukhe_bend::rules::fallback::Why;
use eukhe_types::pi_ai::{AssistantMessage, Model, StopReason, StreamFailureKind};
use eukhe_types::quota::PlanQuota;

use super::provider::{LOGIN_EXPIRED_DIAGNOSTIC, MISSING_KEY_PREFIX};
use crate::models::registry::LOGIN_EXPIRED_REPORT;

#[cfg(test)]
#[path = "backups_tests.rs"]
mod tests;

/// Why a dead end took the model+credential out for the rest of the
/// session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trigger {
    /// The usage limit or plan quota is spent.
    UsageLimit,
    /// The provider rejected the credential (401/403, an expired login
    /// the refresh cannot cure).
    AuthRejected,
    /// The model no longer exists on the provider (404 / not found).
    ModelGone,
}

impl Trigger {
    /// The short reason of a switch line.
    #[must_use]
    pub fn text(self) -> &'static str {
        match self {
            Self::UsageLimit => "its usage limit was exhausted",
            Self::AuthRejected => "the provider rejected the sign-in",
            Self::ModelGone => "the model is gone",
        }
    }
}

/// Whether `failure` names a login the provider will not take (the same
/// wording the provider runtime's generic move reads).
fn login_rejected(failure: &AssistantMessage) -> bool {
    failure
        .diagnostics
        .iter()
        .flatten()
        .any(|diagnostic| diagnostic.kind.as_str() == LOGIN_EXPIRED_DIAGNOSTIC)
        || failure.error_message.as_deref().is_some_and(|error| {
            error.starts_with(MISSING_KEY_PREFIX)
                || error.contains(CREDENTIAL_STORE_FAILED)
                || error.contains(LOGIN_EXPIRED_REPORT)
        })
}

/// Whether `failure`'s newest stream failure names a model gone: a 404
/// status, or a provider error type that says not found (the same facts
/// the retry classifier reads; kept here so the retry module stays the
/// transient path's own).
fn model_gone(failure: &AssistantMessage) -> bool {
    let details = failure
        .diagnostics
        .iter()
        .flatten()
        .rev()
        .find(|diagnostic| diagnostic.kind.as_str() == "provider_stream_failure")
        .and_then(|diagnostic| diagnostic.details.as_ref());
    let gone_status = details
        .and_then(|details| details.get("status"))
        .and_then(serde_json::Value::as_u64)
        .is_some_and(|status| status == 404);
    let gone_type = details
        .and_then(|details| details.get("providerErrorType"))
        .and_then(serde_json::Value::as_str)
        .is_some_and(|error_type| error_type.contains("not_found"));
    gone_status || gone_type
}

/// The dead end of `failure` for its model+credential ([`Trigger`]);
/// `accounts_out` is why every account of its provider is out. A budget
/// refusal is the budget's, not the provider's; a failure that is no
/// error never triggers.
#[must_use]
pub fn trigger(failure: &AssistantMessage, accounts_out: Option<&Why>) -> Option<Trigger> {
    if is_budget_refusal(failure) || failure.stop_reason != StopReason::Error {
        return None;
    }
    if login_rejected(failure) {
        return Some(Trigger::AuthRejected);
    }
    match accounts_out {
        Some(Why::Quota { .. }) => return Some(Trigger::UsageLimit),
        Some(Why::Login) => return Some(Trigger::AuthRejected),
        Some(Why::Failed { .. } | Why::Unset) | None => {}
    }
    let facts = FailureFacts::of(failure)?;
    if model_gone(failure) {
        return Some(Trigger::ModelGone);
    }
    if matches!(
        facts.kind,
        Some(StreamFailureKind::Auth | StreamFailureKind::Permission)
    ) {
        return Some(Trigger::AuthRejected);
    }
    // The known usage-limit texts (the `limit` rule: usage limits,
    // `insufficient_quota`, billing) on a failure the retry ladder would
    // otherwise wait out or park.
    if facts.limit
        && matches!(
            facts.kind,
            None | Some(StreamFailureKind::RateLimit | StreamFailureKind::PaymentRequired)
        )
    {
        return Some(Trigger::UsageLimit);
    }
    None
}

/// Whether `reading`, `provider`'s newest quota reading, shows a window
/// spent: any window at its full thousand permille whose reset has not
/// passed. No reading: not exhausted.
#[must_use]
pub fn quota_exhausted(reading: Option<&PlanQuota>, now_ms: u64) -> bool {
    let Some(reading) = reading else {
        return false;
    };
    reading.windows.iter().any(|window| {
        window.used_permille >= 1000 && window.resets_at_ms.is_none_or(|reset| reset > now_ms)
    })
}

/// One chain entry's facts as [`pick`] reads them.
// Independent facts the pick reads one by one, not a state machine.
#[allow(clippy::struct_excessive_bools)]
pub struct Entry<'a> {
    pub model: &'a Model,
    /// The request already sat on it (its own model, or a move it made).
    pub tried: bool,
    /// A dead end took it out for the session.
    pub dead: bool,
    /// Its provider has a working authenticated credential.
    pub credentialed: bool,
    /// The allowlist permits it.
    pub allowed: bool,
    /// It serves the request's images.
    pub images: bool,
    /// Its newest quota reading shows a window spent.
    pub exhausted: bool,
}

impl Entry<'_> {
    /// Whether [`pick`] may take the entry.
    #[must_use]
    pub fn usable(&self) -> bool {
        !self.tried
            && !self.dead
            && self.credentialed
            && self.allowed
            && self.images
            && !self.exhausted
    }
}

/// The backup the session goes on with: the first usable entry in chain
/// order (the session model, then the `model.backups` entries as
/// listed). `None`: every entry is out; the existing error stands.
#[must_use]
pub fn pick<'a>(entries: &[Entry<'a>]) -> Option<&'a Model> {
    entries
        .iter()
        .find(|entry| entry.usable())
        .map(|entry| entry.model)
}

/// The one-line notice of a switch to `to` because `why`
/// ([`Trigger::text`]).
#[must_use]
pub fn switch_notice(to: &Model, why: Trigger) -> String {
    format!(
        "switched to {} ({}) because {}",
        to.id,
        to.provider,
        why.text()
    )
}
