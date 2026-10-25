//! Transient-error classification and the wait before a retry.
//!
//! A failed message is classified by what its stream failure recorded
//! first: the HTTP status, then the typed failure kind. Its text decides
//! only when the failure recorded neither, and then a status code or a
//! transport word matches only as a whole word. The wait before a retry
//! is never shorter than the server's requested wait; when the server asks
//! for more than the cap, no retry goes out early: the failure surfaces at
//! once with the server's time, as the HTTP layer
//! ([`super::provider_retry`]) reports it. The Bend model `bend/retry.bend`
//! makes the same decisions; `laws/retry.bend` states their laws.

use eukhe_bend::rules::err_text::{self, Rule};
use eukhe_bend::rules::retry::{self as rules, Cause, Facts, Wait, WaitInput};
use eukhe_bend::wire::NAT_MAX;
use eukhe_bend::{expect_core, Entry};
use eukhe_types::pi_ai::{AssistantMessage, StopReason, StreamFailureKind};

use super::js::number_to_js_string;
use super::stream_failure::RepeatedLines;

/// The diagnostic type of a failure the quota park ended: the session
/// waits for the provider's usage reset, so the failure is never retried.
pub const QUOTA_PARK_DIAGNOSTIC: &str = "provider_quota_park";

/// The wait parameters of a retry: the step doubles from `base_delay_ms`
/// each retry, and `max_agent_delay_ms` caps both the step and the
/// server's requested wait (default [`DEFAULT_MAX_AGENT_RETRY_DELAY_MS`];
/// `0` turns the cap on the server's wait off, as in the HTTP layer).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RetryDelay {
    pub base_delay_ms: f64,
    pub max_agent_delay_ms: Option<f64>,
}

/// Default cap of an agent-level retry delay.
pub const DEFAULT_MAX_AGENT_RETRY_DELAY_MS: f64 = 60_000.0;

/// A duration in ms as the wait decision reads it: whole ms, rounded up
/// (a wait never shortens), `0` for a negative or NaN value, saturated
/// at the wire's largest Nat ([`NAT_MAX`]).
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn whole_ms(ms: f64) -> u64 {
    // A NaN casts to 0; the cast of a whole value in [0, 10^14) is exact.
    ms.ceil().clamp(0.0, ms_f64(NAT_MAX)) as u64
}

/// A whole-ms duration (at most [`NAT_MAX`]) as the f64 the callers sleep
/// on.
#[allow(clippy::cast_precision_loss)] // At most 10^14-1: exact.
fn ms_f64(ms: u64) -> f64 {
    ms as f64
}

/// The server-requested wait recorded on a failed message (the
/// `retryAfterMs` of its newest `provider_stream_failure` diagnostic: a
/// `Retry-After` header or a reset time), in milliseconds.
#[must_use]
pub fn server_retry_after_ms(message: &AssistantMessage) -> Option<f64> {
    message
        .diagnostics
        .iter()
        .flatten()
        .rev()
        .filter(|diagnostic| diagnostic.kind == "provider_stream_failure")
        .find_map(|diagnostic| diagnostic.details.as_ref()?.get("retryAfterMs")?.as_f64())
}

/// When the retry of a failed message may go out.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum RetryWait {
    /// After this many milliseconds: never before the server's wait.
    After(f64),
    /// The server asked for `server_ms`, more than the cap `cap_ms`: a
    /// retry before the server's time cannot succeed, so none goes out
    /// and the failure surfaces at once with the server's time
    /// ([`RetryWait::refusal`]).
    Refused { server_ms: f64, cap_ms: f64 },
}

impl RetryWait {
    /// The error of a refused wait: the server's time and the cap, then
    /// the failure's own text (`error`). The HTTP layer reports a refused
    /// server wait in the same words.
    #[must_use]
    pub fn refusal(server_ms: f64, cap_ms: f64, error: &str) -> String {
        format!(
            "Server requested {}s retry delay (max: {}s). {error}",
            number_to_js_string((server_ms / 1000.0).ceil()),
            number_to_js_string((cap_ms / 1000.0).ceil()),
        )
    }
}

/// The wait before retry `attempt` (1-indexed) of the failed `message`
/// (omp2 `TransportRetryLayer`), decided by the compiled Bend core
/// (`bend/retry.bend` `retry_wait`, `laws/retry.bend`): a
/// full-jitter draw under the step, where the step is `base_delay_ms *
/// 2^(attempt-1)` capped at `max_agent_delay_ms`, so agents that hit the
/// same limit together do not retry together; never shorter than the
/// server's requested wait, and [`RetryWait::Refused`] when that wait is
/// above the cap.
#[must_use]
pub fn retry_wait(policy: RetryDelay, attempt: u32, message: &AssistantMessage) -> RetryWait {
    let input = WaitInput {
        base_ms: whole_ms(policy.base_delay_ms),
        attempt,
        cap_ms: whole_ms(
            policy
                .max_agent_delay_ms
                .unwrap_or(DEFAULT_MAX_AGENT_RETRY_DELAY_MS),
        ),
        // Uniform in [0, 2^46): the jitter is the draw modulo the step.
        draw: rand::random::<u64>() >> 18,
        server_ms: server_retry_after_ms(message).map(whole_ms),
    };
    match expect_core(Entry::Retry, rules::wait(input)) {
        Wait::After(ms) => RetryWait::After(ms_f64(ms)),
        Wait::Refused { server_ms, cap_ms } => RetryWait::Refused {
            server_ms: ms_f64(server_ms),
            cap_ms: ms_f64(cap_ms),
        },
    }
}

/// The details of the newest `provider_stream_failure` diagnostic of
/// `message` (the [`StreamFailureInfo`](super::stream_failure::StreamFailureInfo)
/// its stream failed with).
fn newest_stream_failure(
    message: &AssistantMessage,
) -> Option<&serde_json::Map<String, serde_json::Value>> {
    message
        .diagnostics
        .iter()
        .flatten()
        .rev()
        .find(|diagnostic| diagnostic.kind == "provider_stream_failure")?
        .details
        .as_ref()
}

/// What the stream of `message` repeated, when its newest stream failure
/// is the repetition guard's cut (`stream_repeating`).
#[must_use]
pub fn repeated_lines(message: &AssistantMessage) -> Option<RepeatedLines> {
    let repeated = newest_stream_failure(message)?.get("repeated")?;
    serde_json::from_value(repeated.clone()).ok()
}

/// The idle deadline (ms) the stream of `message` stalled under, when its
/// newest stream failure is a stall (`stream_stalled`).
#[must_use]
pub fn stalled_idle_ms(message: &AssistantMessage) -> Option<u64> {
    let details = newest_stream_failure(message)?;
    let stalled = details.get("kind")?.as_str()? == StreamFailureKind::StreamStalled.as_str();
    stalled
        .then(|| details.get("idleTimeoutMs")?.as_u64())
        .flatten()
}

/// A recorded failure kind as the compiled core reads it.
const fn cause(kind: StreamFailureKind) -> Cause {
    match kind {
        StreamFailureKind::Refusal => Cause::Refusal,
        StreamFailureKind::Safety => Cause::Safety,
        StreamFailureKind::PaymentRequired => Cause::PaymentRequired,
        StreamFailureKind::Overloaded => Cause::Overloaded,
        StreamFailureKind::RateLimit => Cause::RateLimit,
        StreamFailureKind::ServerError => Cause::ServerError,
        StreamFailureKind::Auth => Cause::Auth,
        StreamFailureKind::Permission => Cause::Permission,
        StreamFailureKind::InvalidRequest => Cause::InvalidRequest,
        StreamFailureKind::MalformedResponse => Cause::MalformedResponse,
        StreamFailureKind::StreamDrop => Cause::StreamDrop,
        StreamFailureKind::StreamStalled => Cause::StreamStalled,
        StreamFailureKind::StreamRepeating => Cause::StreamRepeating,
        StreamFailureKind::Unknown => Cause::Unknown,
    }
}

/// What the classifier reads of a failed message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FailureFacts {
    /// The quota park ended the failure ([`QUOTA_PARK_DIAGNOSTIC`]).
    pub parked: bool,
    /// Its text or provider error type names a quota, billing, or
    /// admission limit, or the HTTP layer's refused server wait.
    pub limit: bool,
    /// The HTTP status its newest stream failure recorded.
    pub status: Option<u16>,
    /// The typed kind its newest stream failure recorded.
    pub kind: Option<StreamFailureKind>,
    /// Its text names a transient failure, word for word.
    pub transient_text: bool,
}

impl FailureFacts {
    /// The facts of `message`; `None` when it did not fail.
    #[must_use]
    pub fn of(message: &AssistantMessage) -> Option<Self> {
        if message.stop_reason != StopReason::Error {
            return None;
        }
        let parked = message
            .diagnostics
            .iter()
            .flatten()
            .any(|diagnostic| diagnostic.kind == QUOTA_PARK_DIAGNOSTIC);
        let failure = newest_stream_failure(message);
        let text = message.error_message.as_deref().unwrap_or_default();
        let error_type = failure
            .and_then(|details| details.get("providerErrorType")?.as_str())
            .unwrap_or_default();
        let limit = err_text::holds(Rule::Limit, &[text, error_type]);
        let status = failure
            .and_then(|details| details.get("status")?.as_u64())
            .and_then(|status| u16::try_from(status).ok());
        let kind = failure
            .and_then(|details| details.get("kind")?.as_str())
            .and_then(StreamFailureKind::parse);
        Some(Self {
            parked,
            limit,
            status,
            kind,
            transient_text: err_text::holds(Rule::Transient, &[text]),
        })
    }

    /// Whether a retry may cure the failure, decided by the compiled Bend
    /// core (`bend/retry.bend` `retryable`, `laws/retry.bend`):
    /// never a parked failure or a limit; else by its recorded status
    /// (408, 409, 429, 500 and above); else by its typed kind; else by its
    /// text.
    #[must_use]
    pub fn retryable(self) -> bool {
        let facts = Facts {
            parked: self.parked,
            limit: self.limit,
            status: self.status,
            kind: self.kind.map(cause),
            transient_text: self.transient_text,
        };
        expect_core(Entry::Retry, rules::retryable(facts))
    }
}

/// Whether a failed assistant message is a transient provider or
/// transport failure ([`FailureFacts::retryable`]). This is
/// classification only: callers handle context overflow first and apply
/// their own retry budget and wait ([`retry_wait`]).
#[must_use]
pub fn is_retryable_assistant_error(message: &AssistantMessage) -> bool {
    FailureFacts::of(message).is_some_and(FailureFacts::retryable)
}

#[cfg(test)]
mod tests;
