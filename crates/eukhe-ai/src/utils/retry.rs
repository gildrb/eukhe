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
//! makes the same decisions; `LAWS.bend` section `retry` states their laws.

use std::sync::LazyLock;

use regex::Regex;

use eukhe_types::pi_ai::{AssistantMessage, StopReason, StreamFailureKind};

use super::js::number_to_js_string;
use super::stream_failure::RepeatedLines;

fn build_provider_error_pattern(patterns: &[&str]) -> Regex {
    let pattern = format!("(?i){}", patterns.join("|"));
    Regex::new(&pattern).unwrap_or_else(|error| panic!("invalid provider error pattern: {error}"))
}

static NON_RETRYABLE_PROVIDER_LIMIT_ERROR_PATTERN: LazyLock<Regex> = LazyLock::new(|| {
    build_provider_error_pattern(&[
        // OpenCode Go/free-tier limits returned as 429 JSON error types by
        // OpenCode's Zen API: subscription/account limits, not transient throttles.
        "GoUsageLimitError",
        "FreeUsageLimitError",
        // OpenCode Go subscription-limit text.
        "Monthly usage limit reached",
        "available balance",
        // Generic quota/budget/billing exhaustion (`insufficient_quota` is OpenAI's code).
        "insufficient_quota",
        "out of budget",
        "quota exceeded",
        "billing",
        // Sign in with ChatGPT: the subscription's shared usage limit (resets after hours).
        "subscription_sharing_usage_limit_exceeded",
        // eukhe's own provider admission (`providerMaxQueued`): a full wait
        // queue fails fast; a retry would only lengthen it.
        "provider admission queue is full",
        // The HTTP layer's refusal of a server wait above the cap
        // (`provider_retry`, the codex client): a retry before the
        // server's time cannot succeed.
        r"server requested \d+s retry delay",
    ])
});

/// Transient failures by their text, for a failure that recorded no HTTP
/// status and no typed kind. Status codes and transport words match only
/// as whole words: `524` in `5242880` or `timeout` in `timeouts_ms` is no
/// match.
static RETRYABLE_PROVIDER_ERROR_PATTERN: LazyLock<Regex> = LazyLock::new(|| {
    build_provider_error_pattern(&[
        // Generic provider load, HTTP status, and server-side transient failures.
        r"\boverloaded",
        r"\bserver_busy\b",
        "servers are currently busy",
        "currently experiencing high demand",
        "model is at capacity",
        r"\brate.?limit",
        r"\btoo many requests\b",
        r"\b(?:408|429|500|502|503|504|520|524|529)\b",
        r"\bservice.?unavailable\b",
        r"\bserver.?error\b",
        r"\binternal.?error\b",
        // Wrapper/provider text for transient upstream failures (OpenRouter #2264).
        r"\bprovider.?returned.?error\b",
        "exceeded request buffer limit while retrying upstream",
        // Network, proxy, and fetch transport failures (#733, #3317).
        r"\bnetwork.?error\b",
        r"\bconnection.?error\b",
        r"\bconnection.?refused\b",
        r"\bconnection.?lost\b",
        "other side closed",
        r"\bfetch failed\b",
        r"\bgetaddrinfo\b",
        r"\bENOTFOUND\b",
        r"\bEAI_AGAIN\b",
        r"\bupstream.?connect",
        "reset before headers",
        r"\bsocket hang up\b",
        "socket connection was closed",
        r"\btimed? ?out\b",
        r"\bterminated\b",
        // WebSocket close/error text.
        r"\bwebsocket.?closed\b",
        r"\bwebsocket.?error\b",
        // Premature stream endings (#4433, #3594).
        r"\bended without\b",
        "stream ended before message_stop",
        "stream ended before a terminal response event",
        "http2 request did not get a response",
        // HTTP/2 session died before the request was sent (#10379).
        "pending stream has been canceled",
        // Explicit retry guidance emitted mid-stream (#6019).
        "you can retry your request",
        "try your request again",
        "please retry your request",
        // gRPC based providers (e.g. NVIDIA NIM).
        r"\bResourceExhausted\b",
        // Sign in with ChatGPT: usage or user data temporarily unavailable.
        r"\bsubscription_sharing_usage_unavailable\b",
        r"\bsubscription_sharing_user_unavailable\b",
    ])
});

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

/// The largest `Nat` of the Bend core's wire (10^14-1, below the
/// runtime's 2^48-1): a duration past it saturates there (over 3000
/// years).
const NAT_MAX: u64 = 99_999_999_999_999;

/// A duration in ms as the wait decision reads it: whole ms, rounded up
/// (a wait never shortens), `0` for a negative or NaN value, saturated
/// at [`NAT_MAX`].
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

/// What the wait of a retry reads, as plain data (whole ms, each at most
/// the wire's largest Nat).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WaitInput {
    /// The policy's base step (`base_delay_ms`).
    pub base_ms: u64,
    /// The retry: 1 for the first.
    pub attempt: u32,
    /// The policy's cap (`max_agent_delay_ms`; `0`: no cap on the
    /// server's wait).
    pub cap_ms: u64,
    /// A draw uniform in [0, 2^46): the jitter is the draw modulo the step.
    pub draw: u64,
    /// The server's requested wait, if any.
    pub server_ms: Option<u64>,
}

impl RetryWait {
    /// The wait of a retry (`bend/retry.bend` `retry_wait`): the step is
    /// the base doubled per retry before this one, at most the cap; the
    /// jitter is the draw modulo the step (0 for a step of 0); never
    /// before the server's wait; a server wait above a positive cap
    /// refuses the retry.
    #[must_use]
    pub fn decide(input: WaitInput) -> Self {
        let mut step = input.base_ms.min(input.cap_ms);
        for _ in 1..input.attempt {
            if step == 0 || step > input.cap_ms - step {
                step = if step == 0 { 0 } else { input.cap_ms };
                break;
            }
            step += step;
        }
        let jitter = if step == 0 { 0 } else { input.draw % step };
        match input.server_ms {
            Some(server) if input.cap_ms > 0 && server > input.cap_ms => Self::Refused {
                server_ms: ms_f64(server),
                cap_ms: ms_f64(input.cap_ms),
            },
            Some(server) => Self::After(ms_f64(jitter.max(server))),
            None => Self::After(ms_f64(jitter)),
        }
    }

    /// The wait of a retry whose backoff drew `jittered` ms, after a
    /// failure whose server asked for `server` ms (none: no wait), under
    /// the cap `cap_ms` (`0`: no cap).
    #[must_use]
    pub fn of(jittered: f64, server: Option<f64>, cap_ms: f64) -> Self {
        match server {
            Some(server_ms) if cap_ms > 0.0 && server_ms > cap_ms => {
                Self::Refused { server_ms, cap_ms }
            }
            Some(server_ms) => Self::After(jittered.max(server_ms)),
            None => Self::After(jittered),
        }
    }

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
/// (omp2 `TransportRetryLayer`): a full-jitter draw under the step, where
/// the step is `base_delay_ms * 2^(attempt-1)` capped at
/// `max_agent_delay_ms`, so agents that hit the same limit together do not
/// retry together; never shorter than the server's requested wait, and
/// [`RetryWait::Refused`] when that wait is above the cap
/// ([`RetryWait::decide`]).
#[must_use]
pub fn retry_wait(policy: RetryDelay, attempt: u32, message: &AssistantMessage) -> RetryWait {
    RetryWait::decide(WaitInput {
        base_ms: whole_ms(policy.base_delay_ms),
        attempt,
        cap_ms: whole_ms(
            policy
                .max_agent_delay_ms
                .unwrap_or(DEFAULT_MAX_AGENT_RETRY_DELAY_MS),
        ),
        draw: rand::random::<u64>() >> 18,
        server_ms: server_retry_after_ms(message).map(whole_ms),
    })
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

/// Whether a retry may cure an HTTP `status`: a request timeout, a
/// conflict, too many requests (RFC 9110), or any server error. Every
/// other client error fails the same way again.
#[must_use]
pub const fn retryable_status(status: u16) -> bool {
    matches!(status, 408 | 409 | 429) || status >= 500
}

/// Whether a retry may cure a failure of typed `kind`; `None` for
/// [`StreamFailureKind::Unknown`], which leaves the decision to the text.
#[must_use]
pub const fn retryable_kind(kind: StreamFailureKind) -> Option<bool> {
    match kind {
        StreamFailureKind::Overloaded
        | StreamFailureKind::RateLimit
        | StreamFailureKind::ServerError
        | StreamFailureKind::StreamDrop
        | StreamFailureKind::StreamStalled
        | StreamFailureKind::StreamRepeating => Some(true),
        StreamFailureKind::Refusal
        | StreamFailureKind::Safety
        | StreamFailureKind::PaymentRequired
        | StreamFailureKind::Auth
        | StreamFailureKind::Permission
        | StreamFailureKind::InvalidRequest
        | StreamFailureKind::MalformedResponse => Some(false),
        StreamFailureKind::Unknown => None,
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
        let limit = NON_RETRYABLE_PROVIDER_LIMIT_ERROR_PATTERN.is_match(text)
            || NON_RETRYABLE_PROVIDER_LIMIT_ERROR_PATTERN.is_match(error_type);
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
            transient_text: RETRYABLE_PROVIDER_ERROR_PATTERN.is_match(text),
        })
    }

    /// Whether a retry may cure the failure: never a parked failure or a
    /// limit; else by its recorded status; else by its typed kind; else by
    /// its text.
    #[must_use]
    pub fn retryable(self) -> bool {
        if self.parked || self.limit {
            return false;
        }
        match (self.status, self.kind.and_then(retryable_kind)) {
            (Some(status), _) => retryable_status(status),
            (None, Some(by_kind)) => by_kind,
            (None, None) => self.transient_text,
        }
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
