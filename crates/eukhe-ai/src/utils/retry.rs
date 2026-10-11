//! Transient-error classification and the policy-driven assistant retry loop.

use std::future::Future;
use std::sync::{Arc, LazyLock};

use eukhe_chord::context::AbortSignal;
use futures::future::BoxFuture;
use regex::Regex;

use eukhe_types::pi_ai::{AssistantMessage, StopReason};

use super::diagnostics::Thrown;
use super::sleep::timer_duration;

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
    ])
});

static RETRYABLE_PROVIDER_ERROR_PATTERN: LazyLock<Regex> = LazyLock::new(|| {
    build_provider_error_pattern(&[
        // Generic provider load, HTTP status, and server-side transient failures.
        "overloaded",
        "server_busy",
        "servers are currently busy",
        "currently experiencing high demand",
        "model is at capacity",
        "rate.?limit",
        "too many requests",
        "429",
        "500",
        "502",
        "503",
        "504",
        "520",
        "524",
        "service.?unavailable",
        "server.?error",
        "internal.?error",
        // Wrapper/provider text for transient upstream failures (OpenRouter #2264).
        "provider.?returned.?error",
        "exceeded request buffer limit while retrying upstream",
        // Network, proxy, and fetch transport failures (#733, #3317).
        "network.?error",
        "connection.?error",
        "connection.?refused",
        "connection.?lost",
        "other side closed",
        "fetch failed",
        "getaddrinfo",
        "ENOTFOUND",
        "EAI_AGAIN",
        "upstream.?connect",
        "reset before headers",
        "socket hang up",
        "socket connection was closed",
        "timed? out",
        "timeout",
        "terminated",
        // WebSocket close/error text.
        "websocket.?closed",
        "websocket.?error",
        // Premature stream endings (#4433, #3594).
        "ended without",
        "stream ended before message_stop",
        "stream ended before a terminal response event",
        "http2 request did not get a response",
        // HTTP/2 session died before the request was sent (#10379).
        "pending stream has been canceled",
        // Provider-requested retry delay cap failures (#1123).
        "retry delay",
        // Explicit retry guidance emitted mid-stream (#6019).
        "you can retry your request",
        "try your request again",
        "please retry your request",
        // gRPC based providers (e.g. NVIDIA NIM).
        "ResourceExhausted",
        // Sign in with ChatGPT: usage or user data temporarily unavailable.
        "subscription_sharing_usage_unavailable",
        "subscription_sharing_user_unavailable",
    ])
});

/// Retry policy: bounded attempts with exponential backoff
/// (`base_delay_ms * 2^(attempt-1)`), each delay capped by
/// `max_agent_delay_ms` (default 60 seconds).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RetryPolicy {
    pub enabled: bool,
    /// Max retry attempts (0 = no retries). The initial call never counts as a retry.
    pub max_retries: u32,
    /// Base delay in ms.
    pub base_delay_ms: f64,
    /// Optional cap for agent-level retry delays in ms.
    pub max_agent_delay_ms: Option<f64>,
}

impl RetryPolicy {
    /// The delay part of the policy.
    #[must_use]
    pub const fn delay(&self) -> RetryDelay {
        RetryDelay {
            base_delay_ms: self.base_delay_ms,
            max_agent_delay_ms: self.max_agent_delay_ms,
        }
    }
}

/// TS `Pick<RetryPolicy, "baseDelayMs" | "maxAgentDelayMs">`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RetryDelay {
    pub base_delay_ms: f64,
    pub max_agent_delay_ms: Option<f64>,
}

/// Default cap of an agent-level retry delay.
pub const DEFAULT_MAX_AGENT_RETRY_DELAY_MS: f64 = 60_000.0;

/// Largest integer a double represents exactly (`Number.MAX_SAFE_INTEGER`).
const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

/// The capped backoff delay of retry `attempt` (1-indexed).
#[must_use]
pub fn retry_delay_ms(policy: RetryDelay, attempt: u32) -> f64 {
    let exponent = i32::try_from(attempt.saturating_sub(1)).unwrap_or(i32::MAX);
    let delay = policy.base_delay_ms * 2f64.powi(exponent);
    let is_safe_integer =
        delay.is_finite() && delay.fract() == 0.0 && delay.abs() <= MAX_SAFE_INTEGER;
    let safe_delay = if is_safe_integer {
        delay
    } else {
        MAX_SAFE_INTEGER
    };
    safe_delay.min(
        policy
            .max_agent_delay_ms
            .unwrap_or(DEFAULT_MAX_AGENT_RETRY_DELAY_MS),
    )
}

/// A retry callback's completion (callbacks may fail like a TS throw).
pub type RetryCallbackFuture = BoxFuture<'static, Result<(), Thrown>>;

/// `onRetryScheduled(attempt, maxAttempts, delayMs, errorMessage)`.
pub type OnRetryScheduled = Arc<dyn Fn(u32, u32, f64, String) -> RetryCallbackFuture + Send + Sync>;

/// `onRetryAttemptStart()`.
pub type OnRetryAttemptStart = Arc<dyn Fn() -> RetryCallbackFuture + Send + Sync>;

/// `onRetryFinished(success, attempt, finalError)`.
pub type OnRetryFinished =
    Arc<dyn Fn(bool, u32, Option<String>) -> RetryCallbackFuture + Send + Sync>;

/// Optional callbacks emitted by [`retry_assistant_call`] around each retry.
#[derive(Clone, Default)]
pub struct RetryCallbacks {
    /// Before the backoff sleep of each retry.
    pub on_retry_scheduled: Option<OnRetryScheduled>,
    /// After the backoff sleep, immediately before the retried call starts.
    pub on_retry_attempt_start: Option<OnRetryAttemptStart>,
    /// Once when the loop ends.
    pub on_retry_finished: Option<OnRetryFinished>,
}

impl std::fmt::Debug for RetryCallbacks {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("RetryCallbacks")
            .field("on_retry_scheduled", &self.on_retry_scheduled.is_some())
            .field(
                "on_retry_attempt_start",
                &self.on_retry_attempt_start.is_some(),
            )
            .field("on_retry_finished", &self.on_retry_finished.is_some())
            .finish()
    }
}

async fn retry_finished(
    callbacks: Option<&RetryCallbacks>,
    success: bool,
    attempt: u32,
    final_error: Option<String>,
) -> Result<(), Thrown> {
    match callbacks.and_then(|callbacks| callbacks.on_retry_finished.as_ref()) {
        Some(callback) => callback(success, attempt, final_error).await,
        None => Ok(()),
    }
}

/// The backoff sleep. `Ok(false)` when `signal` aborted (before or during it).
async fn backoff_sleep(ms: f64, signal: Option<&AbortSignal>) -> bool {
    let Some(signal) = signal else {
        tokio::time::sleep(timer_duration(ms)).await;
        return true;
    };
    if signal.aborted() {
        return false;
    }
    let token = signal.cancellation_token();
    tokio::select! {
        biased;
        () = token.cancelled() => false,
        () = tokio::time::sleep(timer_duration(ms)) => true,
    }
}

/// Run a single assistant-producing call with bounded retry on transient errors.
///
/// - A successful response is returned immediately. Aborts are terminal and
///   never retried, but reported as unsuccessful after a scheduled retry. An
///   abort during the backoff sleep returns the last error message with
///   `stop_reason` `aborted` and no `error_message`.
/// - A non-retryable error (per [`is_retryable_assistant_error`], including
///   quota/billing exhaustion) is returned immediately.
/// - Otherwise retries up to `max_retries` times with exponential backoff,
///   emitting `on_retry_scheduled` before each sleep, `on_retry_attempt_start`
///   after it, and `on_retry_finished` once at the end.
///
/// With no policy or a disabled one, the first response is returned unchanged.
///
/// # Errors
///
/// A failure of `produce` or of a callback.
pub async fn retry_assistant_call<F, Fut>(
    mut produce: F,
    policy: Option<&RetryPolicy>,
    signal: Option<&AbortSignal>,
    callbacks: Option<&RetryCallbacks>,
) -> Result<AssistantMessage, Thrown>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<AssistantMessage, Thrown>>,
{
    let max_attempts = policy
        .filter(|policy| policy.enabled)
        .map_or(0, |policy| policy.max_retries);
    let mut attempt = 0;
    let mut last_retry: Option<(u32, String)> = None;
    loop {
        let response = produce().await?;

        if response.stop_reason == StopReason::Aborted {
            if let Some((last_attempt, _)) = &last_retry {
                retry_finished(callbacks, false, *last_attempt, None).await?;
            }
            return Ok(response);
        }

        if response.stop_reason != StopReason::Error {
            if let Some((last_attempt, _)) = &last_retry {
                retry_finished(callbacks, true, *last_attempt, None).await?;
            }
            return Ok(response);
        }

        if attempt >= max_attempts || !is_retryable_assistant_error(&response) {
            if let Some((last_attempt, _)) = &last_retry {
                retry_finished(
                    callbacks,
                    false,
                    *last_attempt,
                    response.error_message.clone(),
                )
                .await?;
            }
            return Ok(response);
        }

        attempt += 1;
        let error_message = response
            .error_message
            .clone()
            .filter(|message| !message.is_empty())
            .unwrap_or_else(|| "Unknown error".to_owned());
        last_retry = Some((attempt, error_message.clone()));
        let delay_ms = policy.map_or(0.0, |policy| retry_delay_ms(policy.delay(), attempt));
        if let Some(callback) =
            callbacks.and_then(|callbacks| callbacks.on_retry_scheduled.as_ref())
        {
            callback(attempt, max_attempts, delay_ms, error_message.clone()).await?;
        }

        if !backoff_sleep(delay_ms, signal).await {
            retry_finished(callbacks, false, attempt, Some(error_message)).await?;
            return Ok(AssistantMessage {
                error_message: None,
                stop_reason: StopReason::Aborted,
                ..response
            });
        }
        if let Some(callback) =
            callbacks.and_then(|callbacks| callbacks.on_retry_attempt_start.as_ref())
        {
            callback().await?;
        }
    }
}

/// Whether a failed assistant message looks like a transient provider or
/// transport error. This is classification only: callers handle context
/// overflow first and apply their own retry budget, backoff, and reporting.
#[must_use]
pub fn is_retryable_assistant_error(message: &AssistantMessage) -> bool {
    if message.stop_reason != StopReason::Error {
        return false;
    }
    let Some(error_message) = message
        .error_message
        .as_deref()
        .filter(|text| !text.is_empty())
    else {
        return false;
    };
    if NON_RETRYABLE_PROVIDER_LIMIT_ERROR_PATTERN.is_match(error_message) {
        return false;
    }
    RETRYABLE_PROVIDER_ERROR_PATTERN.is_match(error_message)
}

#[cfg(test)]
mod tests;
