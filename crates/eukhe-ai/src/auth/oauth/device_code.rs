//! RFC 8628 device-code polling shared by the device flows. Port of
//! `auth/oauth/device-code.ts`. Time is tokio's clock, so tests drive it
//! with paused time (the TS tests use fake timers).

use std::future::Future;
use std::time::Duration;

use eukhe_chord::context::AbortSignal;
use tokio::time::Instant;

use crate::auth::errors::js_error;
use crate::utils::diagnostics::Thrown;

const CANCEL_MESSAGE: &str = "Login cancelled";
const TIMEOUT_MESSAGE: &str = "Device flow timed out";
const SLOW_DOWN_TIMEOUT_MESSAGE: &str = "Device flow timed out after one or more slow_down responses. This is often caused by clock drift in WSL or VM environments. Please sync or restart the VM clock and try again.";
const MINIMUM_INTERVAL_MS: f64 = 1000.0;
/// RFC 8628 section 3.2: if the authorization server omits `interval`, the client must use 5 seconds.
const DEFAULT_POLL_INTERVAL_SECONDS: f64 = 5.0;
/// RFC 8628 section 3.5: `slow_down` means the polling interval must increase by 5 seconds.
const SLOW_DOWN_INTERVAL_INCREMENT_MS: f64 = 5000.0;

/// One poll's outcome.
#[derive(Debug, Clone, PartialEq)]
pub enum OAuthDeviceCodePollResult<T> {
    Pending,
    SlowDown { interval_seconds: Option<f64> },
    Failed { message: String },
    Complete { value: T },
}

/// Options of [`poll_oauth_device_code_flow`] other than the poll callback.
#[derive(Debug, Clone)]
pub struct OAuthDeviceCodePollOptions {
    pub interval_seconds: Option<f64>,
    pub expires_in_seconds: Option<f64>,
    pub wait_before_first_poll: bool,
    pub signal: AbortSignal,
}

/// Sleep `ms`, failing with `Error(cancel_message)` when `signal` aborts.
///
/// # Errors
///
/// `Error(cancel_message)` when `signal` is or becomes aborted.
pub async fn abortable_sleep(
    ms: f64,
    signal: &AbortSignal,
    cancel_message: &str,
) -> Result<(), Thrown> {
    if signal.aborted() {
        return Err(js_error(cancel_message));
    }
    tokio::select! {
        _ = signal.cancelled() => Err(js_error(cancel_message)),
        () = tokio::time::sleep(duration_ms(ms)) => Ok(()),
    }
}

fn duration_ms(ms: f64) -> Duration {
    Duration::from_secs_f64(ms.max(0.0) / 1000.0)
}

fn ms_until(deadline: Option<Instant>) -> f64 {
    deadline.map_or(f64::INFINITY, |deadline| {
        let now = Instant::now();
        if deadline > now {
            (deadline - now).as_secs_f64() * 1000.0
        } else {
            -((now - deadline).as_secs_f64() * 1000.0)
        }
    })
}

/// Poll until the flow completes, fails, is cancelled, or expires.
///
/// # Errors
///
/// `Login cancelled` on abort, the poll's failure message, poll errors, or a
/// timeout message after `expires_in_seconds`.
pub async fn poll_oauth_device_code_flow<T, F, Fut>(
    options: OAuthDeviceCodePollOptions,
    mut poll: F,
) -> Result<T, Thrown>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<OAuthDeviceCodePollResult<T>, Thrown>>,
{
    let deadline = options
        .expires_in_seconds
        .map(|seconds| Instant::now() + duration_ms(seconds * 1000.0));
    let mut interval_ms = MINIMUM_INTERVAL_MS.max(
        (options
            .interval_seconds
            .unwrap_or(DEFAULT_POLL_INTERVAL_SECONDS)
            * 1000.0)
            .floor(),
    );

    let mut slow_down_responses = 0_u32;
    if options.wait_before_first_poll {
        let remaining_ms = ms_until(deadline);
        if remaining_ms > 0.0 {
            abortable_sleep(
                interval_ms.min(remaining_ms),
                &options.signal,
                CANCEL_MESSAGE,
            )
            .await?;
        }
    }

    while ms_until(deadline) > 0.0 {
        if options.signal.aborted() {
            return Err(js_error(CANCEL_MESSAGE));
        }

        match poll().await? {
            OAuthDeviceCodePollResult::Complete { value } => return Ok(value),
            OAuthDeviceCodePollResult::Failed { message } => return Err(js_error(message)),
            OAuthDeviceCodePollResult::SlowDown { interval_seconds } => {
                slow_down_responses += 1;
                // Use the server-provided interval when given (GitHub reports the new required
                // minimum in `interval`); trusting only a client-tracked value risks polling early
                // forever under WSL/VM clock drift. Otherwise apply RFC 8628 section 3.5.
                interval_ms = match interval_seconds {
                    Some(seconds) if seconds.is_finite() && seconds > 0.0 => {
                        MINIMUM_INTERVAL_MS.max((seconds * 1000.0).floor())
                    }
                    _ => MINIMUM_INTERVAL_MS.max(interval_ms + SLOW_DOWN_INTERVAL_INCREMENT_MS),
                };
            }
            OAuthDeviceCodePollResult::Pending => {}
        }

        let remaining_ms = ms_until(deadline);
        if remaining_ms <= 0.0 {
            break;
        }

        abortable_sleep(
            interval_ms.min(remaining_ms),
            &options.signal,
            CANCEL_MESSAGE,
        )
        .await?;
    }

    Err(js_error(if slow_down_responses > 0 {
        SLOW_DOWN_TIMEOUT_MESSAGE
    } else {
        TIMEOUT_MESSAGE
    }))
}

#[cfg(test)]
#[path = "device_code_tests.rs"]
mod tests;
