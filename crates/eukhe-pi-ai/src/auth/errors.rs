//! JS `Error` values thrown by the auth code, and the platform
//! `AbortSignal.timeout()` the TS uses for request deadlines.

use std::time::Duration;

use eukhe_chord::context::{AbortController, AbortSignal};

use crate::utils::diagnostics::{ErrorObject, Thrown};

/// `new Error(message)`.
pub(crate) fn js_error(message: impl Into<String>) -> Thrown {
    named_error("Error", message)
}

/// An `Error` with a custom `name`.
pub(crate) fn named_error(name: &str, message: impl Into<String>) -> Thrown {
    ErrorObject::named(name, message).thrown()
}

/// `AbortSignal.timeout(ms)`: aborts with a `TimeoutError` after `ms`.
/// Needs a tokio runtime; the timer task ends with the timeout.
pub(crate) fn timeout_signal(ms: u64) -> AbortSignal {
    let controller = AbortController::new();
    let signal = controller.signal();
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(ms)).await;
        controller.abort(Some(named_error(
            "TimeoutError",
            "The operation was aborted due to timeout",
        )));
    });
    signal
}

/// `Date.now()`: epoch milliseconds as a JS number.
pub(crate) fn date_now() -> f64 {
    let elapsed = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default();
    // Epoch milliseconds stay far below 2^53.
    #[allow(clippy::cast_precision_loss)] // see comment above
    let ms = elapsed.as_millis() as f64;
    ms
}
