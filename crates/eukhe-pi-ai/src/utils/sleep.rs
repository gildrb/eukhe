//! Abortable sleep.

use std::time::Duration;

use eukhe_chord::context::{AbortError, AbortSignal};

use super::diagnostics::Thrown;

/// Largest `setTimeout` delay Node accepts (2^31 - 1 ms).
const TIMEOUT_MAX_MS: f64 = 2_147_483_647.0;

/// The delay Node's `setTimeout(fn, ms)` waits: values below 1, above
/// 2^31 - 1, or `NaN` become 1 ms; fractions are truncated.
#[must_use]
pub fn timer_duration(ms: f64) -> Duration {
    let ms = if (1.0..=TIMEOUT_MAX_MS).contains(&ms) {
        ms.trunc()
    } else {
        1.0
    };
    // In range: 1 ≤ ms ≤ 2^31 - 1, a whole number.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    Duration::from_millis(ms as u64)
}

/// Sleep `ms` milliseconds unless `signal` aborts first.
///
/// # Errors
///
/// Returns the signal's abort reason when it is already aborted or aborts
/// during the sleep.
pub async fn sleep(ms: f64, signal: &AbortSignal) -> Result<(), Thrown> {
    signal.throw_if_aborted()?;
    let token = signal.cancellation_token();
    tokio::select! {
        biased;
        () = token.cancelled() => Err(signal.reason().unwrap_or_else(|| std::sync::Arc::new(AbortError))),
        () = tokio::time::sleep(timer_duration(ms)) => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use eukhe_chord::context::AbortController;

    use super::*;
    use crate::utils::diagnostics::ErrorObject;

    #[test]
    fn clamps_delays_like_node_set_timeout() {
        assert_eq!(timer_duration(0.0), Duration::from_millis(1));
        assert_eq!(timer_duration(f64::NAN), Duration::from_millis(1));
        assert_eq!(timer_duration(1.9), Duration::from_millis(1));
        assert_eq!(timer_duration(250.7), Duration::from_millis(250));
        assert_eq!(timer_duration(3e9), Duration::from_millis(1));
    }

    #[tokio::test(start_paused = true)]
    async fn sleeps_until_the_delay_or_the_abort() {
        let controller = AbortController::new();
        let start = tokio::time::Instant::now();
        sleep(1000.0, &controller.signal()).await.unwrap();
        assert_eq!(start.elapsed(), Duration::from_secs(1));

        let signal = controller.signal();
        let sleeping = sleep(60_000.0, &signal);
        let abort = async {
            tokio::task::yield_now().await;
            controller.abort(Some(ErrorObject::new("cancelled").thrown()));
        };
        let (result, ()) = tokio::join!(sleeping, abort);
        assert_eq!(result.unwrap_err().to_string(), "cancelled");
        assert_eq!(
            sleep(1.0, &signal).await.unwrap_err().to_string(),
            "cancelled"
        );
    }
}
