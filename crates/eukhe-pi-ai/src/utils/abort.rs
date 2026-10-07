//! Abort helpers for public APIs whose signal is optional.

use std::future::Future;

use eukhe_chord::context::{AbortController, AbortSignal};

use super::diagnostics::{ErrorObject, Thrown};

/// The signal's reason, or an `AbortError` when it has none.
fn abort_reason(signal: &AbortSignal) -> Thrown {
    signal
        .reason()
        .unwrap_or_else(|| ErrorObject::named("AbortError", "The operation was aborted").thrown())
}

/// Create an operation-local signal for public APIs whose signal is optional.
#[must_use]
pub fn operation_signal(signal: Option<AbortSignal>) -> AbortSignal {
    signal.unwrap_or_else(|| AbortController::new().signal())
}

/// Stop waiting for an operation when `signal` aborts, while the abandoned
/// operation keeps running to completion (it is spawned, as the TS promise
/// keeps running and is observed so a later failure is always handled).
///
/// # Errors
///
/// Returns the abort reason when `signal` aborts first, otherwise the
/// operation's error.
///
/// # Panics
///
/// Resumes the operation's panic.
pub async fn race_with_abort_signal<T: Send + 'static>(
    operation: impl Future<Output = Result<T, Thrown>> + Send + 'static,
    signal: &AbortSignal,
) -> Result<T, Thrown> {
    if signal.aborted() {
        // Detached: the operation finishes on its own and its outcome is dropped.
        drop(tokio::spawn(operation));
        return Err(abort_reason(signal));
    }
    let mut handle = tokio::spawn(operation);
    let token = signal.cancellation_token();
    tokio::select! {
        biased;
        () = token.cancelled() => Err(abort_reason(signal)),
        joined = &mut handle => match joined {
            Ok(result) => result,
            Err(error) if error.is_panic() => std::panic::resume_unwind(error.into_panic()),
            Err(error) => Err(super::diagnostics::thrown(error)),
        },
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    use super::*;

    #[tokio::test]
    async fn returns_the_operation_result_while_the_signal_is_open() {
        let signal = operation_signal(None);
        assert!(!signal.aborted());
        let result = race_with_abort_signal(async { Ok::<_, Thrown>(7) }, &signal).await;
        assert_eq!(result.unwrap(), 7);
        let failed = race_with_abort_signal(
            async { Err::<i32, _>(ErrorObject::new("boom").thrown()) },
            &signal,
        )
        .await;
        assert_eq!(failed.unwrap_err().to_string(), "boom");
    }

    #[tokio::test]
    async fn rejects_with_the_abort_reason_and_keeps_the_abandoned_operation_running() {
        let controller = AbortController::new();
        let signal = operation_signal(Some(controller.signal()));
        let (release, released) = tokio::sync::oneshot::channel::<()>();
        let finished = Arc::new(AtomicBool::new(false));
        let flag = Arc::clone(&finished);
        let operation = async move {
            released.await.ok();
            flag.store(true, Ordering::SeqCst);
            Ok::<_, Thrown>(())
        };
        let race = race_with_abort_signal(operation, &signal);
        let abort = async {
            tokio::task::yield_now().await;
            controller.abort(Some(ErrorObject::named("AbortError", "stop").thrown()));
        };
        let (result, ()) = tokio::join!(race, abort);
        assert_eq!(result.unwrap_err().to_string(), "stop");
        release.send(()).unwrap();
        while !finished.load(Ordering::SeqCst) {
            tokio::task::yield_now().await;
        }

        let already = race_with_abort_signal(async { Ok::<_, Thrown>(1) }, &signal).await;
        assert_eq!(already.unwrap_err().to_string(), "stop");
    }
}
