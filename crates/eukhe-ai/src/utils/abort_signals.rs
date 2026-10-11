//! Combining optional abort signals.

use eukhe_chord::context::{AbortController, AbortSignal};
use futures::future::{select, select_all, Either};
use tokio_util::sync::CancellationToken;

/// The abort listeners of a combined signal.
#[derive(Debug)]
struct Listeners {
    controller: AbortController,
    watched: Vec<AbortSignal>,
    stop: CancellationToken,
}

impl Listeners {
    /// Forward an abort that already happened at a source.
    fn forward_pending_abort(&self) {
        if self.controller.signal().aborted() {
            return;
        }
        if let Some(source) = self.watched.iter().find(|signal| signal.aborted()) {
            self.controller.abort(source.reason());
        }
    }
}

/// A combined signal and the cleanup that detaches it from its sources.
#[derive(Debug)]
pub struct CombinedAbortSignal {
    /// `None` when no source signal was given.
    pub signal: Option<AbortSignal>,
    listeners: Option<Listeners>,
}

impl CombinedAbortSignal {
    /// Stop following the source signals. A source abort that happened
    /// before this call still reaches the combined signal (TS listeners fire
    /// synchronously), later ones do not.
    pub fn cleanup(&self) {
        if let Some(listeners) = &self.listeners {
            listeners.forward_pending_abort();
            listeners.stop.cancel();
        }
    }
}

/// TS `combineAbortSignals(signals)`: no signal for no sources, the source
/// itself for one, otherwise a new signal that aborts with the reason of the
/// first source to abort (immediately when one already has).
///
/// # Panics
///
/// With two or more pending sources the listener runs as a Tokio task, so the
/// call must happen inside a Tokio runtime.
#[must_use]
pub fn combine_abort_signals(signals: &[Option<AbortSignal>]) -> CombinedAbortSignal {
    let active: Vec<&AbortSignal> = signals.iter().flatten().collect();
    match active.as_slice() {
        [] => {
            return CombinedAbortSignal {
                signal: None,
                listeners: None,
            }
        }
        [single] => {
            return CombinedAbortSignal {
                signal: Some((*single).clone()),
                listeners: None,
            }
        }
        _ => {}
    }
    let controller = AbortController::new();
    let mut watched: Vec<AbortSignal> = Vec::new();
    for signal in active {
        if signal.aborted() {
            controller.abort(signal.reason());
            break;
        }
        watched.push(signal.clone());
    }
    let combined = controller.signal();
    let listeners = Listeners {
        controller,
        watched,
        stop: CancellationToken::new(),
    };
    if !combined.aborted() {
        let controller = listeners.controller.clone();
        let watched = listeners.watched.clone();
        let stop = listeners.stop.clone();
        tokio::spawn(async move {
            let aborts = select_all(
                watched
                    .iter()
                    .map(|signal| Box::pin(signal.cancellation_token().cancelled_owned())),
            );
            let stopped = Box::pin(stop.clone().cancelled_owned());
            if let Either::Left((((), index, _), _)) = select(aborts, stopped).await {
                // An abort observed after `cleanup()` never propagates.
                if !stop.is_cancelled() {
                    controller.abort(watched[index].reason());
                }
            }
        });
    }
    CombinedAbortSignal {
        signal: Some(combined),
        listeners: Some(listeners),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::diagnostics::ErrorObject;

    #[tokio::test]
    async fn combines_zero_one_and_many_signals() {
        assert!(combine_abort_signals(&[None, None]).signal.is_none());

        let only = AbortController::new();
        let single = combine_abort_signals(&[None, Some(only.signal())]);
        assert!(single
            .signal
            .as_ref()
            .is_some_and(|signal| signal.same(&only.signal())));

        let first = AbortController::new();
        let second = AbortController::new();
        let combined = combine_abort_signals(&[Some(first.signal()), Some(second.signal())]);
        let signal = combined.signal.clone().unwrap();
        assert!(!signal.aborted());
        second.abort(Some(ErrorObject::new("second").thrown()));
        signal.cancellation_token().cancelled().await;
        assert_eq!(signal.reason().unwrap().to_string(), "second");
    }

    #[tokio::test]
    async fn uses_an_already_aborted_source_and_detaches_on_cleanup() {
        let aborted = AbortController::new();
        aborted.abort(Some(ErrorObject::new("early").thrown()));
        let other = AbortController::new();
        let combined = combine_abort_signals(&[Some(other.signal()), Some(aborted.signal())]);
        assert_eq!(
            combined.signal.unwrap().reason().unwrap().to_string(),
            "early"
        );

        let first = AbortController::new();
        let second = AbortController::new();
        let detached = combine_abort_signals(&[Some(first.signal()), Some(second.signal())]);
        detached.cleanup();
        tokio::task::yield_now().await;
        first.abort(None);
        tokio::task::yield_now().await;
        assert!(!detached.signal.unwrap().aborted());
    }
}
