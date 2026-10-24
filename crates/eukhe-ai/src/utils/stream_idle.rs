//! eukhe addition: the stream-idle deadline of provider event streams.
//!
//! Response-header timeouts end at the headers; after them a half-open
//! connection would hold a stream (and the turn reading it) forever. Every
//! chat and deferred-fetch stream `Models` dispatches is therefore watched
//! in one place, whatever its codec or transport: a stream with no provider
//! event for the deadline aborts its request and ends with a
//! [`StreamFailureKind::StreamStalled`](eukhe_types::pi_ai::StreamFailureKind)
//! error, which the caller's retry policy re-issues.
//!
//! The provider row that runs the request may hold the clock
//! ([`StreamClock::hold`]) while the request waits for something that is
//! not the provider, such as an admission slot: a queue is not a stall
//! (`docs/harness.md` H6.3).

use std::future::Future;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_bend::rules::retry::{idle_armed, idle_wake, IdleClock, Wake};
use eukhe_bend::Entry;
use eukhe_chord::context::{AbortController, AbortSignal};
use tokio::time::{sleep, Duration, Instant};

use super::sleep::timer_duration;
use super::stream_failure::{stream_stalled_failure, ProviderError};
use crate::types::{OnProviderStreamEvent, ProviderRequestOptions};

/// Default of `ProviderRequestOptions::stream_idle_timeout_ms`: five
/// minutes, longer than the silent reasoning of providers that send
/// nothing while they think.
pub const DEFAULT_STREAM_IDLE_TIMEOUT_MS: f64 = 300_000.0;

/// When a stream last showed life, as its idle deadline counts it. Clones
/// share the clock: `Models` puts one in the request's options
/// (`ProviderRequestOptions::stream_clock`) for the row that runs it.
#[derive(Clone, Debug)]
pub struct StreamClock {
    life: Arc<Mutex<Life>>,
}

#[derive(Debug)]
struct Life {
    last: Instant,
    /// Holds alive: while any is, the stream counts as alive.
    holds: u32,
}

impl StreamClock {
    fn new() -> Self {
        Self {
            life: Arc::new(Mutex::new(Life {
                last: Instant::now(),
                holds: 0,
            })),
        }
    }

    fn life(&self) -> MutexGuard<'_, Life> {
        self.life.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn touch(&self) {
        self.life().last = Instant::now();
    }

    /// Stop the clock until the hold drops; it then runs again from that
    /// moment.
    #[must_use = "the clock runs again when the hold drops"]
    pub fn hold(&self) -> ClockHold {
        self.life().holds += 1;
        ClockHold {
            clock: self.clone(),
        }
    }

    /// What the timer of a deadline of `timeout_us` does now: the compiled
    /// core decides (`R.idle.wake`) from the hold and the time since the
    /// stream last showed life.
    fn wake(&self, timeout_us: u64) -> Wake {
        let (clock, since) = {
            let life = self.life();
            let clock = if life.holds == 0 {
                IdleClock::Free
            } else {
                IdleClock::Held
            };
            (clock, Instant::now().saturating_duration_since(life.last))
        };
        let since_us = u64::try_from(since.as_micros()).unwrap_or(u64::MAX);
        eukhe_bend::expect_core(Entry::RetryIdle, idle_wake(clock, since_us, timeout_us))
    }
}

/// A [`StreamClock::hold`].
#[derive(Debug)]
pub struct ClockHold {
    clock: StreamClock,
}

impl Drop for ClockHold {
    fn drop(&mut self) {
        let mut life = self.clock.life();
        life.holds -= 1;
        life.last = Instant::now();
    }
}

/// The deadline of one stream: its clock, and the abort of its request.
#[derive(Debug)]
pub(crate) struct StreamIdle {
    timeout_ms: f64,
    timeout_us: u64,
    clock: StreamClock,
    stall: AbortController,
}

impl StreamIdle {
    /// Arm the deadline `request.stream_idle_timeout_ms` selects, from now;
    /// `None` when it is disabled. The request's signal becomes one that
    /// also aborts on a stall, its `stream_clock` this stream's clock, and
    /// `observer` (the stream's provider-event observer, when the options
    /// have one) is wrapped so every event the codec parses counts as life,
    /// including events without content.
    #[tracing::instrument(level = "trace", skip_all)]
    pub(crate) fn arm<M>(
        request: &mut ProviderRequestOptions<M>,
        observer: Option<&mut Option<OnProviderStreamEvent>>,
    ) -> Option<Self> {
        let timeout_ms = request
            .stream_idle_timeout_ms
            .unwrap_or(DEFAULT_STREAM_IDLE_TIMEOUT_MS);
        // The compiled core decides (`R.idle.arm`): `0`, a negative value,
        // and NaN disable the deadline.
        if !eukhe_bend::expect_core(Entry::RetryIdle, idle_armed(timeout_ms)) {
            return None;
        }
        let stall = AbortController::new();
        request.signal = Some(match request.signal.take() {
            Some(caller) => AbortSignal::any(&[caller, stall.signal()]),
            None => stall.signal(),
        });
        let clock = StreamClock::new();
        request.stream_clock = Some(clock.clone());
        if let Some(observer) = observer {
            let caller = observer.take();
            let seen = clock.clone();
            let watched: OnProviderStreamEvent = Arc::new(move |event, model| {
                seen.touch();
                match &caller {
                    Some(caller) => caller(event, model),
                    None => Box::pin(async { Ok(()) }),
                }
            });
            *observer = Some(watched);
        }
        let timeout = timer_duration(timeout_ms);
        Some(Self {
            timeout_ms,
            timeout_us: u64::try_from(timeout.as_micros()).unwrap_or(u64::MAX),
            clock,
            stall,
        })
    }

    /// Record a stream event: a plain store of the time (no core call).
    pub(crate) fn touch(&self) {
        self.clock.touch();
    }

    /// Run `work` unless the stream stays silent past the deadline first
    /// (`None`; `work` is dropped). Events recorded while `work` runs move
    /// the deadline. Each time the timer fires (and once at the start) the
    /// compiled core decides: the stream stalled, or sleep that long more.
    pub(crate) async fn within<T>(&self, work: impl Future<Output = T>) -> Option<T> {
        tokio::pin!(work);
        loop {
            let pause = match self.clock.wake(self.timeout_us) {
                Wake::Stall => return None,
                Wake::Sleep(us) => Duration::from_micros(us),
            };
            tokio::select! {
                biased;
                value = &mut work => return Some(value),
                () = sleep(pause) => {}
            }
        }
    }

    /// Abort the stalled request and return its failure.
    #[tracing::instrument(level = "debug", skip_all, fields(timeout_ms = self.timeout_ms))]
    pub(crate) fn stall(&self) -> ProviderError {
        let failure = stream_stalled_failure(self.timeout_ms);
        self.stall.abort(None);
        ProviderError::StreamFailure(failure)
    }
}

#[cfg(test)]
mod tests;
