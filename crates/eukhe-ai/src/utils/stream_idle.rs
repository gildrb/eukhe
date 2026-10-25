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

use eukhe_bend::rules::retry::{Idle, Wake};
use eukhe_chord::context::{AbortController, AbortSignal};
use tokio::time::{sleep, Duration, Instant};

use super::sleep::timer_duration;
use super::stream_failure::{stream_stalled_failure, ProviderError};
use crate::types::{OnProviderStreamEvent, ProviderRequestOptions};

/// Default of `ProviderRequestOptions::stream_idle_timeout_ms`: five
/// minutes, longer than the silent reasoning of providers that send
/// nothing while they think.
pub const DEFAULT_STREAM_IDLE_TIMEOUT_MS: f64 = 300_000.0;

/// The stream's deadline as the compiled core keeps it (a stepper of
/// `bend/ffi_retry_idle.bend`). Clones share it: `Models` puts one in the
/// request's options (`ProviderRequestOptions::stream_clock`) for the row
/// that runs it. It holds no rule: each event of the stream's life goes to
/// the stepper, with its time since the deadline was armed, in the order
/// it comes.
#[derive(Clone, Debug)]
pub struct StreamClock {
    deadline: Arc<Mutex<Deadline>>,
}

#[derive(Debug)]
struct Deadline {
    idle: Idle,
    armed: Instant,
}

impl Deadline {
    fn now_us(&self) -> u64 {
        u64::try_from(self.armed.elapsed().as_micros()).unwrap_or(u64::MAX)
    }
}

impl StreamClock {
    fn deadline(&self) -> MutexGuard<'_, Deadline> {
        self.deadline.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn touch(&self) {
        let mut deadline = self.deadline();
        let now = deadline.now_us();
        deadline.idle.life(now);
    }

    /// Stop the clock until the hold drops; it then runs again from that
    /// moment.
    #[must_use = "the clock runs again when the hold drops"]
    pub fn hold(&self) -> ClockHold {
        self.deadline().idle.hold();
        ClockHold {
            clock: self.clone(),
        }
    }

    /// The deadline's timer fired: what the core says it does now.
    fn fire(&self) -> Option<Wake> {
        let mut deadline = self.deadline();
        let now = deadline.now_us();
        deadline.idle.fire(now)
    }
}

/// A [`StreamClock::hold`].
#[derive(Debug)]
pub struct ClockHold {
    clock: StreamClock,
}

impl Drop for ClockHold {
    fn drop(&mut self) {
        let mut deadline = self.clock.deadline();
        let now = deadline.now_us();
        deadline.idle.free(now);
    }
}

/// The deadline of one stream: its clock, the timer's first decision, and
/// the abort of its request.
#[derive(Debug)]
pub(crate) struct StreamIdle {
    timeout_ms: f64,
    first: Wake,
    clock: StreamClock,
    stall: AbortController,
}

impl StreamIdle {
    /// Arm the deadline `request.stream_idle_timeout_ms` selects, from now;
    /// `None` when the compiled core arms none (`R.idle.arm`: `0`, a
    /// negative value and NaN disable it). The request's signal becomes one
    /// that also aborts on a stall, its `stream_clock` this stream's clock,
    /// and `observer` (the stream's provider-event observer, when the
    /// options have one) is wrapped so every event the codec parses counts
    /// as life, including events without content.
    #[tracing::instrument(level = "trace", skip_all)]
    pub(crate) fn arm<M>(
        request: &mut ProviderRequestOptions<M>,
        observer: Option<&mut Option<OnProviderStreamEvent>>,
    ) -> Option<Self> {
        let timeout_ms = request
            .stream_idle_timeout_ms
            .unwrap_or(DEFAULT_STREAM_IDLE_TIMEOUT_MS);
        let deadline_us = u64::try_from(timer_duration(timeout_ms).as_micros()).unwrap_or(u64::MAX);
        let armed = Instant::now();
        let (idle, first) = Idle::arm(timeout_ms, deadline_us)?;
        let stall = AbortController::new();
        request.signal = Some(match request.signal.take() {
            Some(caller) => AbortSignal::any(&[caller, stall.signal()]),
            None => stall.signal(),
        });
        let clock = StreamClock {
            deadline: Arc::new(Mutex::new(Deadline { idle, armed })),
        };
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
        Some(Self {
            timeout_ms,
            first,
            clock,
            stall,
        })
    }

    /// Record a stream event.
    pub(crate) fn touch(&self) {
        self.clock.touch();
    }

    /// Run `work` unless the stream stays silent past the deadline first
    /// (`None`; `work` is dropped). The timer sleeps as the compiled core
    /// answered (first at the arming, then at each fire); a stall, or no
    /// answer (the deadline had stalled), ends the wait.
    pub(crate) async fn within<T>(&self, work: impl Future<Output = T>) -> Option<T> {
        tokio::pin!(work);
        let mut wake = Some(self.first);
        loop {
            let pause = match wake {
                Some(Wake::Sleep(us)) => Duration::from_micros(us),
                Some(Wake::Stall) | None => return None,
            };
            tokio::select! {
                biased;
                value = &mut work => return Some(value),
                () = sleep(pause) => {}
            }
            wake = self.clock.fire();
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
