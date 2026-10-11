//! Push-based async event streams.
//!
//! [`EventStream`] is a cloneable handle: producers `push` events and `end`
//! the stream, consumers iterate with [`EventStream::iter`] (TS
//! `for await`) and await the final result with [`EventStream::result`].
//! As in TS, an event pushed while a consumer is waiting goes straight to the
//! longest-waiting consumer; otherwise it is queued.

use std::collections::VecDeque;
use std::fmt;
use std::pin::Pin;
use std::sync::{Arc, Mutex, PoisonError};
use std::task::{Context as TaskContext, Poll, Waker};
use std::time::{Duration, Instant};

use futures::Stream;
use tokio::sync::watch;

use eukhe_types::pi_ai::{AssistantMessage, AssistantMessageEvent};

type Predicate<T> = Box<dyn Fn(&T) -> bool + Send + Sync>;
type Extractor<T, R> = Box<dyn Fn(&T) -> R + Send + Sync>;

/// What a waiting consumer received.
enum Delivery<T> {
    /// Still waiting; holds the consumer's latest waker.
    Waiting(Waker),
    /// An event (`Some`) or the end of the stream (`None`).
    Ready(Option<T>),
}

struct Waiter<T> {
    delivery: Mutex<Delivery<T>>,
}

impl<T> Waiter<T> {
    fn deliver(&self, value: Option<T>) {
        let previous = std::mem::replace(
            &mut *self.delivery.lock().unwrap_or_else(PoisonError::into_inner),
            Delivery::Ready(value),
        );
        if let Delivery::Waiting(waker) = previous {
            waker.wake();
        }
    }
}

struct State<T> {
    queue: VecDeque<T>,
    waiting: VecDeque<Arc<Waiter<T>>>,
    done: bool,
}

struct Inner<T, R> {
    state: Mutex<State<T>>,
    result: watch::Sender<Option<R>>,
    is_complete: Predicate<T>,
    extract_result: Extractor<T, R>,
}

impl<T, R> Inner<T, R> {
    fn lock(&self) -> std::sync::MutexGuard<'_, State<T>> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Resolve the final result; only the first resolution counts (a promise).
    fn resolve(&self, result: R) {
        self.result.send_if_modified(|slot| {
            if slot.is_some() {
                return false;
            }
            *slot = Some(result);
            true
        });
    }
}

/// Generic event stream for async iteration (TS `EventStream<T, R>`).
pub struct EventStream<T, R = T> {
    inner: Arc<Inner<T, R>>,
}

impl<T, R> Clone for EventStream<T, R> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<T, R> fmt::Debug for EventStream<T, R> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let state = self.inner.lock();
        formatter
            .debug_struct("EventStream")
            .field("queued", &state.queue.len())
            .field("waiting", &state.waiting.len())
            .field("done", &state.done)
            .finish()
    }
}

impl<T: Send + 'static, R: Clone + Send + Sync + 'static> EventStream<T, R> {
    /// A stream that completes at the first event for which `is_complete`
    /// holds, resolving the final result with `extract_result(event)`.
    pub fn new(
        is_complete: impl Fn(&T) -> bool + Send + Sync + 'static,
        extract_result: impl Fn(&T) -> R + Send + Sync + 'static,
    ) -> Self {
        Self {
            inner: Arc::new(Inner {
                state: Mutex::new(State {
                    queue: VecDeque::new(),
                    waiting: VecDeque::new(),
                    done: false,
                }),
                result: watch::Sender::new(None),
                is_complete: Box::new(is_complete),
                extract_result: Box::new(extract_result),
            }),
        }
    }

    /// Deliver an event. Ignored after the stream is done.
    pub fn push(&self, event: T) {
        let waiter = {
            let mut state = self.inner.lock();
            if state.done {
                return;
            }
            if (self.inner.is_complete)(&event) {
                state.done = true;
                self.inner.resolve((self.inner.extract_result)(&event));
            }
            let Some(waiter) = state.waiting.pop_front() else {
                state.queue.push_back(event);
                return;
            };
            waiter
        };
        waiter.deliver(Some(event));
    }

    /// End the stream, resolving the final result with `result` when given
    /// (and not resolved yet). Waiting consumers see the end.
    pub fn end(&self, result: Option<R>) {
        let waiters = {
            let mut state = self.inner.lock();
            state.done = true;
            if let Some(result) = result {
                self.inner.resolve(result);
            }
            std::mem::take(&mut state.waiting)
        };
        for waiter in waiters {
            waiter.deliver(None);
        }
    }

    /// A consumer (TS `for await`) that yields queued and future events until
    /// the stream ends.
    #[must_use]
    pub fn events(&self) -> EventStreamIter<T, R> {
        EventStreamIter {
            stream: self.clone(),
            waiter: None,
        }
    }

    /// The final result. Pending forever when the stream ends without one.
    pub async fn result(&self) -> R {
        let mut receiver = self.inner.result.subscribe();
        loop {
            if let Some(result) = receiver.borrow_and_update().as_ref() {
                return result.clone();
            }
            if receiver.changed().await.is_err() {
                // The sender lives in `self.inner`, so it is never dropped
                // while `self` exists; mirror a promise that never settles.
                std::future::pending::<()>().await;
            }
        }
    }
}

/// One consumer of an [`EventStream`]; a [`Stream`] of its events.
pub struct EventStreamIter<T, R> {
    stream: EventStream<T, R>,
    waiter: Option<Arc<Waiter<T>>>,
}

impl<T, R> Unpin for EventStreamIter<T, R> {}

impl<T, R> Stream for EventStreamIter<T, R> {
    type Item = T;

    fn poll_next(self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Option<T>> {
        let this = self.get_mut();
        if let Some(waiter) = &this.waiter {
            let mut delivery = waiter
                .delivery
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            match &mut *delivery {
                Delivery::Waiting(waker) => {
                    waker.clone_from(cx.waker());
                    return Poll::Pending;
                }
                Delivery::Ready(value) => {
                    let value = value.take();
                    drop(delivery);
                    this.waiter = None;
                    return Poll::Ready(value);
                }
            }
        }
        let mut state = this.stream.inner.lock();
        if let Some(event) = state.queue.pop_front() {
            return Poll::Ready(Some(event));
        }
        if state.done {
            return Poll::Ready(None);
        }
        let waiter = Arc::new(Waiter {
            delivery: Mutex::new(Delivery::Waiting(cx.waker().clone())),
        });
        state.waiting.push_back(Arc::clone(&waiter));
        drop(state);
        this.waiter = Some(waiter);
        Poll::Pending
    }
}

impl<T, R> Drop for EventStreamIter<T, R> {
    /// A dropped consumer gives up its place: an event already handed to it
    /// but not yet yielded returns to the front of the queue.
    fn drop(&mut self) {
        let Some(waiter) = self.waiter.take() else {
            return;
        };
        let mut state = self.stream.inner.lock();
        state.waiting.retain(|queued| !Arc::ptr_eq(queued, &waiter));
        let delivered = match &mut *waiter
            .delivery
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
        {
            Delivery::Ready(value) => value.take(),
            Delivery::Waiting(_) => None,
        };
        if let Some(event) = delivered {
            state.queue.push_front(event);
        }
    }
}

/// Event stream of one assistant response (TS `AssistantMessageEventStream`):
/// completes at `done` or `error` with the final assistant message.
///
/// It also times the response: the final message (`done` or `error` event, or
/// the result passed to `end()`) gets `duration_ms`, measured with a monotonic
/// clock from the stream's creation, unless the message already has one or its
/// `timestamp` predates the stream. A stream that forwards a response which
/// started elsewhere, such as a deferred result fetched later, therefore
/// leaves it untimed.
#[derive(Clone, Debug)]
pub struct AssistantMessageEventStream {
    inner: EventStream<AssistantMessageEvent, AssistantMessage>,
    started_at: u64,
    started_at_monotonic: Instant,
}

impl Default for AssistantMessageEventStream {
    fn default() -> Self {
        Self::new()
    }
}

impl AssistantMessageEventStream {
    /// An empty stream.
    ///
    /// # Panics
    ///
    /// The result extractor only runs for `done`/`error` events and panics
    /// with TS's "Unexpected event type for final result" otherwise.
    #[must_use]
    pub fn new() -> Self {
        let started_at = crate::utils::now_ms();
        let started_at_monotonic = Instant::now();
        Self {
            inner: EventStream::new(
                |event| {
                    matches!(
                        event,
                        AssistantMessageEvent::Done { .. } | AssistantMessageEvent::Error { .. }
                    )
                },
                |event| match event {
                    AssistantMessageEvent::Done { message, .. } => message.clone(),
                    AssistantMessageEvent::Error { error, .. } => error.clone(),
                    AssistantMessageEvent::Start { .. }
                    | AssistantMessageEvent::TextStart { .. }
                    | AssistantMessageEvent::TextDelta { .. }
                    | AssistantMessageEvent::TextEnd { .. }
                    | AssistantMessageEvent::ThinkingStart { .. }
                    | AssistantMessageEvent::ThinkingDelta { .. }
                    | AssistantMessageEvent::ThinkingEnd { .. }
                    | AssistantMessageEvent::ToolCallStart { .. }
                    | AssistantMessageEvent::ToolCallDelta { .. }
                    | AssistantMessageEvent::ToolCallEnd { .. } => {
                        unreachable!("Unexpected event type for final result")
                    }
                },
            ),
            started_at,
            started_at_monotonic,
        }
    }

    /// See [`EventStream::push`]. Times the final message of a `done` or
    /// `error` event.
    pub fn push(&self, mut event: AssistantMessageEvent) {
        match &mut event {
            AssistantMessageEvent::Done { message, .. } => self.time(message),
            AssistantMessageEvent::Error { error, .. } => self.time(error),
            AssistantMessageEvent::Start { .. }
            | AssistantMessageEvent::TextStart { .. }
            | AssistantMessageEvent::TextDelta { .. }
            | AssistantMessageEvent::TextEnd { .. }
            | AssistantMessageEvent::ThinkingStart { .. }
            | AssistantMessageEvent::ThinkingDelta { .. }
            | AssistantMessageEvent::ThinkingEnd { .. }
            | AssistantMessageEvent::ToolCallStart { .. }
            | AssistantMessageEvent::ToolCallDelta { .. }
            | AssistantMessageEvent::ToolCallEnd { .. } => {}
        }
        self.inner.push(event);
    }

    /// See [`EventStream::end`]. Times the given result.
    pub fn end(&self, mut result: Option<AssistantMessage>) {
        if let Some(message) = &mut result {
            self.time(message);
        }
        self.inner.end(result);
    }

    fn time(&self, message: &mut AssistantMessage) {
        if self.inner.inner.lock().done
            || message.duration_ms.is_some()
            || message.timestamp < self.started_at
        {
            return;
        }
        let elapsed = self.started_at_monotonic.elapsed();
        // TS `Math.round(performance.now() - start)`: round to whole milliseconds.
        let rounded = (elapsed + Duration::from_micros(500)).as_millis();
        message.duration_ms = Some(u64::try_from(rounded).unwrap_or(u64::MAX));
    }

    /// See [`EventStream::events`].
    #[must_use]
    pub fn events(&self) -> EventStreamIter<AssistantMessageEvent, AssistantMessage> {
        self.inner.events()
    }

    /// See [`EventStream::result`].
    pub async fn result(&self) -> AssistantMessage {
        self.inner.result().await
    }

    /// The underlying generic stream. Events pushed through it bypass
    /// response timing.
    #[must_use]
    pub fn as_event_stream(&self) -> &EventStream<AssistantMessageEvent, AssistantMessage> {
        &self.inner
    }
}

/// Factory for [`AssistantMessageEventStream`] (for use in extensions).
#[must_use]
pub fn create_assistant_message_event_stream() -> AssistantMessageEventStream {
    AssistantMessageEventStream::new()
}

#[cfg(test)]
mod tests {
    use futures::{FutureExt, StreamExt};

    use super::*;

    fn numbers(
        is_complete: impl Fn(&i32) -> bool + Send + Sync + 'static,
    ) -> EventStream<i32, i32> {
        EventStream::new(is_complete, |event| *event)
    }

    #[tokio::test]
    async fn drains_buffered_events_in_order_and_ignores_events_pushed_after_completion() {
        let stream = numbers(|event| *event == 3);
        stream.push(1);
        stream.push(2);
        stream.push(3);
        stream.push(4);
        assert_eq!(stream.result().await, 3);
        assert_eq!(stream.events().collect::<Vec<_>>().await, [1, 2, 3]);
    }

    #[tokio::test]
    async fn preserves_order_when_events_arrive_after_buffered_draining_starts() {
        let stream = numbers(|_| false);
        stream.push(1);
        stream.push(2);
        let mut iterator = stream.events();
        assert_eq!(iterator.next().await, Some(1));
        stream.push(3);
        assert_eq!(iterator.next().await, Some(2));
        assert_eq!(iterator.next().await, Some(3));
        stream.end(Some(3));
        assert_eq!(iterator.next().await, None);
    }

    #[tokio::test]
    async fn delivers_events_to_waiting_consumers_in_registration_order() {
        let stream = numbers(|_| false);
        let mut first = stream.events();
        let mut second = stream.events();
        // Polling once registers each consumer as a waiter, like calling `next()` in TS.
        assert_eq!(first.next().now_or_never(), None);
        assert_eq!(second.next().now_or_never(), None);
        stream.push(1);
        stream.push(2);
        assert_eq!(first.next().await, Some(1));
        assert_eq!(second.next().await, Some(2));
    }

    #[tokio::test]
    async fn drains_buffered_events_after_end_and_resolves_the_explicit_result() {
        let stream: EventStream<i32, String> =
            EventStream::new(|_| false, |event: &i32| event.to_string());
        stream.push(1);
        stream.push(2);
        stream.end(Some("complete".to_owned()));
        assert_eq!(stream.result().await, "complete");
        assert_eq!(stream.events().collect::<Vec<_>>().await, [1, 2]);
    }

    #[tokio::test]
    async fn wakes_all_waiting_consumers_when_ended_without_a_result() {
        let stream = numbers(|_| false);
        let mut first = stream.events();
        let mut second = stream.events();
        assert_eq!(first.next().now_or_never(), None);
        assert_eq!(second.next().now_or_never(), None);
        stream.end(None);
        assert_eq!(first.next().await, None);
        assert_eq!(second.next().await, None);
        assert_eq!(stream.result().now_or_never(), None);
    }

    #[tokio::test]
    async fn a_dropped_waiting_consumer_returns_its_event_to_the_queue() {
        let stream = numbers(|_| false);
        let mut first = stream.events();
        assert_eq!(first.next().now_or_never(), None);
        stream.push(1);
        drop(first);
        let mut second = stream.events();
        assert_eq!(second.next().await, Some(1));
    }

    fn message(timestamp: u64, duration_ms: Option<u64>) -> AssistantMessage {
        let mut message: AssistantMessage = serde_json::from_value(serde_json::json!({
            "role": "assistant",
            "content": [],
            "api": "openai-responses",
            "provider": "openai",
            "model": "m",
            "usage": {
                "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
            },
            "stopReason": "stop",
            "timestamp": timestamp,
        }))
        .unwrap();
        message.duration_ms = duration_ms;
        message
    }

    fn done(message: AssistantMessage) -> AssistantMessageEvent {
        AssistantMessageEvent::Done {
            reason: eukhe_types::pi_ai::DoneReason::Stop,
            message,
        }
    }

    #[tokio::test]
    async fn sets_duration_on_the_final_done_or_error_message_of_a_response_it_saw_start() {
        let stream = AssistantMessageEventStream::new();
        stream.push(done(message(crate::utils::now_ms(), None)));
        assert!(stream.result().await.duration_ms.is_some());

        let failed = AssistantMessageEventStream::new();
        let mut error = message(crate::utils::now_ms(), None);
        error.stop_reason = eukhe_types::pi_ai::StopReason::Error;
        failed.push(AssistantMessageEvent::Error {
            reason: eukhe_types::pi_ai::ErrorReason::Error,
            error,
        });
        assert!(failed.result().await.duration_ms.is_some());

        let ended = AssistantMessageEventStream::new();
        ended.end(Some(message(crate::utils::now_ms(), None)));
        assert!(ended.result().await.duration_ms.is_some());
    }

    #[tokio::test]
    async fn keeps_an_existing_duration() {
        let preset = AssistantMessageEventStream::new();
        preset.push(done(message(crate::utils::now_ms(), Some(1234))));
        assert_eq!(preset.result().await.duration_ms, Some(1234));
    }

    #[tokio::test]
    async fn leaves_a_message_untimed_when_it_started_before_the_stream() {
        let stream = AssistantMessageEventStream::new();
        stream.push(done(message(crate::utils::now_ms() - 60_000, None)));
        assert_eq!(stream.result().await.duration_ms, None);
    }

    #[tokio::test]
    async fn does_not_time_a_message_pushed_after_the_stream_completed() {
        let stream = AssistantMessageEventStream::new();
        stream.push(done(message(crate::utils::now_ms(), None)));
        let mut late = message(crate::utils::now_ms(), None);
        stream.time(&mut late);
        assert_eq!(late.duration_ms, None);
    }
}
