//! One streamed request with durable throttled partials (TS
//! `streamResponse`).

use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::json::{to_json, JsonValue};
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, Context as PiContext, Message, Model,
};
use futures::StreamExt;
use tokio::sync::oneshot;
use tokio::task::JoinHandle;
use tokio::time::Duration;

use super::{live_generation, Runtime};
use crate::harness::json::assign_json;
use crate::harness::live::LIVE_DOC;
use crate::session::{SessionError, SessionResult};

/// The partial of a non-terminal event; `None` for `done` and `error`.
fn event_partial(event: AssistantMessageEvent) -> Option<AssistantMessage> {
    match event {
        AssistantMessageEvent::Start { partial }
        | AssistantMessageEvent::TextStart { partial, .. }
        | AssistantMessageEvent::TextDelta { partial, .. }
        | AssistantMessageEvent::TextEnd { partial, .. }
        | AssistantMessageEvent::ThinkingStart { partial, .. }
        | AssistantMessageEvent::ThinkingDelta { partial, .. }
        | AssistantMessageEvent::ThinkingEnd { partial, .. }
        | AssistantMessageEvent::ToolCallStart { partial, .. }
        | AssistantMessageEvent::ToolCallDelta { partial, .. }
        | AssistantMessageEvent::ToolCallEnd { partial, .. } => Some(partial),
        AssistantMessageEvent::Done { .. } | AssistantMessageEvent::Error { .. } => None,
    }
}

struct ThrottleState {
    pending: Option<AssistantMessage>,
    timer: Option<JoinHandle<()>>,
    /// Settles with the commit in flight; absent when none is.
    in_flight: Option<oneshot::Receiver<SessionResult<()>>>,
    stopped: bool,
}

/// Partials commit as trailing writes at most every `interval` with one
/// commit in flight.
#[derive(Clone)]
struct Throttle {
    state: Arc<Mutex<ThrottleState>>,
    runtime: Runtime,
    cx: Context,
    attempt: u64,
    interval: Duration,
}

impl Throttle {
    fn lock(&self) -> MutexGuard<'_, ThrottleState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Start the timer unless one runs or a commit is in flight.
    fn arm(&self, state: &mut ThrottleState) {
        if state.timer.is_none() && state.in_flight.is_none() {
            let throttle = self.clone();
            let interval = self.interval;
            state.timer = Some(tokio::spawn(async move {
                tokio::time::sleep(interval).await;
                throttle.flush();
            }));
        }
    }

    fn flush(&self) {
        let mut state = self.lock();
        state.timer = None;
        let partial = state.pending.take();
        let Some(partial) = partial else {
            return;
        };
        if state.stopped {
            return;
        }
        // Copy synchronously (TS `copyJson(partial, { omitUndefinedProperties: true })`).
        let message = to_json(&partial).map_err(SessionError::from);
        let (sender, receiver) = oneshot::channel();
        state.in_flight = Some(receiver);
        drop(state);
        let throttle = self.clone();
        tokio::spawn(async move {
            let result = match message {
                Ok(message) => throttle.commit(message).await,
                Err(error) => Err(error),
            };
            // Rejections after an abort mark or close are expected; the
            // committed state stays consistent.
            let result = match result {
                Err(error) if !throttle.runtime.signal().aborted() => {
                    throttle.runtime.report(error)
                }
                Ok(()) | Err(_) => Ok(()),
            };
            let _ = sender.send(result);
            let mut state = throttle.lock();
            state.in_flight = None;
            if state.pending.is_some() && !state.stopped {
                let interval = throttle.interval;
                let next = throttle.clone();
                state.timer = Some(tokio::spawn(async move {
                    tokio::time::sleep(interval).await;
                    next.flush();
                }));
            }
        });
    }

    async fn commit(&self, message: JsonValue) -> SessionResult<()> {
        let conversation_id = self.runtime.conversation_id();
        let attempt = self.attempt;
        self.runtime
            .commit(
                move |tx, _current| async move {
                    let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                    if live.get("generation")?.is_none() {
                        live.set("generation", to_json(&live_generation(attempt))?)?;
                    }
                    assign_json(&live.child("generation")?, "message", &message)?;
                    Ok(None)
                },
                &self.cx,
            )
            .await
    }

    /// Stop the throttle and await the commit in flight, so no stale partial
    /// lands after the outcome.
    async fn stop(&self) -> SessionResult<()> {
        let in_flight = {
            let mut state = self.lock();
            state.stopped = true;
            if let Some(timer) = state.timer.take() {
                timer.abort();
            }
            state.in_flight.take()
        };
        match in_flight {
            // A dropped sender means the commit task was cancelled with the runtime.
            Some(in_flight) => in_flight.await.unwrap_or(Ok(())),
            None => Ok(()),
        }
    }
}

/// Stops the throttle when the request ends early (TS `finally`): a dropped
/// request must not leave a timer committing partials.
struct StopOnDrop(Throttle);

impl Drop for StopOnDrop {
    fn drop(&mut self) {
        let mut state = self.0.lock();
        state.stopped = true;
        if let Some(timer) = state.timer.take() {
            timer.abort();
        }
    }
}

/// Stream one request and return the terminal message. Partials commit as
/// trailing writes at most every `progress.partial_interval_ms` (default
/// 100 ms) with one commit in flight; the end stops the throttle and awaits
/// that commit, so no stale partial lands after the outcome.
pub(super) async fn stream_response(
    runtime: &Runtime,
    model: &Model,
    messages: Vec<Message>,
    options: eukhe_pi_ai::types::SimpleStreamOptions,
    attempt: u64,
    cx: &Context,
) -> SessionResult<AssistantMessage> {
    let interval = runtime.settings().progress.partial_interval_ms;
    let throttle = Throttle {
        state: Arc::new(Mutex::new(ThrottleState {
            pending: None,
            timer: None,
            in_flight: None,
            stopped: false,
        })),
        runtime: runtime.clone(),
        cx: cx.clone(),
        attempt,
        interval: Duration::from_secs_f64(interval.max(0.0) / 1000.0),
    };
    let _guard = StopOnDrop(throttle.clone());
    let events = runtime.models().stream_simple(
        model,
        PiContext {
            system_prompt: None,
            messages,
            tools: None,
        },
        options.into(),
    );
    let mut iter = events.events();
    while let Some(event) = iter.next().await {
        // A partial without content, such as pi-ai's opening `start` event,
        // shows nothing; a deferred response never gets past it, so it never
        // leaves a partial.
        let Some(partial) = event_partial(event) else {
            continue;
        };
        if partial.content.is_empty() {
            continue;
        }
        let mut state = throttle.lock();
        state.pending = Some(partial);
        throttle.arm(&mut state);
    }
    let message = events.result().await;
    throttle.stop().await?;
    Ok(message)
}
