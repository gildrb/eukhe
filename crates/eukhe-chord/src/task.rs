//! JS promise semantics on Tokio.
//!
//! A JS async function runs synchronously until its first suspension, keeps
//! running whether or not anyone awaits it, and can be awaited by any number
//! of callers. [`spawn_eager`] reproduces that: it polls the future once on
//! the calling thread, hands the rest to a spawned Tokio task, and returns a
//! cloneable [`Task`] that resolves with the result.

use std::future::Future;
use std::task::{Context as TaskContext, Poll, Waker};

use futures::future::{BoxFuture, Shared};
use futures::FutureExt;

use crate::callback::Outcome;
use crate::error::{report_uncaught, ChordError, ErrorReporter};

/// A started JS promise: cloneable and awaitable by many callers.
pub(crate) type Task = Shared<BoxFuture<'static, Result<(), ChordError>>>;

/// An already settled [`Task`].
pub(crate) fn ready_task(result: Result<(), ChordError>) -> Task {
    futures::future::ready(result).boxed().shared()
}

/// Start `future` like a JS async function call.
///
/// Without a Tokio runtime a future that suspends cannot continue; the task
/// then fails with an error saying so instead of panicking.
pub(crate) fn spawn_eager<F>(future: F) -> Task
where
    F: Future<Output = Result<(), ChordError>> + Send + 'static,
{
    let mut future = Box::pin(future);
    let mut context = TaskContext::from_waker(Waker::noop());
    if let Poll::Ready(result) = future.as_mut().poll(&mut context) {
        return ready_task(result);
    }
    let Ok(runtime) = tokio::runtime::Handle::try_current() else {
        return ready_task(Err(missing_runtime()));
    };
    let handle = runtime.spawn(future);
    async move {
        match handle.await {
            Ok(result) => result,
            Err(error) => std::panic::resume_unwind(error.into_panic()),
        }
    }
    .boxed()
    .shared()
}

/// Await `future` in the background like a `void promise.catch(report)`.
pub(crate) fn spawn_detached<F>(future: F)
where
    F: Future<Output = ()> + Send + 'static,
{
    let mut future = Box::pin(future);
    let mut context = TaskContext::from_waker(Waker::noop());
    if future.as_mut().poll(&mut context).is_ready() {
        return;
    }
    match tokio::runtime::Handle::try_current() {
        Ok(runtime) => {
            drop(runtime.spawn(future));
        }
        Err(_) => report_uncaught(&missing_runtime()),
    }
}

/// Settle a callback outcome in the background, reporting a failure.
/// A synchronous failure is reported before this returns.
pub(crate) fn settle_detached(outcome: Outcome, report: ErrorReporter) {
    match outcome {
        Outcome::Done => {}
        Outcome::Failed(error) => report(error),
        Outcome::Pending(future) => spawn_detached(async move {
            if let Err(error) = future.await {
                report(error);
            }
        }),
    }
}

/// Yield once, like the microtask turn after a JS `await` of a settled
/// promise. Code that continues after a JS `await` never runs in the same
/// synchronous turn as its caller; this keeps that ordering observable.
pub(crate) async fn microtask() {
    let mut yielded = false;
    std::future::poll_fn(|context| {
        if yielded {
            Poll::Ready(())
        } else {
            yielded = true;
            context.waker().wake_by_ref();
            Poll::Pending
        }
    })
    .await;
}

fn missing_runtime() -> ChordError {
    ChordError::error("Chord asynchronous callbacks require a Tokio runtime")
}
