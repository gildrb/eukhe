//! A wait with every exit (docs/harness.md H6): an event raced against a
//! deadline and a cancel signal. At each poll the race gathers what is
//! ready and the compiled Bend core decides which ends it
//! (`eukhe_bend::rules::wait`, `bend/wait.bend` `poll`): the event, then
//! the cancel, then the deadline. How tokio's wakeups make up the polls is
//! checked on tokio's paused clock against the wait model by [`bridge`].

#[cfg(test)]
mod bridge;

use std::future::{pending, poll_fn, Future};
use std::pin::pin;
use std::task::Poll;

use eukhe_bend::rules::wait::{end, End, Ready};
use eukhe_chord::context::{AbortReason, AbortSignal};

/// The exits of a [`race`] besides the awaited event.
#[derive(Clone, Debug, Default)]
pub(super) struct Exits {
    /// When the wait gives up; `None`: never.
    pub(super) deadline: Option<tokio::time::Instant>,
    /// What cancels the wait; `None`: nothing.
    pub(super) signal: Option<AbortSignal>,
}

/// How a [`race`] ended.
#[derive(Debug)]
pub(super) enum Raced<T> {
    /// The awaited event came first.
    Done(T),
    /// The deadline passed first.
    Expired,
    /// The signal aborted first, with its reason.
    Cancelled(AbortReason),
}

/// Await `work` until it completes, the deadline passes, or the signal
/// aborts, whichever the core picks among those ready at a poll. The wait
/// ends exactly once, and the losers are dropped: dropping `work` must end
/// the work it waits for, or leave it safe to finish alone. A deadline
/// already passed or a signal already aborted ends the wait at its first
/// poll unless the event is ready by then. Its laws: `wait_*` in
/// `laws/wait.bend`.
pub(super) async fn race<F: Future>(work: F, exits: Exits) -> Raced<F::Output> {
    let mut work = pin!(work);
    let mut deadline = pin!(async {
        match exits.deadline {
            Some(at) => tokio::time::sleep_until(at).await,
            None => pending().await,
        }
    });
    let mut cancelled = pin!(async {
        match &exits.signal {
            Some(signal) => signal.cancelled().await,
            None => pending().await,
        }
    });
    // What came, kept: a finished future is not polled again.
    let mut output = None;
    let mut reason = None;
    let mut late = false;
    poll_fn(|cx| {
        if output.is_none() {
            if let Poll::Ready(done) = work.as_mut().poll(cx) {
                output = Some(done);
            }
        }
        if reason.is_none() {
            if let Poll::Ready(why) = cancelled.as_mut().poll(cx) {
                reason = Some(why);
            }
        }
        if !late {
            late = deadline.as_mut().poll(cx).is_ready();
        }
        let ready = Ready {
            work: output.is_some(),
            cancel: reason.is_some(),
            deadline: late,
        };
        match end(ready) {
            None => Poll::Pending,
            Some(End::Work) => Poll::Ready(Raced::Done(
                output
                    .take()
                    .expect("the core ends a race on its event only once it is ready"),
            )),
            Some(End::Cancel) => Poll::Ready(Raced::Cancelled(
                reason
                    .take()
                    .expect("the core ends a race on its cancel only once it fired"),
            )),
            Some(End::Deadline) => Poll::Ready(Raced::Expired),
        }
    })
    .await
}
