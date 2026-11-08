//! A wait with every exit (spec/README.md D4): an event raced against a
//! deadline and a cancel signal. The race holds no rule: the wait is a
//! stepper of the compiled Bend core (`eukhe_bend::rules::wait`,
//! `bend/ffi_wait_race.bend`). The race opens it with its deadline, sends what
//! it finds ready at each poll, and ends on the end the stepper answers;
//! its laws (`wait_*` in `laws/wait.bend`) hold for every order of polls.

#[cfg(test)]
mod tests;

use std::future::{pending, poll_fn, Future};
use std::pin::pin;
use std::task::Poll;

use eukhe_bend::rules::wait::{Deadline, End, Ready, Wait};
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
/// poll unless the event is ready by then.
pub(super) async fn race<F: Future>(work: F, exits: Exits) -> Raced<F::Output> {
    let (mut wait, opened) = Wait::open(match exits.deadline {
        Some(_) => Deadline::Set,
        None => Deadline::Never,
    });
    // What came, kept: a finished future is not polled again.
    let mut output = None;
    let mut reason = None;
    if let Some(end) = opened {
        return raced(end, &mut output, &mut reason);
    }
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
        match wait.poll(ready) {
            None => Poll::Pending,
            Some(end) => Poll::Ready(raced(end, &mut output, &mut reason)),
        }
    })
    .await
}

/// The race's end `end`, with what it brought.
fn raced<T>(end: End, output: &mut Option<T>, reason: &mut Option<AbortReason>) -> Raced<T> {
    match end {
        End::Work => Raced::Done(
            output
                .take()
                .expect("the core ends a race on its event only once it is ready"),
        ),
        End::Cancel => Raced::Cancelled(
            reason
                .take()
                .expect("the core ends a race on its cancel only once it fired"),
        ),
        End::Deadline => Raced::Expired,
    }
}
