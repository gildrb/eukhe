//! The race's host: a oneshot event, tokio's timer and an abort signal
//! wake it, and it ends on the core's answer (the answers themselves are
//! pinned by `laws/wait.bend` for every order of polls). On tokio's
//! paused clock the deadline fires exactly at its instant.

use std::time::Duration;

use eukhe_chord::context::AbortController;
use tokio::sync::oneshot;
use tokio::time::Instant;

use super::{race, Exits, Raced};

const DEADLINE: Duration = Duration::from_millis(30);

#[tokio::test(start_paused = true)]
async fn the_event_before_the_deadline_ends_the_race() {
    let (event, arrived) = oneshot::channel::<u32>();
    let exits = Exits {
        deadline: Some(Instant::now() + DEADLINE),
        signal: Some(AbortController::new().signal()),
    };
    let mut wait = Box::pin(race(arrived, exits));
    assert!(futures::poll!(wait.as_mut()).is_pending());
    tokio::time::advance(DEADLINE / 2).await;
    assert!(futures::poll!(wait.as_mut()).is_pending());
    event.send(7).unwrap();
    assert!(matches!(wait.await, Raced::Done(Ok(7))));
}

#[tokio::test(start_paused = true)]
async fn the_deadline_ends_the_race_at_its_instant() {
    let (_event, arrived) = oneshot::channel::<()>();
    let start = Instant::now();
    let exits = Exits {
        deadline: Some(start + DEADLINE),
        signal: None,
    };
    let raced = race(arrived, exits).await;
    assert!(matches!(raced, Raced::Expired));
    assert_eq!(start.elapsed(), DEADLINE);
}

#[tokio::test(start_paused = true)]
async fn the_cancel_ends_the_race_before_its_deadline() {
    let (_event, arrived) = oneshot::channel::<()>();
    let cancel = AbortController::new();
    let start = Instant::now();
    let exits = Exits {
        deadline: Some(start + DEADLINE),
        signal: Some(cancel.signal()),
    };
    let mut wait = Box::pin(race(arrived, exits));
    assert!(futures::poll!(wait.as_mut()).is_pending());
    tokio::time::advance(DEADLINE / 3).await;
    cancel.abort(None);
    assert!(matches!(wait.await, Raced::Cancelled(_)));
    assert_eq!(start.elapsed(), DEADLINE / 3);
}

#[tokio::test(start_paused = true)]
async fn an_event_ready_at_its_first_poll_beats_a_passed_deadline_and_a_fired_cancel() {
    let (event, arrived) = oneshot::channel::<u32>();
    event.send(3).unwrap();
    let cancel = AbortController::new();
    cancel.abort(None);
    let exits = Exits {
        deadline: Some(Instant::now()),
        signal: Some(cancel.signal()),
    };
    assert!(matches!(race(arrived, exits).await, Raced::Done(Ok(3))));
}

#[tokio::test(start_paused = true)]
async fn a_passed_deadline_ends_the_race_at_its_first_poll() {
    let (_event, arrived) = oneshot::channel::<()>();
    let start = Instant::now();
    let exits = Exits {
        deadline: Some(start),
        signal: None,
    };
    assert!(matches!(race(arrived, exits).await, Raced::Expired));
    assert_eq!(start.elapsed(), Duration::ZERO);
}

#[tokio::test(start_paused = true)]
async fn without_a_deadline_the_race_waits_for_its_event() {
    let (event, arrived) = oneshot::channel::<u32>();
    let mut wait = Box::pin(race(arrived, Exits::default()));
    assert!(futures::poll!(wait.as_mut()).is_pending());
    tokio::time::advance(Duration::from_secs(3600)).await;
    assert!(futures::poll!(wait.as_mut()).is_pending());
    event.send(9).unwrap();
    assert!(matches!(wait.await, Raced::Done(Ok(9))));
}
