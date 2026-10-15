use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use eukhe_types::daemon::AdmissionPriority::{Background, Interactive};

use super::*;

fn limits(limit: u32, max_queued: u32) -> AdmissionLimits {
    AdmissionLimits::new(
        Some(&BTreeMap::from([("p".to_owned(), limit)])),
        Some(max_queued),
    )
}

fn granted(admission: Result<Admission, AdmissionRejected>) -> ProviderPermit {
    match admission.expect("admitted") {
        Admission::Granted(permit) => permit,
        Admission::Queued(_) => panic!("queued, expected an immediate grant"),
    }
}

fn queued(admission: Result<Admission, AdmissionRejected>) -> QueuedPermit {
    match admission.expect("admitted") {
        Admission::Queued(waiting) => waiting,
        Admission::Granted(_) => panic!("granted, expected to wait"),
    }
}

/// Interactive counters only.
fn snapshot(active: u32, waiting: u32) -> AdmissionSnapshot {
    AdmissionSnapshot {
        active,
        waiting,
        ..AdmissionSnapshot::default()
    }
}

/// Interactive, then background counters.
fn classes(
    active: u32,
    waiting: u32,
    background: u32,
    background_waiting: u32,
) -> AdmissionSnapshot {
    AdmissionSnapshot {
        active,
        waiting,
        background_active: background,
        background_waiting,
    }
}

#[test]
fn admits_up_to_the_limit_then_queues() {
    let controller = AdmissionController::new("p", &limits(2, 8));
    let _first = granted(controller.admit(Interactive));
    let _second = granted(controller.admit(Interactive));
    let _third = queued(controller.admit(Interactive));
    assert_eq!(controller.snapshot(), snapshot(2, 1));
}

#[test]
fn an_unlimited_provider_never_queues() {
    let controller = AdmissionController::new("other", &limits(1, 0));
    let permits: Vec<ProviderPermit> = (0..5)
        .map(|_| granted(controller.admit(Interactive)))
        .collect();
    assert_eq!(controller.snapshot(), snapshot(5, 0));
    drop(permits);
    assert_eq!(controller.snapshot(), snapshot(0, 0));
}

#[test]
fn a_released_slot_goes_to_the_oldest_waiter() {
    let controller = AdmissionController::new("p", &limits(1, 8));
    let holder = granted(controller.admit(Interactive));
    let mut first = queued(controller.admit(Interactive));
    let mut second = queued(controller.admit(Interactive));
    assert!((&mut first).now_or_never().is_none());
    assert!((&mut second).now_or_never().is_none());

    drop(holder);
    // A new arrival cannot overtake the queue.
    let mut late = queued(controller.admit(Interactive));
    assert!((&mut second).now_or_never().is_none());
    let first_permit = (&mut first)
        .now_or_never()
        .expect("the oldest waiter is granted");
    assert_eq!(controller.snapshot(), snapshot(1, 2));

    drop(first_permit);
    assert!((&mut late).now_or_never().is_none());
    let _second_permit = (&mut second).now_or_never().expect("then the next one");
    assert_eq!(controller.snapshot(), snapshot(1, 1));
}

#[test]
fn a_full_queue_fails_fast() {
    let controller = AdmissionController::new("p", &limits(1, 2));
    let _holder = granted(controller.admit(Interactive));
    let _first = queued(controller.admit(Interactive));
    let _second = queued(controller.admit(Interactive));
    let Err(rejected) = controller.admit(Interactive) else {
        panic!("the third waiter must be rejected");
    };
    assert_eq!(
        rejected,
        AdmissionRejected {
            provider_id: "p".to_owned(),
            queue_limit: 2,
        }
    );
    assert_eq!(controller.snapshot(), snapshot(1, 2));
}

#[test]
fn a_dropped_waiter_leaves_the_queue() {
    let controller = AdmissionController::new("p", &limits(1, 8));
    let holder = granted(controller.admit(Interactive));
    let gone = queued(controller.admit(Interactive));
    let mut kept = queued(controller.admit(Interactive));
    drop(gone);
    assert_eq!(controller.snapshot(), snapshot(1, 1));
    drop(holder);
    let _permit = (&mut kept).now_or_never().expect("the remaining waiter");
    assert_eq!(controller.snapshot(), snapshot(1, 0));
}

#[test]
fn a_granted_but_uncollected_permit_passes_on_when_dropped() {
    let controller = AdmissionController::new("p", &limits(1, 8));
    let holder = granted(controller.admit(Interactive));
    let granted_late = queued(controller.admit(Interactive));
    let mut next = queued(controller.admit(Interactive));
    drop(holder);
    // The grant landed on `granted_late`, which is dropped before polling.
    drop(granted_late);
    let _permit = (&mut next).now_or_never().expect("the slot moved on");
    assert_eq!(controller.snapshot(), snapshot(1, 0));
}

#[test]
fn raising_the_limit_admits_waiters_and_lowering_drains() {
    let controller = AdmissionController::new("p", &limits(1, 8));
    let holder = granted(controller.admit(Interactive));
    let mut waiting = queued(controller.admit(Interactive));
    controller.set_limits(&limits(2, 8));
    let second = (&mut waiting).now_or_never().expect("granted by the raise");
    assert_eq!(controller.snapshot(), snapshot(2, 0));

    controller.set_limits(&limits(1, 8));
    let mut third = queued(controller.admit(Interactive));
    drop(holder);
    // Two active over a limit of one: the release only drains.
    assert!((&mut third).now_or_never().is_none());
    drop(second);
    let _third = (&mut third).now_or_never().expect("under the limit again");
    assert_eq!(controller.snapshot(), snapshot(1, 0));
}

#[test]
fn zero_means_unlimited_and_the_queue_default_applies() {
    let limits = AdmissionLimits::new(
        Some(&BTreeMap::from([
            ("zero".to_owned(), 0),
            ("four".to_owned(), 4),
        ])),
        None,
    );
    assert_eq!(
        (
            limits.max_in_flight("zero"),
            limits.max_in_flight("four"),
            limits.max_queued()
        ),
        (None, NonZeroU32::new(4), 64)
    );
}

/// Background requests take slots under the same limit: past it they
/// wait, oldest first, and `providerMaxQueued` never rejects them.
#[test]
fn background_requests_count_against_the_limit() {
    let controller = AdmissionController::new("p", &limits(2, 0));
    let first = granted(controller.admit(Background));
    let _second = granted(controller.admit(Background));
    let mut third = queued(controller.admit(Background));
    let mut fourth = queued(controller.admit(Background));
    assert_eq!(controller.snapshot(), classes(0, 0, 2, 2));
    drop(first);
    assert!((&mut fourth).now_or_never().is_none());
    let _third = (&mut third).now_or_never().expect("the oldest waiter");
    assert_eq!(controller.snapshot(), classes(0, 0, 2, 1));
}

/// An interactive request takes back every background slot at once, so it
/// is admitted even when background requests fill the limit; the
/// preempted permits' slots are gone already, so dropping them frees
/// nothing more.
#[test]
fn an_interactive_request_preempts_every_background_permit() {
    let controller = AdmissionController::new("p", &limits(2, 8));
    let first = granted(controller.admit(Background));
    let second = granted(controller.admit(Background));
    let preemptions = [first.preemption(), second.preemption()];
    let interactive = granted(controller.admit(Interactive));
    assert_eq!(
        (
            preemptions.each_ref().map(CancellationToken::is_cancelled),
            interactive.preemption().is_cancelled(),
            controller.snapshot()
        ),
        ([true, true], false, classes(1, 0, 0, 0))
    );
    drop((first, second));
    let _another = granted(controller.admit(Interactive));
    let _waiting = queued(controller.admit(Interactive));
    assert_eq!(controller.snapshot(), classes(2, 1, 0, 0));
}

/// A background request waits while an interactive request of its
/// provider holds a slot (even with room to spare) or waits for one, and
/// gets its slot once none does.
#[test]
fn background_waits_while_interactive_requests_hold_or_wait() {
    let controller = AdmissionController::new("p", &limits(2, 8));
    let first = granted(controller.admit(Interactive));
    let mut background = queued(controller.admit(Background));
    let second = granted(controller.admit(Interactive));
    let mut third = queued(controller.admit(Interactive));
    assert_eq!(controller.snapshot(), classes(2, 1, 0, 1));
    drop(first);
    // The slot goes to the interactive waiter.
    assert!((&mut background).now_or_never().is_none());
    let third_permit = (&mut third).now_or_never().expect("the interactive waiter");
    drop(second);
    assert!((&mut background).now_or_never().is_none());
    drop(third_permit);
    let permit = (&mut background)
        .now_or_never()
        .expect("granted once no interactive request runs");
    assert_eq!(
        (permit.preemption().is_cancelled(), controller.snapshot()),
        (false, classes(0, 0, 1, 0))
    );
}

/// At a limit of one (a server that runs one request at a time), the
/// rounds of a turn keep the slot: a waiting round gets it before any
/// background request, the compactor gets it only between rounds, and the
/// next round takes it back from the compactor at once.
#[test]
fn at_a_limit_of_one_the_rounds_of_a_turn_come_before_the_compactor() {
    let controller = AdmissionController::new("p", &limits(1, 8));
    let first_round = granted(controller.admit(Interactive));
    let mut compactor = queued(controller.admit(Background));
    let mut second_round = queued(controller.admit(Interactive));
    drop(first_round);
    assert!((&mut compactor).now_or_never().is_none());
    let second_round = (&mut second_round)
        .now_or_never()
        .expect("the waiting round");
    assert_eq!(controller.snapshot(), classes(1, 0, 0, 1));
    // A tool runs: no round holds or waits.
    drop(second_round);
    let compactor = (&mut compactor)
        .now_or_never()
        .expect("the compactor between rounds");
    let preempted = compactor.preemption();
    let _third_round = granted(controller.admit(Interactive));
    assert_eq!(
        (preempted.is_cancelled(), controller.snapshot()),
        (true, classes(1, 0, 0, 0))
    );
}

/// An unlimited provider admits every interactive request at once, still
/// holds its background requests back while one runs, and preempts them
/// when one comes.
#[test]
fn an_unlimited_provider_still_puts_background_requests_last() {
    let controller = AdmissionController::new("other", &limits(1, 0));
    let interactive = granted(controller.admit(Interactive));
    let mut background = queued(controller.admit(Background));
    let second = granted(controller.admit(Interactive));
    assert_eq!(controller.snapshot(), classes(2, 0, 0, 1));
    drop((interactive, second));
    let background = (&mut background)
        .now_or_never()
        .expect("granted once the interactive requests ended");
    let _more = granted(controller.admit(Background));
    let preempted = background.preemption();
    let _interactive = granted(controller.admit(Interactive));
    assert_eq!(
        (preempted.is_cancelled(), controller.snapshot()),
        (true, classes(1, 0, 0, 0))
    );
}

/// A background grant its waiter has not collected yet goes back to the
/// head of the background queue when an interactive request comes.
#[test]
fn an_uncollected_background_grant_goes_back_to_the_queue() {
    let controller = AdmissionController::new("p", &limits(1, 8));
    let holder = granted(controller.admit(Interactive));
    let mut older = queued(controller.admit(Background));
    let mut newer = queued(controller.admit(Background));
    drop(holder);
    // The grant landed on `older`; an interactive request takes it back.
    let interactive = granted(controller.admit(Interactive));
    assert_eq!(controller.snapshot(), classes(1, 0, 0, 2));
    assert!((&mut older).now_or_never().is_none());
    drop(interactive);
    assert!((&mut newer).now_or_never().is_none());
    let permit = (&mut older).now_or_never().expect("still the oldest");
    assert_eq!(
        (permit.preemption().is_cancelled(), controller.snapshot()),
        (false, classes(0, 0, 1, 1))
    );
}

#[tokio::test]
async fn local_admission_notifies_only_requests_that_wait() {
    let registry = Arc::new(AdmissionRegistry::default());
    let admission =
        AdmissionHandle::new(Arc::new(LocalAdmission::new(Arc::clone(&registry), || {
            limits(1, 8)
        })));
    let notices = Arc::new(AtomicUsize::new(0));
    let request = |notices: &Arc<AtomicUsize>| {
        let notices = Arc::clone(notices);
        AdmissionRequest {
            provider_id: "p".to_owned(),
            priority: Interactive,
            on_queued: QueuedNotice::new(move || {
                notices.fetch_add(1, Ordering::SeqCst);
            }),
        }
    };
    let first = admission
        .acquire(request(&notices))
        .await
        .expect("a free slot");
    assert_eq!(notices.load(Ordering::SeqCst), 0);
    let mut second = admission.acquire(request(&notices));
    assert!((&mut second).now_or_never().is_none());
    assert_eq!(notices.load(Ordering::SeqCst), 1);
    drop(first);
    let _second = second.await.expect("granted after the release");
    assert_eq!(registry.controller("p").snapshot(), snapshot(1, 0));
}

/// A background model permit learns of its preemption.
#[tokio::test]
async fn a_preempted_model_permit_says_so() {
    let admission = AdmissionHandle::new(Arc::new(LocalAdmission::new(
        Arc::new(AdmissionRegistry::default()),
        || limits(1, 8),
    )));
    let request = |priority| AdmissionRequest {
        provider_id: "p".to_owned(),
        priority,
        on_queued: QueuedNotice::new(|| {}),
    };
    let background = admission
        .acquire(request(Background))
        .await
        .expect("a free slot");
    assert!(background.preempted().now_or_never().is_none());
    let interactive = admission
        .acquire(request(Interactive))
        .now_or_never()
        .expect("admitted at once")
        .expect("a slot");
    assert_eq!(
        (
            background.preempted().now_or_never(),
            interactive.preempted().now_or_never()
        ),
        (Some(()), None)
    );
}

#[tokio::test]
async fn local_admission_rejects_past_the_queue_limit() {
    let admission = AdmissionHandle::new(Arc::new(LocalAdmission::new(
        Arc::new(AdmissionRegistry::default()),
        || limits(1, 0),
    )));
    let request = || AdmissionRequest {
        provider_id: "p".to_owned(),
        priority: Interactive,
        on_queued: QueuedNotice::new(|| {}),
    };
    let _held = admission.acquire(request()).await.expect("a free slot");
    let Err(error) = admission.acquire(request()).await else {
        panic!("a zero-length queue rejects the waiter");
    };
    assert_eq!(
        error,
        AdmissionError::QueueFull(AdmissionRejected {
            provider_id: "p".to_owned(),
            queue_limit: 0,
        })
    );
}
