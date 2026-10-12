use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

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

fn snapshot(active: u32, waiting: u32) -> AdmissionSnapshot {
    AdmissionSnapshot { active, waiting }
}

#[test]
fn admits_up_to_the_limit_then_queues() {
    let controller = AdmissionController::new("p", &limits(2, 8));
    let _first = granted(controller.admit());
    let _second = granted(controller.admit());
    let _third = queued(controller.admit());
    assert_eq!(controller.snapshot(), snapshot(2, 1));
}

#[test]
fn an_unlimited_provider_never_queues() {
    let controller = AdmissionController::new("other", &limits(1, 0));
    let permits: Vec<ProviderPermit> = (0..5).map(|_| granted(controller.admit())).collect();
    assert_eq!(controller.snapshot(), snapshot(5, 0));
    drop(permits);
    assert_eq!(controller.snapshot(), snapshot(0, 0));
}

#[test]
fn a_released_slot_goes_to_the_oldest_waiter() {
    let controller = AdmissionController::new("p", &limits(1, 8));
    let holder = granted(controller.admit());
    let mut first = queued(controller.admit());
    let mut second = queued(controller.admit());
    assert!((&mut first).now_or_never().is_none());
    assert!((&mut second).now_or_never().is_none());

    drop(holder);
    // A new arrival cannot overtake the queue.
    let mut late = queued(controller.admit());
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
    let _holder = granted(controller.admit());
    let _first = queued(controller.admit());
    let _second = queued(controller.admit());
    let Err(rejected) = controller.admit() else {
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
    let holder = granted(controller.admit());
    let gone = queued(controller.admit());
    let mut kept = queued(controller.admit());
    drop(gone);
    assert_eq!(controller.snapshot(), snapshot(1, 1));
    drop(holder);
    let _permit = (&mut kept).now_or_never().expect("the remaining waiter");
    assert_eq!(controller.snapshot(), snapshot(1, 0));
}

#[test]
fn a_granted_but_uncollected_permit_passes_on_when_dropped() {
    let controller = AdmissionController::new("p", &limits(1, 8));
    let holder = granted(controller.admit());
    let granted_late = queued(controller.admit());
    let mut next = queued(controller.admit());
    drop(holder);
    // The grant landed on `granted_late`, which is dropped before polling.
    drop(granted_late);
    let _permit = (&mut next).now_or_never().expect("the slot moved on");
    assert_eq!(controller.snapshot(), snapshot(1, 0));
}

#[test]
fn raising_the_limit_admits_waiters_and_lowering_drains() {
    let controller = AdmissionController::new("p", &limits(1, 8));
    let holder = granted(controller.admit());
    let mut waiting = queued(controller.admit());
    controller.set_limits(&limits(2, 8));
    let second = (&mut waiting).now_or_never().expect("granted by the raise");
    assert_eq!(controller.snapshot(), snapshot(2, 0));

    controller.set_limits(&limits(1, 8));
    let mut third = queued(controller.admit());
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
    assert_eq!(
        registry.controller("p").snapshot(),
        AdmissionSnapshot {
            active: 1,
            waiting: 0
        }
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
