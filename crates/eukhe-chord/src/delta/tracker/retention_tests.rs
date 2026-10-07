//! Rust-observable equivalents of `test/delta-tracker/retention.test.ts`.
//!
//! The TS scenarios run a worker with `--expose-gc` and watch `WeakRef`s.
//! Here the same retention contracts are checked deterministically: a weak
//! reference to a container's `Arc` allocation is dead exactly when nothing
//! (tracker, change, prepared, draft handle, registry) still owns it.

use std::sync::Arc;

use super::{track, Tracker};
use crate::json::{JsonObject, JsonValue, WeakContainer};

fn rows(count: usize) -> JsonValue {
    JsonValue::from(
        (0..count)
            .map(|value| {
                JsonValue::from(JsonObject::from_iter([(
                    "value",
                    JsonValue::try_from(value).unwrap(),
                )]))
            })
            .collect::<Vec<_>>(),
    )
}

fn with(key: &str, value: JsonValue) -> JsonValue {
    JsonValue::from(JsonObject::from_iter([(key, value)]))
}

fn weak(value: &JsonValue) -> WeakContainer {
    value.downgrade().expect("container")
}

fn payload_tracker() -> Tracker {
    track(with("payload", JsonValue::Null)).unwrap()
}

#[test]
fn aborted_payload() {
    let tracker = payload_tracker();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.set("payload", with("rows", rows(50_000))).unwrap();
    let draft_rows = state.child("payload").unwrap().child("rows").unwrap();
    let reference = weak(&draft_rows.base_for_test().unwrap());
    change.abort();
    assert!(!reference.is_alive());
    assert_eq!(tracker.value(), with("payload", JsonValue::Null));
}

#[test]
fn unadopted_prepared() {
    let tracker = payload_tracker();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .set("payload", with("rows", rows(50_000)))
        .unwrap();
    let prepared = change.prepare().unwrap();
    let reference = weak(&prepared.value()["payload"]["rows"]);
    drop(prepared);
    assert!(!reference.is_alive());
    assert_eq!(tracker.value(), with("payload", JsonValue::Null));
}

#[test]
fn draft_proxies() {
    let tracker = payload_tracker();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.set("payload", with("rows", rows(1))).unwrap();
    let row = state
        .child("payload")
        .unwrap()
        .child("rows")
        .unwrap()
        .child(0)
        .unwrap();
    let reference = weak(&row.base_for_test().unwrap());
    change.abort();
    assert!(!reference.is_alive());
    assert!(row.get("value").is_err());
    assert_eq!(tracker.value(), with("payload", JsonValue::Null));
}

#[test]
fn settled_lifecycle() {
    let tracker = payload_tracker();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .set("payload", with("rows", rows(1)))
        .unwrap();
    let retained_prepared = change.prepare().unwrap();
    tracker.adopt(&retained_prepared).unwrap();
    let future_prepared = tracker
        .prepare_replace(with("payload", with("rows", rows(50_000))))
        .unwrap();
    tracker.adopt(&future_prepared).unwrap();
    let tracker_reference = Arc::downgrade(&tracker.inner);
    let future = weak(&future_prepared.value()["payload"]["rows"]);
    drop(future_prepared);
    drop(tracker);
    assert_eq!(tracker_reference.strong_count(), 0);
    assert!(!future.is_alive());
    // The retained change and preparation stay usable as settled handles.
    assert!(change.state().is_err());
    assert_eq!(
        retained_prepared.value(),
        &with("payload", with("rows", rows(1)))
    );
}

#[test]
fn retained_settled_prepared() {
    let tracker = track(with("payload", with("rows", rows(50_000)))).unwrap();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .child("payload")
        .unwrap()
        .child("rows")
        .unwrap()
        .child(0)
        .unwrap()
        .set("value", -1)
        .unwrap();
    let prepared = change.prepare().unwrap();
    let base = weak(&prepared.base()["payload"]["rows"]);
    let value = weak(&prepared.value()["payload"]["rows"]);
    tracker.adopt(&prepared).unwrap();
    drop(change);
    let replacement = tracker
        .prepare_replace(with("payload", with("rows", rows(1))))
        .unwrap();
    tracker.adopt(&replacement).unwrap();
    // The TS replacement is a local of its own function.
    drop(replacement);
    assert!(
        base.is_alive(),
        "retained Prepared must retain its immutable revisions"
    );
    assert!(
        value.is_alive(),
        "retained Prepared must retain its immutable revisions"
    );
    drop(prepared);
    assert!(!base.is_alive());
    assert!(!value.is_alive());
}

#[test]
fn retained_settled_change() {
    let tracker = track(with("payload", with("rows", rows(50_000)))).unwrap();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .child("payload")
        .unwrap()
        .child("rows")
        .unwrap()
        .child(0)
        .unwrap()
        .set("value", -1)
        .unwrap();
    let prepared = change.prepare().unwrap();
    let base = weak(&prepared.base()["payload"]["rows"]);
    let value = weak(&prepared.value()["payload"]["rows"]);
    tracker.adopt(&prepared).unwrap();
    drop(prepared);
    let replacement = tracker
        .prepare_replace(with("payload", with("rows", rows(1))))
        .unwrap();
    tracker.adopt(&replacement).unwrap();
    // The TS replacement is a local of its own function.
    drop(replacement);
    assert!(!base.is_alive());
    assert!(!value.is_alive());
    assert!(change.state().is_err());
}

#[test]
fn retained_settled_proxy() {
    let tracker = track(JsonValue::from(JsonObject::from_iter([
        ("child", with("value", JsonValue::from(0))),
        ("payload", with("rows", rows(50_000))),
    ])))
    .unwrap();
    let obsolete = weak(&tracker.value()["payload"]["rows"]);
    let held = {
        let change = tracker.begin_change();
        let held = change.state().unwrap().child("child").unwrap();
        held.set("value", 1).unwrap();
        let prepared = change.prepare().unwrap();
        tracker.adopt(&prepared).unwrap();
        held
    };
    let replacement = tracker
        .prepare_replace(JsonValue::from(JsonObject::from_iter([
            ("child", with("value", JsonValue::from(2))),
            ("payload", with("rows", rows(1))),
        ])))
        .unwrap();
    tracker.adopt(&replacement).unwrap();
    drop(replacement);
    assert!(!obsolete.is_alive());
    assert_eq!(
        held.get("value").unwrap_err().to_string(),
        "Cannot use a settled overlay"
    );
}

#[test]
fn retained_large_settled_proxy() {
    let tracker = track(with("rows", rows(100_000))).unwrap();
    let obsolete = weak(&tracker.value()["rows"]);
    let held = {
        let change = tracker.begin_change();
        let draft_rows = change.state().unwrap().child("rows").unwrap();
        let held = draft_rows.child(0).unwrap();
        for index in 1..5_000 {
            let value = draft_rows
                .child(index)
                .unwrap()
                .get("value")
                .unwrap()
                .unwrap()
                .to_value()
                .unwrap();
            assert_eq!(value.as_u64(), Some(u64::try_from(index).unwrap()));
        }
        held.set("value", -1).unwrap();
        let prepared = change.prepare().unwrap();
        tracker.adopt(&prepared).unwrap();
        held
    };
    let replacement = tracker.prepare_replace(with("rows", rows(1))).unwrap();
    tracker.adopt(&replacement).unwrap();
    drop(replacement);
    assert!(!obsolete.is_alive());
    assert_eq!(
        held.get("value").unwrap_err().to_string(),
        "Cannot use a settled overlay"
    );
}

#[test]
fn retained_large_placement_proxies() {
    let mut retained = Vec::new();
    for kind in ["write", "writes", "insert", "override"] {
        let tracker = track(JsonValue::from(JsonObject::from_iter([
            ("child", with("value", JsonValue::from(0))),
            ("visited", rows(5_000)),
            ("first", JsonValue::Null),
            ("second", JsonValue::Null),
            (
                "rows",
                if kind == "override" {
                    JsonValue::from(vec![JsonValue::Null])
                } else {
                    JsonValue::array()
                },
            ),
        ])))
        .unwrap();
        let change = tracker.begin_change();
        let state = change.state().unwrap();
        let visited = state.child("visited").unwrap();
        for index in 0..5_000 {
            assert!(visited
                .child(index)
                .unwrap()
                .get("value")
                .unwrap()
                .is_some());
        }
        let filled = |value: i32| JsonValue::from(vec![JsonValue::from(value); 50_000]);
        let held = if kind == "write" || kind == "writes" {
            let held = state.child("child").unwrap();
            state.set("first", filled(1)).unwrap();
            if kind == "writes" {
                state.set("second", filled(2)).unwrap();
            }
            held
        } else {
            let held = state.child("rows").unwrap();
            if kind == "insert" {
                held.push([filled(1)]).unwrap();
            } else {
                held.set(0, filled(1)).unwrap();
            }
            held
        };
        let prepared = change.prepare().unwrap();
        let payload = if kind == "write" || kind == "writes" {
            &prepared.value()["first"]
        } else {
            &prepared.value()["rows"][0]
        };
        let reference = weak(payload);
        tracker.adopt(&prepared).unwrap();
        drop(prepared);
        let replacement = tracker
            .prepare_replace(JsonValue::from(JsonObject::from_iter([
                ("child", with("value", JsonValue::from(1))),
                ("visited", JsonValue::array()),
                ("first", JsonValue::Null),
                ("second", JsonValue::Null),
                ("rows", JsonValue::array()),
            ])))
            .unwrap();
        tracker.adopt(&replacement).unwrap();
        drop(replacement);
        assert!(!reference.is_alive(), "{kind}");
        retained.push(held);
    }
    for held in retained {
        assert_eq!(
            held.get("length").unwrap_err().to_string(),
            "Cannot use a settled overlay"
        );
    }
}

#[test]
fn stale_unprepared_change() {
    let tracker = track(with("payload", with("rows", rows(50_000)))).unwrap();
    let stale = tracker.begin_change();
    stale
        .state()
        .unwrap()
        .child("payload")
        .unwrap()
        .child("rows")
        .unwrap()
        .child(0)
        .unwrap()
        .set("value", -1)
        .unwrap();
    let obsolete = weak(&tracker.value()["payload"]["rows"]);
    let winner = tracker
        .prepare_replace(with("payload", with("rows", rows(1))))
        .unwrap();
    tracker.adopt(&winner).unwrap();
    drop(winner);
    assert_eq!(
        stale.prepare().unwrap_err().to_string(),
        "Cannot use a settled overlay"
    );
    assert!(!obsolete.is_alive());
}

#[test]
fn same_job_fast_cleanup() {
    let tracker = track(with("rows", rows(100_000))).unwrap();
    let mut obsolete = Vec::new();
    for value in 0..100_i32 {
        obsolete.push(weak(&tracker.value()["rows"]));
        let change = tracker.begin_change();
        let draft_rows = change.state().unwrap().child("rows").unwrap();
        for index in 0..4_094 {
            assert!(draft_rows
                .child(index)
                .unwrap()
                .get("value")
                .unwrap()
                .is_some());
        }
        draft_rows
            .child(99_999)
            .unwrap()
            .set("value", -value - 1)
            .unwrap();
        let prepared = change.prepare().unwrap();
        tracker.adopt(&prepared).unwrap();
    }
    assert!(obsolete.iter().all(|reference| !reference.is_alive()));
    assert_eq!(tracker.registered_contexts(), 0);
    assert_eq!(
        tracker.value()["rows"][99_999]["value"],
        JsonValue::from(-100)
    );
}

#[test]
fn same_job_folded_ops_cleanup() {
    let wide: JsonObject = (0..5_000)
        .map(|index| (format!("field{index}"), JsonValue::from(0)))
        .collect();
    let tracker = track(JsonValue::from(wide)).unwrap();
    let mut obsolete = Vec::new();
    for value in 1..=100_i32 {
        obsolete.push(weak(&tracker.value()));
        let change = tracker.begin_change();
        let state = change.state().unwrap();
        for index in 0..5_000 {
            state.set(format!("field{index}"), value).unwrap();
        }
        let prepared = change.prepare().unwrap();
        assert_eq!(prepared.ops().len(), 1);
        assert_eq!(prepared.ops()[0].verb(), "r");
        tracker.adopt(&prepared).unwrap();
    }
    assert!(obsolete.iter().all(|reference| !reference.is_alive()));
    assert_eq!(tracker.value()["field0"], JsonValue::from(100));
}

#[test]
fn lifecycle_churn() {
    let tracker = track(with("value", JsonValue::from(0))).unwrap();
    for index in 0..100_000_i32 {
        let change = tracker.begin_change();
        change.state().unwrap().set("value", index).unwrap();
        change.abort();
    }
    assert!(tracker.lock().contexts.len() <= 256);
    let prepared = tracker
        .prepare_replace(with("value", JsonValue::from(1)))
        .unwrap();
    tracker.adopt(&prepared).unwrap();
    assert_eq!(tracker.value(), with("value", JsonValue::from(1)));
}

#[test]
fn obsolete_revisions() {
    let tracker = track(with("payload", with("rows", rows(50_000)))).unwrap();
    let old_root = weak(&tracker.value()["payload"]["rows"]);
    for value in 0..100_i32 {
        let prepared = tracker
            .prepare_replace(with(
                "payload",
                with(
                    "rows",
                    JsonValue::from(vec![with("value", JsonValue::from(value))]),
                ),
            ))
            .unwrap();
        tracker.adopt(&prepared).unwrap();
    }
    assert!(!old_root.is_alive());
    assert_eq!(
        tracker.value(),
        with(
            "payload",
            with(
                "rows",
                JsonValue::from(vec![with("value", JsonValue::from(99))])
            )
        )
    );
}
