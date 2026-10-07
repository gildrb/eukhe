//! Port of `test/state-value.test.ts`.
//!
//! The `Object.isFrozen(...) === false` checks have no counterpart:
//! `JsonValue` is immutable by type and never frozen at run time. TS
//! `structuredClone` is [`copy_json`].

use serde_json::json as j;

use super::json;
use crate::delta::track;
use crate::json::copy_json;

#[test]
fn takes_ownership_of_an_alias_free_mutable_json_root_without_freezing() {
    let input = json(j!({ "left": { "value": 1 }, "right": { "value": 1 } }));
    let tracker = track(input.clone()).unwrap();
    assert!(tracker.value().strict_equals(&input));
    assert!(!tracker.value()["left"].strict_equals(&tracker.value()["right"]));
}

#[test]
fn commits_transaction_copies_in_place_while_sharing_unchanged_branches() {
    let tracker = track(json(
        j!({ "changed": { "value": 1 }, "retained": { "value": 2 } }),
    ))
    .unwrap();
    let base = tracker.value();
    let base_snapshot = copy_json(&base);
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .child("changed")
        .unwrap()
        .set("value", 3)
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert!(!prepared.value()["changed"].strict_equals(&base["changed"]));
    assert!(prepared.value()["retained"].strict_equals(&base["retained"]));
    tracker.adopt(&prepared).unwrap();
    assert_eq!(base, base_snapshot);
    assert!(tracker.value().strict_equals(prepared.value()));
}

#[test]
fn makes_repeated_placements_independent() {
    let tracker = track(json(j!({ "values": [] }))).unwrap();
    let change = tracker.begin_change();
    let shared = json(j!({ "value": 1 }));
    change
        .state()
        .unwrap()
        .child("values")
        .unwrap()
        .push([shared.clone(), shared])
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert!(!prepared.value()["values"][0].strict_equals(&prepared.value()["values"][1]));
}
