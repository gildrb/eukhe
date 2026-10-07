//! Port of `test/state-draft.test.ts`.
//!
//! "rejects non-strict JSON placements without mutating the draft or base"
//! places `undefined`, `{ nested: undefined }`, `NaN`, and a `Date`; none of
//! them is a `JsonValue`, so a placement cannot be built. The Rust-observable
//! equivalent asserts that building the non-finite number fails and that the
//! draft and base stay unchanged. `Reflect.apply` argument spreading becomes
//! passing the 100,000 items as one iterator.

use serde_json::json as j;

use crate::delta::{apply_immutable, track, DraftItem, TrackerError};
use crate::json::{to_json, JsonError, JsonValue};

use super::json;

fn number(item: &DraftItem) -> f64 {
    item.as_value().and_then(JsonValue::as_f64).unwrap()
}

fn field(item: &DraftItem, key: &str) -> f64 {
    let value = item.as_draft().unwrap().get(key).unwrap().unwrap();
    number(&value)
}

fn int(value: i64) -> JsonValue {
    JsonValue::try_from(value).unwrap()
}

#[test]
fn copies_only_changed_branches() {
    let tracker = track(json(j!({
        "changed": { "count": 1, "sibling": { "value": "kept" } },
        "untouched": { "value": 2 },
    })))
    .unwrap();
    let base = tracker.value();
    let change = tracker.begin_change();
    let first = change.state().unwrap().child("changed").unwrap();
    assert_eq!(change.state().unwrap().child("changed").unwrap(), first);
    change
        .state()
        .unwrap()
        .child("changed")
        .unwrap()
        .set("count", 3)
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert!(!prepared.value().strict_equals(&base));
    assert!(!prepared.value()["changed"].strict_equals(&base["changed"]));
    assert!(prepared.value()["changed"]["sibling"].strict_equals(&base["changed"]["sibling"]));
    assert!(prepared.value()["untouched"].strict_equals(&base["untouched"]));
}

#[test]
fn supports_frozen_bases_deletion_and_native_array_mutators() {
    let tracker = track(json(j!({ "optional": "remove", "values": [3, 1, 2] }))).unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.delete("optional").unwrap();
    let values = state.child("values").unwrap();
    values.push([4]).unwrap();
    assert!(values
        .pop()
        .unwrap()
        .unwrap()
        .as_value()
        .unwrap()
        .strict_equals(&int(4)));
    values.unshift([0]).unwrap();
    assert!(values
        .shift()
        .unwrap()
        .unwrap()
        .as_value()
        .unwrap()
        .strict_equals(&int(0)));
    let removed: Vec<JsonValue> = values
        .splice(1, 1, [5, 4])
        .unwrap()
        .iter()
        .map(|item| item.to_value().unwrap())
        .collect();
    assert_eq!(removed, vec![json(j!(1))]);
    values
        .sort_by(|left, right| number(left).total_cmp(&number(right)))
        .unwrap();
    values.reverse().unwrap();
    values.fill(9, 1, 3).unwrap();
    values.copy_within(1, 0, 2).unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value(), &json(j!({ "values": [5, 5, 9, 2] })));
}

#[test]
fn copies_inserted_draft_values_without_aliasing_their_original_handle() {
    let tracker = track(json(j!({ "values": [{ "value": 1 }, { "value": 2 }] }))).unwrap();
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    let held = values.child(0).unwrap();
    values.unshift([&held]).unwrap();
    held.set("value", 9).unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value()["values"],
        json(j!([{ "value": 1 }, { "value": 9 }, { "value": 2 }]))
    );
    assert!(!prepared.value()["values"][0].strict_equals(&prepared.value()["values"][1]));
}

#[test]
fn keeps_comparator_edits_when_sorting_object_drafts() {
    let tracker = track(json(j!({
        "rows": [{ "rank": 2, "comparisons": 0 }, { "rank": 1, "comparisons": 0 }],
    })))
    .unwrap();
    let change = tracker.begin_change();
    let increment = |item: &DraftItem| {
        let next = JsonValue::try_from(field(item, "comparisons") + 1.0).unwrap();
        item.as_draft().unwrap().set("comparisons", next).unwrap();
    };
    change
        .state()
        .unwrap()
        .child("rows")
        .unwrap()
        .sort_by(|left, right| {
            increment(left);
            increment(right);
            field(left, "rank").total_cmp(&field(right, "rank"))
        })
        .unwrap();
    let prepared = change.prepare().unwrap();
    let rows = prepared.value()["rows"].as_array().unwrap();
    assert_eq!(
        rows.iter()
            .map(|row| row["rank"].clone())
            .collect::<Vec<_>>(),
        vec![json(j!(1)), json(j!(2))]
    );
    assert_eq!(
        rows.iter()
            .map(|row| row["comparisons"].clone())
            .collect::<Vec<_>>(),
        vec![json(j!(1)), json(j!(1))]
    );
}

#[test]
fn drops_writes_through_detached_child_handles() {
    let tracker = track(json(j!({
        "child": { "value": "removed" },
        "items": [{ "value": "removed" }, { "value": "kept" }],
    })))
    .unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    let child = state.child("child").unwrap();
    let shifted = state.child("items").unwrap().shift().unwrap();
    state.delete("child").unwrap();
    child.set("value", "detached child").unwrap();
    if let Some(shifted) = shifted {
        shifted
            .as_draft()
            .unwrap()
            .set("value", "detached item")
            .unwrap();
    }
    assert_eq!(
        change.prepare().unwrap().value(),
        &json(j!({ "items": [{ "value": "kept" }] }))
    );
}

#[test]
fn inserts_100_000_items_without_argument_overflow() {
    for method in ["unshift", "splice"] {
        let tracker = track(json(j!({ "values": [-1] }))).unwrap();
        let change = tracker.begin_change();
        let values = change.state().unwrap().child("values").unwrap();
        let items = (0..100_000).map(int);
        if method == "unshift" {
            values.unshift(items).unwrap();
        } else {
            values.splice(1, 0, items).unwrap();
        }
        let prepared = change.prepare().unwrap();
        let result = &prepared.value()["values"];
        assert_eq!(result.as_array().unwrap().len(), 100_001, "{method}");
        let (first, last) = if method == "unshift" {
            (0, 99_999)
        } else {
            (1, 100_000)
        };
        assert!(result[first].strict_equals(&int(0)), "{method}");
        assert!(result[last].strict_equals(&int(99_999)), "{method}");
        assert_eq!(
            &apply_immutable(prepared.base(), prepared.ops()).unwrap(),
            prepared.value(),
            "{method}"
        );
    }
}

#[test]
fn rejects_non_strict_json_placements_without_mutating_the_draft_or_base() {
    let tracker = track(json(j!({ "number": 0, "payload": null, "values": [1, 2] }))).unwrap();
    let change = tracker.begin_change();
    assert!(matches!(
        JsonValue::try_from(f64::NAN),
        Err(JsonError::NonFinite)
    ));
    assert!(matches!(to_json(&f64::NAN), Err(JsonError::NonFinite)));
    assert_eq!(change.state().unwrap().value().unwrap(), tracker.value());
    change.abort();
    assert_eq!(
        tracker.value(),
        json(j!({ "number": 0, "payload": null, "values": [1, 2] }))
    );
}

#[test]
fn rejects_array_holes_without_mutating_the_committed_base() {
    let tracker = track(json(j!({ "values": [1, 2] }))).unwrap();
    let change = tracker.begin_change();
    let error = change
        .state()
        .unwrap()
        .child("values")
        .unwrap()
        .delete(0)
        .unwrap_err();
    assert!(matches!(error, TrackerError::ArrayHoles));
    assert!(error.to_string().contains("holes"), "{error}");
    change.abort();
    assert_eq!(tracker.value()["values"], json(j!([1, 2])));
}
