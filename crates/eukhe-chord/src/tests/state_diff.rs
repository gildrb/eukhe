//! Port of `test/state-diff.test.ts`.
//!
//! TS object identity (the same object literal placed in `before` and
//! `after`) maps to cloning one `JsonValue`, which shares its `Arc`
//! container. `Object.freeze` in "does not retain a removed-neighbor payload"
//! has no counterpart: `JsonValue` is immutable by type.

use serde_json::json as j;

use super::{json, ops_json};
use crate::delta::{
    apply_immutable, assert_valid_op, assert_valid_wire_op, decoder, diff_revisions, encoder, Op,
    WireOp,
};
use crate::json::{copy_json, JsonObject, JsonValue};

/// A shared `JsonValue` embedded in a `serde_json` literal.
fn sj(value: &JsonValue) -> serde_json::Value {
    serde_json::Value::from(value)
}

/// An array sharing the given containers.
fn array(items: &[JsonValue]) -> JsonValue {
    JsonValue::from(items.to_vec())
}

/// `{ values: items }` sharing the given containers.
fn values(items: &[JsonValue]) -> JsonValue {
    JsonValue::from(
        [("values", array(items))]
            .into_iter()
            .collect::<JsonObject>(),
    )
}

fn number(value: usize) -> JsonValue {
    JsonValue::try_from(value).unwrap()
}

fn negative(value: usize) -> JsonValue {
    JsonValue::try_from(-i64::try_from(value).unwrap()).unwrap()
}

fn expect_diff(before: &JsonValue, after: &JsonValue, expected: &JsonValue) {
    let operations = diff_revisions(before, after);
    assert_eq!(&ops_json(&operations), expected);
    assert_eq!(&apply_immutable(before, &operations).unwrap(), after);
}

#[test]
fn emits_sets_and_deletes() {
    expect_diff(
        &json(j!({ "keep": 1, "change": 1, "remove": true })),
        &json(j!({ "keep": 1, "change": 2, "add": 3 })),
        &json(j!([
            ["s", ["change"], 2],
            ["s", ["add"], 3],
            ["d", ["remove"]]
        ])),
    );
}

#[test]
fn emits_string_append_and_front_truncation() {
    expect_diff(
        &json(j!({ "text": "hello" })),
        &json(j!({ "text": "hello world" })),
        &json(j!([["a", ["text"], " world"]])),
    );
    expect_diff(
        &json(j!({ "text": "hello world" })),
        &json(j!({ "text": "world" })),
        &json(j!([["t", ["text"], 6]])),
    );
    expect_diff(
        &json(j!({ "text": "abcdefgh" })),
        &json(j!({ "text": "defghxyz" })),
        &json(j!([["t", ["text"], 3], ["a", ["text"], "xyz"]])),
    );
}

#[test]
fn represents_array_insertion_removal_and_shift_with_splices() {
    let a = json(j!({ "id": "a" }));
    let b = json(j!({ "id": "b" }));
    let c = json(j!({ "id": "c" }));
    expect_diff(
        &values(&[a.clone(), b.clone()]),
        &values(&[a.clone(), c.clone(), b.clone()]),
        &json(j!([["p", ["values"], 1, 0, [sj(&c)]]])),
    );
    expect_diff(
        &values(&[a, b.clone(), c.clone()]),
        &values(&[b, c]),
        &json(j!([["p", ["values"], 0, 1, []]])),
    );
}

#[test]
fn collapses_a_same_length_queue_update_to_two_splices() {
    let a = json(j!({ "id": "a" }));
    let b = json(j!({ "id": "b" }));
    let c = json(j!({ "id": "c" }));
    let d = json(j!({ "id": "d" }));
    expect_diff(
        &values(&[a, b.clone(), c.clone()]),
        &values(&[b, c, d.clone()]),
        &json(j!([
            ["p", ["values"], 0, 1, []],
            ["p", ["values"], 2, 0, [sj(&d)]]
        ])),
    );
}

#[test]
fn emits_a_permutation_for_a_pure_reorder() {
    let a = json(j!({ "id": "a" }));
    let b = json(j!({ "id": "b" }));
    let c = json(j!({ "id": "c" }));
    expect_diff(
        &values(&[a.clone(), b.clone(), c.clone()]),
        &values(&[c, a, b]),
        &json(j!([["m", ["values"], [2, 0, 1]]])),
    );
}

#[test]
fn normalizes_reordered_distinct_deeply_equal_objects_to_a_no_op() {
    let first = json(j!({ "nested": { "value": 1 } }));
    let second = json(j!({ "nested": { "value": 1 } }));
    assert!(!first.strict_equals(&second));
    assert_eq!(
        diff_revisions(
            &values(&[first.clone(), second.clone()]),
            &values(&[second, first])
        ),
        Vec::<Op>::new()
    );
}

#[test]
fn validates_and_encodes_permutations() {
    let operations = vec![
        Op::from_json(&json(j!(["m", ["values"], [2, 0, 1]]))).unwrap(),
        Op::from_json(&json(j!(["m", ["values"], [1, 2, 0]]))).unwrap(),
    ];
    for operation in &operations {
        assert_valid_op(&operation.to_json()).unwrap();
    }
    let wire = encoder().encode(&operations);
    assert_eq!(
        wire.iter().map(WireOp::to_json).collect::<JsonValue>(),
        json(j!([["m", ["values"], [2, 0, 1]], ["m", [1, 2, 0]]]))
    );
    for operation in &wire {
        assert_valid_wire_op(&operation.to_json()).unwrap();
    }
    assert_eq!(decoder().decode(&wire).unwrap(), operations);
    let error = assert_valid_op(&json(j!(["m", ["values"], [0, 0]]))).unwrap_err();
    assert!(error.to_string().contains("bijection"), "{error}");
}

#[test]
fn emits_nothing_for_deeply_equal_reconstructed_values() {
    assert_eq!(
        diff_revisions(
            &json(j!({ "value": { "nested": [1, 2] } })),
            &json(j!({ "value": { "nested": [1, 2] } }))
        ),
        Vec::<Op>::new()
    );
    assert_eq!(
        diff_revisions(
            &json(j!({ "values": [{ "id": 1 }, { "id": 2 }] })),
            &json(j!({ "values": [{ "id": 1 }, { "id": 2 }] }))
        ),
        Vec::<Op>::new()
    );
    assert_eq!(
        diff_revisions(
            &json(j!({ "values": [true, true, true] })),
            &json(j!({ "values": [true, true, true] }))
        ),
        Vec::<Op>::new()
    );
}

#[test]
fn keeps_a_leaf_edit_inside_a_reconstructed_array_narrow() {
    expect_diff(
        &json(j!({ "values": [{ "id": 1, "label": "one" }, { "id": 2, "label": "two" }] })),
        &json(j!({ "values": [{ "id": 1, "label": "one" }, { "id": 2, "label": "changed" }] })),
        &json(j!([["s", ["values", 1, "label"], "changed"]])),
    );
}

#[test]
fn emits_payload_free_splices_for_scattered_removals() {
    let [id_a, id_b, id_c, id_d, id_e] = ["a", "b", "c", "d", "e"].map(|id| json(j!({ "id": id })));
    expect_diff(
        &values(&[id_a.clone(), id_b, id_c.clone(), id_d, id_e.clone()]),
        &values(&[id_a, id_c, id_e]),
        &json(j!([
            ["p", ["values"], 1, 1, []],
            ["p", ["values"], 2, 1, []]
        ])),
    );
}

#[test]
fn encodes_removal_canonically() {
    let cases = [
        (
            "front",
            j!([1, 2, 3, 4]),
            j!([2, 3, 4]),
            j!([["p", ["values"], 0, 1, []]]),
        ),
        (
            "tail",
            j!([1, 2, 3, 4]),
            j!([1, 2, 3]),
            j!([["p", ["values"], 3, 1, []]]),
        ),
        (
            "middle",
            j!([1, 2, 3, 4]),
            j!([1, 3, 4]),
            j!([["p", ["values"], 1, 1, []]]),
        ),
        (
            "all",
            j!([1, 2, 3, 4]),
            j!([]),
            j!([["p", ["values"], 0, 4, []]]),
        ),
        ("none", j!([1, 2, 3, 4]), j!([1, 2, 3, 4]), j!([])),
    ];
    for (name, before, after, expected) in cases {
        let operations = diff_revisions(
            &json(j!({ "values": before })),
            &json(j!({ "values": after })),
        );
        assert_eq!(ops_json(&operations), json(expected), "{name}");
        assert_eq!(
            apply_immutable(&json(j!({ "values": before })), &operations).unwrap(),
            json(j!({ "values": after })),
            "{name}"
        );
    }
}

#[test]
fn does_not_field_diff_unrelated_shifted_objects_with_common_fields() {
    let before: Vec<_> = [1, 2, 3]
        .map(|value| json(j!({ "type": "row", "value": value })))
        .into();
    let after: Vec<_> = [2, 3, 4]
        .map(|value| json(j!({ "type": "row", "value": value })))
        .into();
    expect_diff(
        &values(&before),
        &values(&after),
        &json(j!([
            ["p", ["values"], 0, 1, []],
            ["p", ["values"], 2, 0, [{ "type": "row", "value": 4 }]]
        ])),
    );
}

#[test]
fn does_not_treat_coincidental_id_or_key_fields_as_structural_identity() {
    let left = json(j!({ "value": "left" }));
    let right = json(j!({ "value": "right" }));
    let before = [
        left.clone(),
        json(j!({ "id": 1, "key": "a", "value": "first" })),
        json(j!({ "id": 2, "key": "b", "value": "second" })),
        right.clone(),
    ];
    let replacements = [
        json(j!({ "id": 2, "key": "b", "value": "edited-second" })),
        json(j!({ "id": 1, "key": "a", "value": "edited-first" })),
    ];
    let after = [
        left,
        replacements[0].clone(),
        replacements[1].clone(),
        right,
    ];
    expect_diff(
        &values(&before),
        &values(&after),
        &json(j!([["p", ["values"], 1, 2, sj(&array(&replacements))]])),
    );
}

#[test]
fn combines_removals_append_and_a_shared_subtree_survivor_edit() {
    let a = json(j!({ "id": "a", "stable": {}, "detail": { "text": "a" } }));
    let b = json(j!({ "id": "b", "stable": {}, "detail": { "text": "b" } }));
    let c = json(j!({ "id": "c", "stable": {}, "detail": { "text": "c" } }));
    let d = json(j!({ "id": "d", "stable": {}, "detail": { "text": "d" } }));
    let changed_c = JsonValue::from(
        [
            ("id", json(j!("c"))),
            ("stable", c["stable"].clone()),
            ("detail", json(j!({ "text": "changed" }))),
        ]
        .into_iter()
        .collect::<JsonObject>(),
    );
    let appended = json(j!({ "id": "e", "stable": {}, "detail": { "text": "e" } }));
    expect_diff(
        &values(&[a.clone(), b, c, d.clone()]),
        &values(&[a, changed_c, d, appended.clone()]),
        &json(j!([
            ["p", ["values"], 1, 1, []],
            ["a", ["values", 1, "detail", "text"], "hanged"],
            ["p", ["values"], 3, 0, [sj(&appended)]]
        ])),
    );
}

#[test]
fn does_not_retain_a_removed_neighbor_payload() {
    for size in [256 * 1024, 1024 * 1024] {
        let payload = "x".repeat(size);
        let retained =
            ["a", "b", "c", "d", "e"].map(|id| json(j!({ "id": id, "payload": payload })));
        let before = values(&retained);
        let after = values(&[
            retained[0].clone(),
            retained[2].clone(),
            retained[4].clone(),
        ]);
        let operations = diff_revisions(&before, &after);
        assert_eq!(
            ops_json(&operations),
            json(j!([
                ["p", ["values"], 1, 1, []],
                ["p", ["values"], 2, 1, []]
            ])),
            "{size}"
        );
        assert!(ops_json(&operations).to_string().len() < 100, "{size}");
        assert_eq!(
            apply_immutable(&before, &operations).unwrap(),
            after,
            "{size}"
        );
        assert_eq!(before["values"], array(&retained), "{size}");
    }
}

#[test]
fn keeps_push_pop_and_middle_removal_narrow() {
    for size in [1_001, 10_000] {
        let items: Vec<JsonValue> = (0..size)
            .map(|value| json(j!({ "value": value })))
            .collect();
        let before = values(&items);
        let appended = json(j!({ "value": size }));
        let mut pushed = items.clone();
        pushed.push(appended.clone());
        expect_diff(
            &before,
            &values(&pushed),
            &json(j!([["p", ["values"], size, 0, [sj(&appended)]]])),
        );
        expect_diff(
            &before,
            &values(&items[..size - 1]),
            &json(j!([["p", ["values"], size - 1, 1, []]])),
        );
        let middle = size / 2;
        let mut removed = items.clone();
        removed.remove(middle);
        expect_diff(
            &before,
            &values(&removed),
            &json(j!([["p", ["values"], middle, 1, []]])),
        );
    }
}

#[test]
fn keeps_forty_thousand_row_sparse_edits_narrow() {
    let items: Vec<JsonValue> = (0..40_000)
        .map(|value| json(j!({ "value": value, "stable": { "value": value } })))
        .collect();
    let mut after = items.clone();
    let mut changed = Vec::new();
    for index in (100..after.len()).step_by(400) {
        after[index] = JsonValue::from(
            [
                ("value", negative(index)),
                ("stable", items[index]["stable"].clone()),
            ]
            .into_iter()
            .collect::<JsonObject>(),
        );
        changed.push(index);
    }
    let operations = diff_revisions(&values(&items), &values(&after));
    assert_eq!(
        ops_json(&operations),
        changed
            .iter()
            .map(|&index| json(j!(["s", ["values", index, "value"], sj(&negative(index))])))
            .collect::<JsonValue>()
    );
    assert!(ops_json(&operations).to_string().len() < 7_500);
    assert_eq!(
        apply_immutable(&values(&items), &operations).unwrap(),
        values(&after)
    );
}

#[test]
fn keeps_a_reconstructed_large_array_leaf_edit_narrow() {
    let before: Vec<JsonValue> = (0..1_000)
        .map(|value| json(j!({ "value": value, "label": format!("row-{value}") })))
        .collect();
    let mut after: Vec<JsonValue> = before.iter().map(copy_json).collect();
    after[700]
        .as_object_mut()
        .unwrap()
        .insert("label", json(j!("changed")));
    let operations = diff_revisions(&values(&before), &values(&after));
    assert_eq!(
        ops_json(&operations),
        json(j!([["s", ["values", 700, "label"], "changed"]]))
    );
    assert!(ops_json(&operations).to_string().len() < 100);
    assert_eq!(
        apply_immutable(&values(&before), &operations).unwrap(),
        values(&after)
    );
}

#[test]
fn splices_an_ambiguous_equal_count_moved_and_edited_gap() {
    let left = json(j!({ "value": "left" }));
    let right = json(j!({ "value": "right" }));
    let before = [
        left.clone(),
        json(j!({ "id": 1, "value": "a" })),
        json(j!({ "id": 2, "value": "b" })),
        right.clone(),
    ];
    let replacements = [
        json(j!({ "id": 2, "value": "edited" })),
        json(j!({ "id": 1, "value": "also-edited" })),
    ];
    let after = [
        left,
        replacements[0].clone(),
        replacements[1].clone(),
        right,
    ];
    expect_diff(
        &values(&before),
        &values(&after),
        &json(j!([["p", ["values"], 1, 2, sj(&array(&replacements))]])),
    );
}

#[test]
fn encodes_five_hundred_unshifts_without_snapshotting_retained_rows() {
    let payload = "x".repeat(100);
    let retained: Vec<JsonValue> = (0..10_000)
        .map(|value| json(j!({ "value": value, "payload": payload })))
        .collect();
    let inserted: Vec<JsonValue> = (0..500)
        .map(|value| json(j!({ "value": -value - 1 })))
        .collect();
    let combined: Vec<JsonValue> = inserted.iter().chain(&retained).cloned().collect();
    let operations = diff_revisions(&values(&retained), &values(&combined));
    assert_eq!(
        ops_json(&operations),
        json(j!([["p", ["values"], 0, 0, sj(&array(&inserted))]]))
    );
    assert!(ops_json(&operations).to_string().len() < 20_000);
    assert_eq!(
        apply_immutable(&values(&retained), &operations).unwrap(),
        values(&combined)
    );
}

#[test]
fn bounds_wide_object_operation_emission_with_a_root_replacement() {
    let mut before = JsonObject::new();
    let mut after = JsonObject::new();
    for index in 0..20_000 {
        before.insert(format!("field{index}"), number(0));
        after.insert(format!("field{index}"), number(1));
    }
    let after = JsonValue::from(after);
    assert_eq!(
        ops_json(&diff_revisions(&JsonValue::from(before), &after)),
        json(j!([["r", sj(&after)]]))
    );
}

#[test]
fn falls_back_to_a_base_operation_when_leaf_operations_are_larger() {
    let before = json(j!({ "values": vec![0; 40_000] }));
    let after = json(j!({ "values": vec![1; 40_000] }));
    let operations = diff_revisions(&before, &after);
    assert_eq!(ops_json(&operations), json(j!([["r", sj(&after)]])));
}
