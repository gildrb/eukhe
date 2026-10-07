//! Port of `test/delta-diff.test.ts`. Shared JS objects become shared
//! `JsonValue` clones (same `Arc`), which is the identity diff aligns on.

mod common;

use common::{j, ops, ops_text, wire};
use eukhe_chord::delta::{apply_immutable, assert_valid_op, decoder, diff_revisions, encoder, Op};
use eukhe_chord::json::{JsonObject, JsonValue};

fn values(items: Vec<JsonValue>) -> JsonValue {
    JsonValue::from(JsonObject::from_iter([("values", JsonValue::from(items))]))
}

fn id(name: &str) -> JsonValue {
    j(&format!(r#"{{"id":"{name}"}}"#))
}

fn expect_diff(before: &JsonValue, after: &JsonValue, expected: &[Op]) {
    let operations = diff_revisions(before, after);
    assert_eq!(operations, expected);
    assert_eq!(&apply_immutable(before, &operations).unwrap(), after);
}

#[test]
fn emits_sets_and_deletes() {
    expect_diff(
        &j(r#"{"keep":1,"change":1,"remove":true}"#),
        &j(r#"{"keep":1,"change":2,"add":3}"#),
        &ops(r#"[["s",["change"],2],["s",["add"],3],["d",["remove"]]]"#),
    );
}

#[test]
fn emits_string_append_and_front_truncation() {
    expect_diff(
        &j(r#"{"text":"hello"}"#),
        &j(r#"{"text":"hello world"}"#),
        &ops(r#"[["a",["text"]," world"]]"#),
    );
    expect_diff(
        &j(r#"{"text":"hello world"}"#),
        &j(r#"{"text":"world"}"#),
        &ops(r#"[["t",["text"],6]]"#),
    );
    expect_diff(
        &j(r#"{"text":"abcdefgh"}"#),
        &j(r#"{"text":"defghxyz"}"#),
        &ops(r#"[["t",["text"],3],["a",["text"],"xyz"]]"#),
    );
}

#[test]
fn represents_array_insertion_removal_and_shift_with_splices() {
    let (a, b, c) = (id("a"), id("b"), id("c"));
    expect_diff(
        &values(vec![a.clone(), b.clone()]),
        &values(vec![a.clone(), c.clone(), b.clone()]),
        &[Op::Splice(vec!["values".into()], 1, 0, vec![c.clone()])],
    );
    expect_diff(
        &values(vec![a, b.clone(), c.clone()]),
        &values(vec![b, c]),
        &ops(r#"[["p",["values"],0,1,[]]]"#),
    );
}

#[test]
fn collapses_a_same_length_queue_update_to_two_splices() {
    let (a, b, c, d) = (id("a"), id("b"), id("c"), id("d"));
    expect_diff(
        &values(vec![a, b.clone(), c.clone()]),
        &values(vec![b, c, d.clone()]),
        &[
            Op::Splice(vec!["values".into()], 0, 1, Vec::new()),
            Op::Splice(vec!["values".into()], 2, 0, vec![d]),
        ],
    );
}

#[test]
fn emits_a_permutation_for_a_pure_reorder() {
    let (a, b, c) = (id("a"), id("b"), id("c"));
    expect_diff(
        &values(vec![a.clone(), b.clone(), c.clone()]),
        &values(vec![c, a, b]),
        &ops(r#"[["m",["values"],[2,0,1]]]"#),
    );
}

#[test]
fn normalizes_reordered_distinct_deeply_equal_objects_to_a_no_op() {
    let first = j(r#"{"nested":{"value":1}}"#);
    let second = j(r#"{"nested":{"value":1}}"#);
    assert!(!first.strict_equals(&second));
    assert!(diff_revisions(
        &values(vec![first.clone(), second.clone()]),
        &values(vec![second, first])
    )
    .is_empty());
}

#[test]
fn validates_and_encodes_permutations() {
    let operations = ops(r#"[["m",["values"],[2,0,1]],["m",["values"],[1,2,0]]]"#);
    for operation in &operations {
        assert_valid_op(&operation.to_json()).unwrap();
    }
    let encoded = encoder().encode(&operations);
    assert_eq!(encoded, wire(r#"[["m",["values"],[2,0,1]],["m",[1,2,0]]]"#));
    for operation in &encoded {
        eukhe_chord::delta::assert_valid_wire_op(&operation.to_json()).unwrap();
    }
    assert_eq!(decoder().decode(&encoded).unwrap(), operations);
    assert_eq!(
        assert_valid_op(&j(r#"["m",["values"],[0,0]]"#))
            .unwrap_err()
            .to_string(),
        "m permutation is not a bijection"
    );
}

#[test]
fn emits_nothing_for_deeply_equal_reconstructed_values() {
    assert!(diff_revisions(
        &j(r#"{"value":{"nested":[1,2]}}"#),
        &j(r#"{"value":{"nested":[1,2]}}"#)
    )
    .is_empty());
    assert!(diff_revisions(
        &j(r#"{"values":[{"id":1},{"id":2}]}"#),
        &j(r#"{"values":[{"id":1},{"id":2}]}"#)
    )
    .is_empty());
    assert!(diff_revisions(
        &j(r#"{"values":[true,true,true]}"#),
        &j(r#"{"values":[true,true,true]}"#)
    )
    .is_empty());
}

#[test]
fn keeps_a_leaf_edit_inside_a_reconstructed_array_narrow() {
    expect_diff(
        &j(r#"{"values":[{"id":1,"label":"one"},{"id":2,"label":"two"}]}"#),
        &j(r#"{"values":[{"id":1,"label":"one"},{"id":2,"label":"changed"}]}"#),
        &ops(r#"[["s",["values",1,"label"],"changed"]]"#),
    );
}

#[test]
#[allow(clippy::many_single_char_names)] // the TS fixture names
fn emits_payload_free_splices_for_scattered_removals() {
    let [a, b, c, d, e] = ["a", "b", "c", "d", "e"].map(id);
    expect_diff(
        &values(vec![a.clone(), b, c.clone(), d, e.clone()]),
        &values(vec![a, c, e]),
        &ops(r#"[["p",["values"],1,1,[]],["p",["values"],2,1,[]]]"#),
    );
}

#[test]
fn encodes_removal_canonically() {
    for (before, after, expected) in [
        ("[1,2,3,4]", "[2,3,4]", r#"[["p",["values"],0,1,[]]]"#),
        ("[1,2,3,4]", "[1,2,3]", r#"[["p",["values"],3,1,[]]]"#),
        ("[1,2,3,4]", "[1,3,4]", r#"[["p",["values"],1,1,[]]]"#),
        ("[1,2,3,4]", "[]", r#"[["p",["values"],0,4,[]]]"#),
        ("[1,2,3,4]", "[1,2,3,4]", "[]"),
    ] {
        expect_diff(
            &j(&format!(r#"{{"values":{before}}}"#)),
            &j(&format!(r#"{{"values":{after}}}"#)),
            &ops(expected),
        );
    }
}

#[test]
fn does_not_field_diff_unrelated_shifted_objects_with_common_fields() {
    let row = |value: i32| j(&format!(r#"{{"type":"row","value":{value}}}"#));
    expect_diff(
        &values(vec![row(1), row(2), row(3)]),
        &values(vec![row(2), row(3), row(4)]),
        &ops(r#"[["p",["values"],0,1,[]],["p",["values"],2,0,[{"type":"row","value":4}]]]"#),
    );
}

#[test]
fn does_not_treat_coincidental_id_or_key_fields_as_structural_identity() {
    let left = j(r#"{"value":"left"}"#);
    let right = j(r#"{"value":"right"}"#);
    let before = vec![
        left.clone(),
        j(r#"{"id":1,"key":"a","value":"first"}"#),
        j(r#"{"id":2,"key":"b","value":"second"}"#),
        right.clone(),
    ];
    let replacements = vec![
        j(r#"{"id":2,"key":"b","value":"edited-second"}"#),
        j(r#"{"id":1,"key":"a","value":"edited-first"}"#),
    ];
    let after = vec![
        left,
        replacements[0].clone(),
        replacements[1].clone(),
        right,
    ];
    expect_diff(
        &values(before),
        &values(after),
        &[Op::Splice(vec!["values".into()], 1, 2, replacements)],
    );
}

#[test]
fn combines_removals_append_and_a_shared_subtree_survivor_edit() {
    let item = |name: &str| {
        j(&format!(
            r#"{{"id":"{name}","stable":{{}},"detail":{{"text":"{name}"}}}}"#
        ))
    };
    let (a, b, c, d) = (item("a"), item("b"), item("c"), item("d"));
    let changed_c = JsonValue::from(JsonObject::from_iter([
        ("id", JsonValue::from("c")),
        ("stable", c["stable"].clone()),
        ("detail", j(r#"{"text":"changed"}"#)),
    ]));
    let appended = item("e");
    expect_diff(
        &values(vec![a.clone(), b, c, d.clone()]),
        &values(vec![a, changed_c, d, appended.clone()]),
        &[
            Op::Splice(vec!["values".into()], 1, 1, Vec::new()),
            Op::Append(
                vec!["values".into(), 1.into(), "detail".into(), "text".into()],
                "hanged".to_owned(),
            ),
            Op::Splice(vec!["values".into()], 3, 0, vec![appended]),
        ],
    );
}

#[test]
fn does_not_retain_a_removed_neighbor_payload() {
    for size in [256 * 1024, 1024 * 1024] {
        let payload = JsonValue::from("x".repeat(size));
        let retained: Vec<JsonValue> = ["a", "b", "c", "d", "e"]
            .iter()
            .map(|name| {
                JsonValue::from(JsonObject::from_iter([
                    ("id", JsonValue::from(*name)),
                    ("payload", payload.clone()),
                ]))
            })
            .collect();
        let before = values(retained.clone());
        let after = values(vec![
            retained[0].clone(),
            retained[2].clone(),
            retained[4].clone(),
        ]);
        let operations = diff_revisions(&before, &after);
        assert_eq!(
            operations,
            ops(r#"[["p",["values"],1,1,[]],["p",["values"],2,1,[]]]"#)
        );
        assert!(ops_text(&operations).len() < 100);
        assert_eq!(apply_immutable(&before, &operations).unwrap(), after);
        assert_eq!(before["values"], JsonValue::from(retained));
    }
}

#[test]
fn keeps_push_pop_and_middle_removal_narrow() {
    for size in [1_001_usize, 10_000] {
        let items: Vec<JsonValue> = (0..size)
            .map(|value| j(&format!(r#"{{"value":{value}}}"#)))
            .collect();
        let appended = j(&format!(r#"{{"value":{size}}}"#));
        let mut pushed = items.clone();
        pushed.push(appended.clone());
        expect_diff(
            &values(items.clone()),
            &values(pushed),
            &[Op::Splice(vec!["values".into()], size, 0, vec![appended])],
        );
        expect_diff(
            &values(items.clone()),
            &values(items[..size - 1].to_vec()),
            &[Op::Splice(vec!["values".into()], size - 1, 1, Vec::new())],
        );
        let middle = size / 2;
        let mut removed = items.clone();
        removed.remove(middle);
        expect_diff(
            &values(items),
            &values(removed),
            &[Op::Splice(vec!["values".into()], middle, 1, Vec::new())],
        );
    }
}

#[test]
fn keeps_forty_thousand_row_sparse_edits_narrow() {
    let items: Vec<JsonValue> = (0..40_000)
        .map(|value| {
            j(&format!(
                r#"{{"value":{value},"stable":{{"value":{value}}}}}"#
            ))
        })
        .collect();
    let mut after = items.clone();
    let mut changed = Vec::new();
    for index in (100..after.len()).step_by(400) {
        let negative = -i32::try_from(index).unwrap();
        after[index] = JsonValue::from(JsonObject::from_iter([
            ("value", JsonValue::from(negative)),
            ("stable", items[index]["stable"].clone()),
        ]));
        changed.push((index, negative));
    }
    let operations = diff_revisions(&values(items.clone()), &values(after.clone()));
    let expected: Vec<Op> = changed
        .iter()
        .map(|(index, value)| {
            Op::Set(
                vec!["values".into(), (*index).into(), "value".into()],
                JsonValue::from(*value),
            )
        })
        .collect();
    assert_eq!(operations, expected);
    assert!(ops_text(&operations).len() < 7_500);
    assert_eq!(
        apply_immutable(&values(items), &operations).unwrap(),
        values(after)
    );
}

#[test]
fn keeps_a_reconstructed_large_array_leaf_edit_narrow() {
    let before: Vec<JsonValue> = (0..1_000)
        .map(|value| j(&format!(r#"{{"value":{value},"label":"row-{value}"}}"#)))
        .collect();
    let mut after: Vec<JsonValue> = before.iter().map(common::clone).collect();
    after[700] = j(r#"{"value":700,"label":"changed"}"#);
    let operations = diff_revisions(&values(before.clone()), &values(after.clone()));
    assert_eq!(
        operations,
        ops(r#"[["s",["values",700,"label"],"changed"]]"#)
    );
    assert!(ops_text(&operations).len() < 100);
    assert_eq!(
        apply_immutable(&values(before), &operations).unwrap(),
        values(after)
    );
}

#[test]
fn splices_an_ambiguous_equal_count_moved_and_edited_gap() {
    let left = j(r#"{"value":"left"}"#);
    let right = j(r#"{"value":"right"}"#);
    let before = vec![
        left.clone(),
        j(r#"{"id":1,"value":"a"}"#),
        j(r#"{"id":2,"value":"b"}"#),
        right.clone(),
    ];
    let replacements = vec![
        j(r#"{"id":2,"value":"edited"}"#),
        j(r#"{"id":1,"value":"also-edited"}"#),
    ];
    let after = vec![
        left,
        replacements[0].clone(),
        replacements[1].clone(),
        right,
    ];
    expect_diff(
        &values(before),
        &values(after),
        &[Op::Splice(vec!["values".into()], 1, 2, replacements)],
    );
}

#[test]
fn keeps_a_large_rotation_payload_free() {
    let items: Vec<JsonValue> = (0..10_000)
        .map(|value| j(&format!(r#"{{"value":{value}}}"#)))
        .collect();
    let rotated: Vec<JsonValue> = items[1_000..]
        .iter()
        .chain(&items[..1_000])
        .cloned()
        .collect();
    let operations = diff_revisions(&values(items.clone()), &values(rotated.clone()));
    assert_eq!(operations.len(), 1);
    assert_eq!(operations[0].verb(), "m");
    assert!(ops_text(&operations).len() < 60_000);
    assert_eq!(
        apply_immutable(&values(items), &operations).unwrap(),
        values(rotated)
    );
}

#[test]
fn encodes_five_hundred_unshifts_without_snapshotting_retained_rows() {
    let retained: Vec<JsonValue> = (0..10_000)
        .map(|value| {
            j(&format!(
                r#"{{"value":{value},"payload":"{}"}}"#,
                "x".repeat(100)
            ))
        })
        .collect();
    let inserted: Vec<JsonValue> = (0..500)
        .map(|value| j(&format!(r#"{{"value":{}}}"#, -value - 1)))
        .collect();
    let combined: Vec<JsonValue> = inserted.iter().chain(&retained).cloned().collect();
    let operations = diff_revisions(&values(retained.clone()), &values(combined.clone()));
    assert_eq!(
        operations,
        [Op::Splice(vec!["values".into()], 0, 0, inserted)]
    );
    assert!(ops_text(&operations).len() < 20_000);
    assert_eq!(
        apply_immutable(&values(retained), &operations).unwrap(),
        values(combined)
    );
}

#[test]
fn bounds_wide_object_operation_emission_with_a_root_replacement() {
    let before: JsonValue = (0..20_000)
        .map(|index| (format!("field{index}"), JsonValue::from(0)))
        .collect::<JsonObject>()
        .into();
    let after: JsonValue = (0..20_000)
        .map(|index| (format!("field{index}"), JsonValue::from(1)))
        .collect::<JsonObject>()
        .into();
    assert_eq!(diff_revisions(&before, &after), [Op::Replace(after)]);
}

#[test]
fn bounds_a_wide_normalized_array_fallback_with_a_root_replacement() {
    let before = values(vec![JsonValue::from(0); 40_000]);
    let after = values(vec![JsonValue::from(1); 40_000]);
    let operations = diff_revisions(&before, &after);
    assert_eq!(operations, [Op::Replace(after.clone())]);
    assert_eq!(apply_immutable(&before, &operations).unwrap(), after);
}
