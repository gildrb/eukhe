//! Port of `test/delta-apply-immutable.test.ts`.
//!
//! Mapped: `Object.freeze` inputs become plain values (immutable by type);
//! the getter-trap read counter has no Rust counterpart (no accessors); the
//! "copies a wide object once" check counted `Object.keys` calls, which in
//! Rust is `Arc::make_mut` copying the object once per scope, so it checks
//! the result and the untouched base instead.

mod common;

use common::{clone, j, ops};
use eukhe_chord::delta::{
    apply, apply_immutable, apply_immutable_batches, track, try_apply_immutable_batches,
    DeltaError, Op, Seg,
};
use eukhe_chord::json::{JsonObject, JsonValue};

fn key(name: &str) -> Seg {
    Seg::from(name)
}

fn object(entries: Vec<(&str, JsonValue)>) -> JsonValue {
    JsonValue::from(entries.into_iter().collect::<JsonObject>())
}

#[test]
fn copies_each_touched_container_once_while_preserving_input_and_payload_ownership() {
    let shared = j(r#"{"nested":{"value":1}}"#);
    let untouched = j(r#"{"value":9}"#);
    let row_payload = j(r#"{"id":4,"label":"placed"}"#);
    let base = j(
        r#"{"text":"abcdef","stable":{"value":7},"branch":{"value":1},"copy":null,"placed":null,"untouched":null,"left":null,"right":null,"meta":{"count":0,"obsolete":true},"rows":[{"id":1,"label":"one"},{"id":2,"label":"two"},{"id":3,"label":"three"}]}"#,
    );
    let set = |path: &[&str], value: JsonValue| {
        Op::Set(path.iter().map(|segment| key(segment)).collect(), value)
    };
    let operations = vec![
        Op::Truncate(vec![key("text")], 2),
        Op::Append(vec![key("text")], "!".to_owned()),
        set(&["meta", "count"], JsonValue::from(1)),
        set(&["meta", "count"], JsonValue::from(2)),
        Op::Delete(vec![key("meta"), key("obsolete")]),
        set(&["copy"], base["branch"].clone()),
        set(&["copy", "value"], JsonValue::from(2)),
        set(&["placed"], shared.clone()),
        Op::Set(
            vec![key("placed"), key("nested"), key("value")],
            JsonValue::from(2),
        ),
        set(&["untouched"], untouched.clone()),
        set(&["left"], shared.clone()),
        set(&["right"], shared.clone()),
        set(&["left", "nested", "value"], JsonValue::from(3)),
        Op::Splice(vec![key("rows")], 1, 1, vec![row_payload.clone()]),
        Op::Set(
            vec![key("rows"), Seg::Index(1), key("label")],
            JsonValue::from("edited"),
        ),
        Op::Move(vec![key("rows")], vec![1, 0, 2]),
        Op::Set(
            vec![key("rows"), Seg::Index(0), key("label")],
            JsonValue::from("moved"),
        ),
    ];

    let result = apply_immutable(&base, &operations).unwrap();
    let mutable_result = apply(clone(&base), &operations).unwrap();

    assert_eq!(result, mutable_result);
    assert_eq!(result["text"], JsonValue::from("cdef!"));
    assert!(result["stable"].strict_equals(&base["stable"]));
    assert!(result["untouched"].strict_equals(&untouched));
    assert!(!result["copy"].strict_equals(&base["branch"]));
    assert_eq!(result["copy"], j(r#"{"value":2}"#));
    assert!(!result["placed"].strict_equals(&shared));
    assert_eq!(result["placed"], j(r#"{"nested":{"value":2}}"#));
    assert!(!result["left"].strict_equals(&shared));
    assert!(result["right"].strict_equals(&shared));
    assert!(!result["rows"][0].strict_equals(&row_payload));
    assert_eq!(result["rows"][0], j(r#"{"id":4,"label":"moved"}"#));
    assert_eq!(base["branch"]["value"], JsonValue::from(1));
    assert_eq!(shared["nested"]["value"], JsonValue::from(1));
    assert_eq!(row_payload["label"], JsonValue::from("placed"));
}

#[test]
fn protects_root_replacement_payloads_before_later_object_and_array_edits() {
    let replacement = j(r#"{"nested":{"value":1},"values":[1,2,3]}"#);
    let result = apply_immutable_batches(
        &JsonValue::Null,
        [
            vec![Op::Replace(replacement.clone())],
            ops(r#"[["s",["nested","value"],2]]"#),
            ops(r#"[["p",["values"],1,1,[4,5]],["m",["values"],[3,0,1,2]]]"#),
        ],
    )
    .unwrap();
    assert_eq!(result, j(r#"{"nested":{"value":2},"values":[3,1,4,5]}"#));
    assert_eq!(replacement, j(r#"{"nested":{"value":1},"values":[1,2,3]}"#));

    let array = j("[1,2,3]");
    let array_result = apply_immutable(
        &array,
        &ops(r#"[["p",[],1,1,[4,5]],["m",[],[3,0,1,2]],["d",[1]]]"#),
    )
    .unwrap();
    assert_eq!(array_result, j("[3,4,5]"));
    assert_eq!(array, j("[1,2,3]"));
}

#[test]
fn shares_one_private_copy_on_write_scope_across_batch_partitions() {
    let base = j(
        r#"{"text":"abcdef","meta":{"count":0},"values":[{"id":1,"value":1},{"id":2,"value":2},{"id":3,"value":3}]}"#,
    );
    let batches = [
        ops(r#"[["s",["meta","count"],1],["p",["values"],1,1,[{"id":4,"value":4}]]]"#),
        Vec::new(),
        ops(r#"[["m",["values"],[2,0,1]],["s",["values",2,"value"],40]]"#),
        ops(r#"[["t",["text"],2],["a",["text"],"!"]]"#),
    ];
    let intermediate = apply_immutable(&base, &batches[0]).unwrap();
    let intermediate_snapshot = clone(&intermediate);
    let mut sequential = intermediate.clone();
    for batch in &batches[1..] {
        sequential = apply_immutable(&sequential, batch).unwrap();
    }
    let streamed = apply_immutable_batches(&base, &batches).unwrap();
    let flattened = apply_immutable(&base, &batches.concat()).unwrap();
    assert_eq!(streamed, sequential);
    assert_eq!(streamed, flattened);
    assert_eq!(intermediate, intermediate_snapshot);
    assert_eq!(base["meta"]["count"], JsonValue::from(0));
    assert_eq!(base["values"][1]["id"], JsonValue::from(2));
}

#[test]
fn handles_tracker_produced_batches_across_arbitrary_revision_boundaries() {
    let values: Vec<JsonValue> = (0..8)
        .map(|id| {
            object(vec![
                ("id", JsonValue::from(id)),
                ("score", JsonValue::from(0)),
            ])
        })
        .collect();
    let initial = object(vec![
        ("text", JsonValue::from("start")),
        ("values", JsonValue::from(values)),
        ("revision", JsonValue::from(0)),
    ]);
    let tracker = track(initial.clone()).unwrap();
    let mut batches: Vec<Vec<Op>> = Vec::new();
    for revision in 1..=40_i32 {
        let change = tracker.begin_change();
        let state = change.state().unwrap();
        state.set("revision", revision).unwrap();
        let text = state.get("text").unwrap().unwrap().to_value().unwrap();
        let text = text.as_str().unwrap();
        state
            .set("text", format!("{}{revision}", &text[1..]))
            .unwrap();
        let values = state.child("values").unwrap();
        match revision % 5 {
            0 => {
                values.reverse().unwrap();
            }
            1 => {
                values
                    .push([object(vec![
                        ("id", JsonValue::from(100 + revision)),
                        ("score", JsonValue::from(revision)),
                    ])])
                    .unwrap();
            }
            2 => {
                values.shift().unwrap();
            }
            3 => {
                let length = i32::try_from(values.len().unwrap()).unwrap();
                let index = usize::try_from(revision % length).unwrap();
                values.child(index).unwrap().set("score", revision).unwrap();
            }
            _ => {
                values
                    .splice(
                        1,
                        1,
                        [object(vec![
                            ("id", JsonValue::from(200 + revision)),
                            ("score", JsonValue::from(revision)),
                        ])],
                    )
                    .unwrap();
            }
        }
        let prepared = change.prepare().unwrap();
        batches.push(prepared.ops().to_vec());
        tracker.adopt(&prepared).unwrap();
    }
    assert_eq!(
        apply_immutable_batches(&initial, &batches).unwrap(),
        tracker.value()
    );
}

#[derive(Debug, thiserror::Error)]
#[error("revision stream failed")]
struct StreamFailed;

#[test]
fn does_not_expose_partial_application_when_validation_or_iteration_fails() {
    let base = j(r#"{"nested":{"value":1}}"#);
    let invalid_batches = [
        ops(r#"[["s",["nested","value"],2]]"#),
        vec![Op::Set(
            vec![key("constructor"), key("prototype"), key("polluted")],
            JsonValue::Bool(true),
        )],
    ];
    assert!(apply_immutable_batches(&base, &invalid_batches).is_err());
    assert_eq!(base["nested"]["value"], JsonValue::from(1));

    let throwing: Vec<Result<Vec<Op>, StreamFailed>> = vec![
        Ok(ops(r#"[["s",["nested","value"],3]]"#)),
        Err(StreamFailed),
    ];
    let error = try_apply_immutable_batches(&base, throwing).unwrap_err();
    assert_eq!(error.to_string(), "revision stream failed");
    assert_eq!(base["nested"]["value"], JsonValue::from(1));

    let mut advanced_past_invalid = false;
    let batches = [
        ops(r#"[["s",["nested","value"],4]]"#),
        vec![Op::Set(
            vec![key("__proto__"), key("polluted")],
            JsonValue::Bool(true),
        )],
    ];
    let source = batches.iter().chain(std::iter::from_fn(|| {
        advanced_past_invalid = true;
        None
    }));
    let error = apply_immutable_batches(&base, source).unwrap_err();
    assert!(matches!(error, DeltaError::UnsafePath(_)));
    assert!(!advanced_past_invalid);
    assert_eq!(base["nested"]["value"], JsonValue::from(1));

    let malformed = Op::from_json(&j(r#"["s","bad-path",1]"#)).unwrap_err();
    assert!(malformed.to_string().contains("path"));

    assert!(matches!(
        apply_immutable(
            &j(r#"{"values":[]}"#),
            &ops(r#"[["s",["values","missing","value"],1]]"#)
        ),
        Err(DeltaError::Path(_))
    ));
    assert!(matches!(
        apply_immutable(
            &j(r#"{"values":[{}]}"#),
            &ops(r#"[["s",["values","0","value"],1]]"#)
        ),
        Err(DeltaError::UnsafePath(_))
    ));
}

#[test]
fn allows_one_immutable_batch_to_fan_out_without_mutating_shared_payloads() {
    let payload = j(r#"{"nested":{"value":1}}"#);
    let operations = vec![
        Op::Set(vec![key("placed")], payload.clone()),
        Op::Set(
            vec![key("placed"), key("nested"), key("value")],
            JsonValue::from(2),
        ),
    ];
    let base = j(r#"{"placed":null}"#);
    let first = apply_immutable(&base, &operations).unwrap();
    let second = apply_immutable(&base, &operations).unwrap();
    assert_eq!(first, second);
    assert!(!first.strict_equals(&second));
    assert!(!first["placed"].strict_equals(&second["placed"]));
    assert_eq!(payload["nested"]["value"], JsonValue::from(1));
}

#[test]
fn copies_a_wide_object_once_rather_than_once_per_repeated_write() {
    let base: JsonValue = (0..20_000)
        .map(|index| (format!("field{index}"), JsonValue::from(index)))
        .collect::<JsonObject>()
        .into();
    let operations: Vec<Op> = (0..1_000)
        .map(|index| {
            Op::Set(
                vec![Seg::from(format!("field{index}"))],
                JsonValue::from(-index),
            )
        })
        .collect();
    let result = apply_immutable(&base, &operations).unwrap();
    assert_eq!(result["field999"], JsonValue::from(-999));
    assert_eq!(base["field999"], JsonValue::from(999));
}
