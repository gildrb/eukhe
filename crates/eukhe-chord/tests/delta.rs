//! Port of `test/delta.test.ts`.
//!
//! JS-only cases mapped: `Object.isFrozen` checks have no Rust counterpart
//! (values are immutable by type); prototype-setter and `Object.prototype`
//! pollution checks become "the key is an own key of the result"; `apply`
//! of a mutable replacement payload that aliases two replicas cannot be
//! expressed (no shared mutation), so it checks the payload is adopted
//! without copying.

mod common;

use common::{j, ops, ops_text, wire};
use eukhe_chord::delta::{
    apply, apply_immutable, assert_valid_op, assert_valid_wire_op, decoder, encoder, is_base,
    overlap, track, DeltaError, Op, Seg, TrackerError, WireOp, WirePath,
};
use eukhe_chord::json::JsonValue;

fn key(name: &str) -> Seg {
    Seg::from(name)
}

#[test]
fn keeps_a_draft_alive_across_await_and_adopts_only_a_prepared_change() {
    let input = j(r#"{"count":1,"nested":{"text":"a"},"values":[1]}"#);
    let tracker = track(input.clone()).unwrap();
    assert!(tracker.value().strict_equals(&input));

    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.set("count", 2).unwrap();
    let nested = state.child("nested").unwrap();
    let text = nested.get("text").unwrap().unwrap().to_value().unwrap();
    nested
        .set("text", format!("{}b", text.as_str().unwrap()))
        .unwrap();
    state.child("values").unwrap().push([2]).unwrap();
    assert_eq!(tracker.value(), input);

    let prepared = change.prepare().unwrap();
    assert!(prepared.base().strict_equals(&tracker.value()));
    assert_eq!(
        prepared.value(),
        &j(r#"{"count":2,"nested":{"text":"ab"},"values":[1,2]}"#)
    );
    assert_eq!(
        prepared.ops(),
        ops(r#"[["s",["count"],2],["a",["nested","text"],"b"],["p",["values"],1,0,[2]]]"#)
    );
    assert_eq!(change.state().unwrap_err(), TrackerError::SettledOverlay);
    assert_eq!(tracker.value(), input);

    tracker.adopt(&prepared).unwrap();
    assert!(tracker.value().strict_equals(prepared.value()));
}

#[test]
fn aborts_and_revokes_without_changing_the_committed_value() {
    let tracker = track(j(r#"{"child":{"value":1}}"#)).unwrap();
    let change = tracker.begin_change();
    let child = change.state().unwrap().child("child").unwrap();
    child.set("value", 2).unwrap();
    change.abort();
    assert_eq!(tracker.value()["child"]["value"], JsonValue::from(1));
    assert_eq!(
        child.get("value").unwrap_err(),
        TrackerError::SettledOverlay
    );
    change.abort();
    assert_eq!(
        change.prepare().unwrap_err().to_string(),
        "Change has already been settled"
    );
    let next = tracker.begin_change();
    next.abort();
}

#[test]
fn grows_arrays_with_explicit_nulls_and_revokes_drafts_after_preparation() {
    let tracker = track(j(r#"{"values":[1,2]}"#)).unwrap();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .child("values")
        .unwrap()
        .set_len(4)
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value()["values"], j("[1,2,null,null]"));
    assert!(change.state().is_err());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn normalizes_a_deep_no_op_to_exact_previous_identity() {
    let tracker = track(j(r#"{"value":{"nested":[1,2]}}"#)).unwrap();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .set("value", j(r#"{"nested":[1,2]}"#))
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert!(prepared.value().strict_equals(prepared.base()));
    assert!(prepared.ops().is_empty());
    tracker.adopt(&prepared).unwrap();
    assert!(tracker.value().strict_equals(prepared.base()));
}

#[test]
fn takes_immutable_ownership_of_replacement_input_and_applies_no_op_normalization() {
    let tracker = track(j(r#"{"nested":{"value":1}}"#)).unwrap();
    let replacement = j(r#"{"nested":{"value":2}}"#);
    let prepared = tracker.prepare_replace(replacement.clone()).unwrap();
    assert!(prepared.value().strict_equals(&replacement));
    assert_eq!(prepared.ops(), [Op::Replace(replacement)]);
    tracker.adopt(&prepared).unwrap();

    let no_op = tracker
        .prepare_replace(j(r#"{"nested":{"value":2}}"#))
        .unwrap();
    assert!(no_op.value().strict_equals(&tracker.value()));
    assert!(no_op.ops().is_empty());
}

#[test]
fn shares_immutable_operation_placements_with_the_prepared_candidate() {
    let tracker = track(j(r#"{"rows":[]}"#)).unwrap();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .child("rows")
        .unwrap()
        .push([j(r#"{"id":1}"#)])
        .unwrap();
    let prepared = change.prepare().unwrap();
    let Op::Splice(_, _, _, items) = &prepared.ops()[0] else {
        panic!("expected splice");
    };
    assert!(items[0].strict_equals(&prepared.value()["rows"][0]));
}

#[test]
fn rejects_foreign_stale_and_repeated_preparations_while_allowing_competing_changes() {
    let first = track(j(r#"{"value":0}"#)).unwrap();
    let second = track(j(r#"{"value":0}"#)).unwrap();
    let change = first.begin_change();
    let competing = first.begin_change();
    change.state().unwrap().set("value", 1).unwrap();
    competing.state().unwrap().set("value", 2).unwrap();
    let prepared = change.prepare().unwrap();
    let competing_prepared = competing.prepare().unwrap();
    assert_eq!(
        second.adopt(&prepared).unwrap_err(),
        TrackerError::DifferentTracker
    );
    first.adopt(&prepared).unwrap();
    assert_eq!(
        first.adopt(&prepared).unwrap_err(),
        TrackerError::AlreadyUsed
    );
    assert_eq!(
        first.adopt(&competing_prepared).unwrap_err(),
        TrackerError::Stale
    );

    let stale = first.prepare_replace(j(r#"{"value":2}"#)).unwrap();
    let winner = first.prepare_replace(j(r#"{"value":3}"#)).unwrap();
    first.adopt(&winner).unwrap();
    assert_eq!(
        first.adopt(&stale).unwrap_err().to_string(),
        "Prepared change is stale"
    );
    assert_eq!(
        first.adopt(&stale).unwrap_err().to_string(),
        "Prepared change is stale"
    );
}

#[test]
fn invalidates_a_prepared_result_when_its_change_is_aborted() {
    let tracker = track(j(r#"{"value":0}"#)).unwrap();
    let change = tracker.begin_change();
    change.state().unwrap().set("value", 1).unwrap();
    let prepared = change.prepare().unwrap();
    change.abort();
    assert_eq!(
        tracker.adopt(&prepared).unwrap_err().to_string(),
        "Prepared change has been aborted"
    );
    change.abort();
}

#[test]
fn makes_competing_same_base_preparations_stale_after_adopting_a_no_op() {
    let tracker = track(j(r#"{"value":{"count":1}}"#)).unwrap();
    let first = tracker
        .prepare_replace(j(r#"{"value":{"count":1}}"#))
        .unwrap();
    let competing = tracker
        .prepare_replace(j(r#"{"value":{"count":1}}"#))
        .unwrap();
    assert!(first.value().strict_equals(first.base()));
    assert!(competing.value().strict_equals(competing.base()));
    tracker.adopt(&first).unwrap();
    assert_eq!(
        tracker.adopt(&first).unwrap_err(),
        TrackerError::AlreadyUsed
    );
    assert_eq!(tracker.adopt(&competing).unwrap_err(), TrackerError::Stale);
}

#[test]
fn emits_an_owned_root_replacement_without_traversing_large_replacement_input() {
    let rows: Vec<JsonValue> = (0..10_000)
        .map(|value| {
            j(&format!(
                r#"{{"value":{value},"stable":{{"value":{value}}}}}"#
            ))
        })
        .collect();
    let tracker = track(JsonValue::from(eukhe_chord::json::JsonObject::from_iter([
        ("rows", JsonValue::from(rows)),
    ])))
    .unwrap();
    let mut replacement = tracker.value();
    let current_rows = tracker.value()["rows"].clone();
    let stable = current_rows[5_000]["stable"].clone();
    let rows = replacement
        .as_object_mut()
        .unwrap()
        .get_mut("rows")
        .unwrap()
        .as_array_mut()
        .unwrap();
    rows[5_000] = JsonValue::from(eukhe_chord::json::JsonObject::from_iter([
        ("value", JsonValue::from(-1)),
        ("stable", stable),
    ]));
    let prepared = tracker.prepare_replace(replacement.clone()).unwrap();
    assert!(prepared.value().strict_equals(&replacement));
    assert_eq!(prepared.ops(), [Op::Replace(replacement)]);
    assert_eq!(
        &apply_immutable(prepared.base(), prepared.ops()).unwrap(),
        prepared.value()
    );
}

#[test]
fn emits_append_and_rolling_window_operations() {
    let tracker = track(j(r#"{"text":"abcdefgh"}"#)).unwrap();
    let change = tracker.begin_change();
    change.state().unwrap().set("text", "abcdefghij").unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.ops(), ops(r#"[["a",["text"],"ij"]]"#));
    tracker.adopt(&prepared).unwrap();

    let change = tracker.begin_change();
    change.state().unwrap().set("text", "defghijxyz").unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.ops(),
        ops(r#"[["t",["text"],3],["a",["text"],"xyz"]]"#)
    );
}

#[test]
fn finds_bounded_overlaps() {
    assert_eq!(overlap("abcdefgh", "defghxyz", 65_536), 5);
    assert_eq!(overlap("abcdef", "defghi", 0), 0);
}

#[test]
fn applies_mutable_and_immutable_operations() {
    let operations =
        ops(r#"[["a",["text"],"b"],["p",["values"],1,1,[3,4]],["s",["nested","value"],2]]"#);
    let base = j(r#"{"text":"a","values":[1,2],"nested":{"value":1},"stable":{"value":9}}"#);
    let immutable = apply_immutable(&base, &operations).unwrap();
    assert_eq!(
        immutable,
        j(r#"{"text":"ab","values":[1,3,4],"nested":{"value":2},"stable":{"value":9}}"#)
    );
    assert_eq!(
        base,
        j(r#"{"text":"a","values":[1,2],"nested":{"value":1},"stable":{"value":9}}"#)
    );
    assert!(immutable["stable"].strict_equals(&base["stable"]));
    assert_eq!(apply(common::clone(&base), &operations).unwrap(), immutable);
}

#[test]
fn supports_root_replacement_root_splice_and_permutations() {
    let base = ops(r#"[["r",[1,2,3]]]"#);
    assert!(is_base(&base));
    let mut value = apply(JsonValue::Null, &base).unwrap();
    value = apply(value, &ops(r#"[["p",[],1,1,[4]]]"#)).unwrap();
    value = apply(value, &ops(r#"[["m",[],[2,0,1]]]"#)).unwrap();
    assert_eq!(value, j("[3,1,4]"));
}

#[test]
fn rejects_unsafe_and_malformed_paths() {
    assert!(matches!(
        apply(
            j("{}"),
            &[Op::Set(
                vec![key("constructor"), key("prototype"), key("x")],
                JsonValue::Bool(true)
            )]
        ),
        Err(DeltaError::UnsafePath(_))
    ));
    assert!(matches!(
        apply(j(r#"{"values":[1]}"#), &ops(r#"[["s",["values",3],2]]"#)),
        Err(DeltaError::UnsafePath(_))
    ));
    assert!(apply(j(r#"{"value":1}"#), &ops(r#"[["a",["value"],"x"]]"#)).is_err());
    assert!(assert_valid_op(&j(r#"["s","value",1]"#)).is_err());
    assert_eq!(
        assert_valid_op(&j(r#"["m",[],[0,0]]"#))
            .unwrap_err()
            .to_string(),
        "m permutation is not a bijection"
    );
}

#[test]
fn validates_immutable_operations_before_traversing_the_target() {
    let error = Op::from_json(&j(r#"["s","bad-path",1]"#)).unwrap_err();
    assert_eq!(error.to_string(), "path is not an array");
}

#[test]
fn validates_decoded_and_wire_vocabularies_separately() {
    assert!(assert_valid_op(&j(r#"["s",["value"],1]"#)).is_ok());
    assert!(assert_valid_op(&j(r#"["s",1]"#)).is_err());
    assert!(assert_valid_wire_op(&j(r#"["s",1]"#)).is_ok());
    assert!(assert_valid_wire_op(&j(r##"["#",0,["value"]]"##)).is_ok());
}

#[test]
fn interns_paths_omits_adjacent_paths_and_round_trips() {
    let mut enc = encoder();
    let mut dec = decoder();
    let first = ops(r#"[["t",["nested","text"],1],["a",["nested","text"],"x"]]"#);
    assert_eq!(dec.decode(&enc.encode(&first)).unwrap(), first);
    let second = ops(r#"[["a",["nested","text"],"y"]]"#);
    let encoded = enc.encode(&second);
    assert_eq!(
        encoded,
        wire(r##"[["#",0,["nested","text"]],["a",0,"y"]]"##)
    );
    assert_eq!(dec.decode(&encoded).unwrap(), second);
}

#[test]
fn resets_path_dictionaries_on_a_base() {
    let mut enc = encoder();
    enc.encode(&ops(r#"[["s",["value"],1]]"#));
    enc.encode(&ops(r#"[["s",["value"],2]]"#));
    assert_eq!(
        enc.encode(&ops(r#"[["r",{"value":3}]]"#)),
        wire(r#"[["r",{"value":3}]]"#)
    );
    assert_eq!(
        enc.encode(&ops(r#"[["s",["value"],4]]"#)),
        wire(r#"[["s",["value"],4]]"#)
    );
}

#[test]
fn rejects_unresolved_short_forms_and_unsafe_interned_paths() {
    assert!(decoder().decode(&wire(r#"[["a","x"]]"#)).is_err());
    let unsafe_wire = [
        WireOp::Define(0, vec![key("__proto__")]),
        WireOp::Set(WirePath::Id(0), JsonValue::Bool(true)),
    ];
    assert!(matches!(
        decoder().decode(&unsafe_wire),
        Err(DeltaError::UnsafePath(_))
    ));
    assert!(matches!(
        WireOp::from_json(&j(r##"["#",0,["__proto__"]]"##)),
        Err(DeltaError::UnsafePath(_))
    ));
}

#[test]
fn omits_an_adjacent_repeated_path() {
    let mut enc = encoder();
    assert_eq!(
        enc.encode(&ops(r#"[["s",["value"],1],["s",["value"],2]]"#)),
        wire(r#"[["s",["value"],1],["s",2]]"#)
    );
}

#[test]
fn interns_on_second_use_rather_than_first() {
    let mut enc = encoder();
    assert_eq!(
        enc.encode(&ops(r#"[["a",["a","deep"],"1"]]"#)),
        wire(r#"[["a",["a","deep"],"1"]]"#)
    );
    assert_eq!(
        enc.encode(&ops(r#"[["a",["a","deep"],"2"]]"#)),
        wire(r##"[["#",0,["a","deep"]],["a",0,"2"]]"##)
    );
}

#[test]
fn does_not_collide_paths_containing_null_characters() {
    let operations = ops(r#"[["s",["a\u0000b"],1],["s",["a","b"],2]]"#);
    assert_eq!(
        decoder().decode(&encoder().encode(&operations)).unwrap(),
        operations
    );
}

#[test]
fn clears_decoder_ids_on_a_base_batch() {
    let mut dec = decoder();
    dec.decode(&wire(r##"[["#",0,["a"]],["a",0,"1"]]"##))
        .unwrap();
    dec.decode(&wire(r#"[["r",{"a":""}]]"#)).unwrap();
    assert!(dec.decode(&wire(r#"[["a",0,"2"]]"#)).is_err());
}

#[test]
fn makes_batches_after_a_base_self_contained() {
    let mut enc = encoder();
    enc.encode(&ops(r#"[["a",["a","deep"],"1"]]"#));
    enc.encode(&ops(r#"[["a",["a","deep"],"2"]]"#));
    let base = enc.encode(&ops(r#"[["r",{"a":{"deep":"x"}}]]"#));
    let after = enc.encode(&ops(r#"[["a",["a","deep"],"3"]]"#));
    assert_eq!(after, wire(r#"[["a",["a","deep"],"3"]]"#));
    let mut dec = decoder();
    assert_eq!(
        dec.decode(&base).unwrap(),
        ops(r#"[["r",{"a":{"deep":"x"}}]]"#)
    );
    assert_eq!(
        dec.decode(&after).unwrap(),
        ops(r#"[["a",["a","deep"],"3"]]"#)
    );
}

#[test]
fn round_trips_deterministic_mixed_operation_streams() {
    let batches: Vec<Vec<Op>> = (0..100)
        .map(|index| {
            ops(&format!(
                r#"[["s",["rows",{index},"value"],{index}],["a",["output"],"{index}"],["p",["tail"],{index},0,[{index}]]]"#
            ))
        })
        .collect();
    let mut enc = encoder();
    let mut dec = decoder();
    let decoded: Vec<Vec<Op>> = batches
        .iter()
        .map(|batch| dec.decode(&enc.encode(batch)).unwrap())
        .collect();
    assert_eq!(decoded, batches);
}

#[test]
fn does_not_mutate_a_replacement_payload_targeted_by_a_later_operation() {
    let replacement = j(r#"{"nested":{"value":1}}"#);
    let next = apply_immutable(
        &JsonValue::Null,
        &[
            Op::Replace(replacement.clone()),
            Op::Set(vec![key("nested"), key("value")], JsonValue::from(2)),
        ],
    )
    .unwrap();
    assert_eq!(replacement["nested"]["value"], JsonValue::from(1));
    assert_eq!(next["nested"]["value"], JsonValue::from(2));
}

#[test]
fn adopts_a_replacement_payload_rather_than_copying_it() {
    let batch = ops(r#"[["r",{"value":0}]]"#);
    let Op::Replace(payload) = &batch[0] else {
        panic!("expected replace");
    };
    let first = apply(JsonValue::Null, &batch).unwrap();
    let second = apply(JsonValue::Null, &batch).unwrap();
    assert!(first.strict_equals(payload));
    assert!(second.strict_equals(payload));
}

#[test]
fn rejects_constructor_walks_and_forbidden_interned_paths() {
    let parsed: Result<Vec<Op>, _> =
        serde_json::from_str(r#"[["s",["constructor","prototype","gadget"],true]]"#);
    assert!(parsed.is_err());
    assert!(matches!(
        apply(
            j("{}"),
            &[Op::Set(
                vec![key("constructor"), key("prototype"), key("gadget")],
                JsonValue::Bool(true)
            )]
        ),
        Err(DeltaError::UnsafePath(_))
    ));
    let forbidden = [
        WireOp::Define(0, vec![key("__proto__"), key("w")]),
        WireOp::Set(WirePath::Id(0), JsonValue::Bool(true)),
    ];
    assert!(decoder().decode(&forbidden).is_err());
}

#[test]
fn defines_own_keys_without_prototype_setters() {
    assert_eq!(
        apply(j("{}"), &ops(r#"[["s",["trap"],1]]"#)).unwrap(),
        j(r#"{"trap":1}"#)
    );
}

#[test]
fn allows_reserved_names_inside_values_without_prototype_pollution() {
    let value = j(r#"{"__proto__":{"z":1}}"#);
    let out = apply(j("{}"), &[Op::Set(vec![key("value")], value)]).unwrap();
    assert!(out["value"].as_object().unwrap().contains_key("__proto__"));
}

#[test]
fn imports_own_properties_in_o1() {
    let root = j(r#"{"trap":1}"#);
    let tracker = track(root.clone()).unwrap();
    assert!(tracker.value().strict_equals(&root));
    assert_eq!(
        track(j(r#"{"values":[1,2]}"#)).unwrap().value(),
        j(r#"{"values":[1,2]}"#)
    );
}

#[test]
fn writes_an_existing_index_and_appends_exactly_one_past_the_end() {
    assert_eq!(
        apply(
            j(r#"{"values":[1,2,3]}"#),
            &ops(r#"[["s",["values",1],9]]"#)
        )
        .unwrap(),
        j(r#"{"values":[1,9,3]}"#)
    );
    assert_eq!(
        apply(
            j(r#"{"values":[1,2,3]}"#),
            &ops(r#"[["s",["values",3],9]]"#)
        )
        .unwrap(),
        j(r#"{"values":[1,2,3,9]}"#)
    );
}

#[test]
fn rejects_gaps_huge_indices_and_string_spelled_indices() {
    assert!(apply(
        j(r#"{"values":[1,2,3]}"#),
        &ops(r#"[["s",["values",5],9]]"#)
    )
    .is_err());
    assert!(apply(
        j(r#"{"values":[]}"#),
        &ops(r#"[["s",["values",4294967290],1]]"#)
    )
    .is_err());
    assert!(apply(j(r#"{"values":[1]}"#), &ops(r#"[["s",["values","0"],9]]"#)).is_err());
    assert!(apply(
        j(r#"{"values":["a"]}"#),
        &ops(r#"[["a",["values","0"],"b"]]"#)
    )
    .is_err());
}

#[test]
fn allows_explicit_growth_values_and_rejects_deletion_past_the_end() {
    assert_eq!(
        apply(
            j(r#"{"values":[1]}"#),
            &ops(r#"[["p",["values"],1,0,[null,null,9]]]"#)
        )
        .unwrap(),
        j(r#"{"values":[1,null,null,9]}"#)
    );
    assert!(apply(j(r#"{"values":[1]}"#), &ops(r#"[["d",["values",1]]]"#)).is_err());
}

#[test]
fn applies_large_splice_payloads_without_spreading_them_at_once() {
    let items = vec![JsonValue::Null; 300_000];
    let result = apply(
        j(r#"{"values":[]}"#),
        &[Op::Splice(vec![key("values")], 0, 0, items)],
    )
    .unwrap();
    assert_eq!(result["values"].as_array().unwrap().len(), 300_000);
}

#[test]
fn rejects_unknown_verbs_malformed_tuples_paths_and_splice_payloads() {
    for invalid in [
        r#"["ZZZ",["value"],9]"#,
        r#"["p",["values"],0,0,"not-an-array"]"#,
        r#"["s","value",9]"#,
        r#"{"op":"s"}"#,
        "null",
    ] {
        assert!(Op::from_json(&j(invalid)).is_err(), "{invalid}");
    }
    assert_eq!(
        Op::from_json(&j(r#"["ZZZ",["value"],9]"#))
            .unwrap_err()
            .to_string(),
        "unknown op verb: ZZZ"
    );
}

#[test]
fn rejects_invalid_append_and_truncation_operations() {
    assert!(apply(j(r#"{"value":1}"#), &ops(r#"[["a",["missing"],"x"]]"#)).is_err());
    assert!(apply(j(r#"{"value":1}"#), &ops(r#"[["a",["value"],"x"]]"#)).is_err());
    assert_eq!(
        Op::from_json(&j(r#"["t",["value"],-1]"#))
            .unwrap_err()
            .to_string(),
        "t shape"
    );
    assert_eq!(
        WireOp::from_json(&j(r#"["t",["value"],-1]"#))
            .unwrap_err()
            .to_string(),
        "t count"
    );
}

#[test]
fn clamps_splice_removal_past_the_end() {
    assert_eq!(
        apply(
            j(r#"{"values":[1,2]}"#),
            &ops(r#"[["p",["values"],0,1e9,[]]]"#)
        )
        .unwrap(),
        j(r#"{"values":[]}"#)
    );
}

#[test]
fn accepts_decoded_operations_and_rejects_wire_only_forms() {
    for operation in [
        r#"["r",{"value":1}]"#,
        r#"["s",["value"],1]"#,
        r#"["d",["value"]]"#,
        r#"["a",["value"],"x"]"#,
        r#"["t",["value"],2]"#,
        r#"["p",["value"],0,0,[]]"#,
        r#"["m",["value"],[0]]"#,
    ] {
        assert!(assert_valid_op(&j(operation)).is_ok(), "{operation}");
    }
    for wire_only in [
        r#"["s",1]"#,
        r#"["d"]"#,
        r#"["a","x"]"#,
        r#"["t",2]"#,
        r#"["p",0,0,[]]"#,
        r##"["#",0,["value"]]"##,
        r#"["s",0,1]"#,
    ] {
        assert!(assert_valid_op(&j(wire_only)).is_err(), "{wire_only}");
        assert!(assert_valid_wire_op(&j(wire_only)).is_ok(), "{wire_only}");
    }
}

#[test]
fn does_not_recursively_inspect_operation_payloads() {
    assert!(assert_valid_op(&j(r#"["s",["value"],{"nested":[{"deep":null}]}]"#)).is_ok());
    assert!(assert_valid_wire_op(&j(r#"["r",{"any":"payload"}]"#)).is_ok());
    assert_eq!(ops_text(&ops(r#"[["r",{"a":-0}]]"#)), r#"[["r",{"a":0}]]"#);
}
