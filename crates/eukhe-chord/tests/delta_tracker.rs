//! Port of `test/delta-tracker/tracker.test.ts`.
//!
//! JS-only mechanisms and their Rust mapping:
//! - `isProxy(prepared.value)`: values are plain `JsonValue`s by type.
//! - Promise `then` probing of settled drafts: kept as "a `then` key reads like
//!   any key, and settled drafts reject reads".
//! - Property descriptors, prototypes, inherited setters, and
//!   `Object.prototype` pollution: not representable; the checks become own
//!   keys and key order.
//! - Argument coercion callbacks (`valueOf`) and borrowed mutators applied to
//!   ordinary arrays: Rust arguments are plain integers and mutators are
//!   methods, so these become direct-argument checks against native results.
//! - Non-strict placements (`undefined`, functions, symbols, bigint, NaN,
//!   cycles, accessors, sparse arrays, class instances): unrepresentable in
//!   `JsonValue`; the remaining assertions (deletion, valid placements) stay.

mod common;

use std::cmp::Ordering;

use common::{clone, expect_alias_free, j, ops, replay};
use eukhe_chord::delta::{decoder, encoder, track, Draft, DraftItem, Op, Tracker, TrackerError};
use eukhe_chord::json::{JsonObject, JsonValue};

fn read(draft: &Draft, key: impl Into<eukhe_chord::delta::Seg>) -> JsonValue {
    draft
        .get(key)
        .unwrap()
        .map(|item| item.to_value().unwrap())
        .unwrap_or_default()
}

fn number(draft: &Draft, key: impl Into<eukhe_chord::delta::Seg>) -> f64 {
    read(draft, key).as_f64().unwrap()
}

fn text(draft: &Draft, key: impl Into<eukhe_chord::delta::Seg>) -> String {
    read(draft, key).as_str().unwrap().to_owned()
}

fn int(value: f64) -> JsonValue {
    JsonValue::try_from(value).unwrap()
}

/// Change, prepare, check replay and base immutability, adopt.
fn settle(tracker: &Tracker, mutate: impl FnOnce(&Draft)) -> JsonValue {
    let base_root = tracker.value();
    let base = clone(&base_root);
    let change = tracker.begin_change();
    mutate(&change.state().unwrap());
    let prepared = change.prepare().unwrap();
    let candidate = clone(prepared.value());
    assert_eq!(replay(&base, prepared.ops()), candidate);
    assert_eq!(base_root, base);
    tracker.adopt(&prepared).unwrap();
    assert_eq!(base_root, base);
    assert!(tracker.value().strict_equals(prepared.value()));
    assert_eq!(tracker.value(), candidate);
    candidate
}

fn rows(count: usize, row: impl Fn(usize) -> String) -> JsonValue {
    JsonValue::from((0..count).map(|index| j(&row(index))).collect::<Vec<_>>())
}

fn with(key: &str, value: JsonValue) -> JsonValue {
    JsonValue::from(JsonObject::from_iter([(key, value)]))
}

// ─── Transactional overlay lifecycle ─────────────────────────────────────────

#[test]
fn materializes_an_immutable_next_revision_and_adopts_it_by_pointer_swap() {
    let initial = j(r#"{"count":1,"nested":{"text":"a"},"values":[1]}"#);
    let tracker = track(initial.clone()).unwrap();
    assert!(tracker.value().strict_equals(&initial));
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.set("count", 2).unwrap();
    let nested = state.child("nested").unwrap();
    nested
        .set("text", format!("{}b", text(&nested, "text")))
        .unwrap();
    state.child("values").unwrap().push([2]).unwrap();
    assert_eq!(
        initial,
        j(r#"{"count":1,"nested":{"text":"a"},"values":[1]}"#)
    );
    let prepared = change.prepare().unwrap();
    let next = prepared.value().clone();
    assert_eq!(prepared.base_revision(), 0);
    assert!(prepared.base().strict_equals(&initial));
    assert!(!next.strict_equals(&initial));
    assert_eq!(
        next,
        j(r#"{"count":2,"nested":{"text":"ab"},"values":[1,2]}"#)
    );
    assert_eq!(
        prepared.ops(),
        ops(r#"[["s",["count"],2],["a",["nested","text"],"b"],["p",["values"],1,0,[2]]]"#)
    );
    assert!(tracker.value().strict_equals(&initial));
    tracker.adopt(&prepared).unwrap();
    assert_eq!(
        initial,
        j(r#"{"count":1,"nested":{"text":"a"},"values":[1]}"#)
    );
    assert!(tracker.value().strict_equals(&next));
    assert!(prepared.value().strict_equals(&next));
    assert!(prepared.base().strict_equals(&initial));
    assert_eq!(
        state.get("count").unwrap_err(),
        TrackerError::SettledOverlay
    );
}

#[tokio::test]
async fn keeps_a_transaction_live_across_await_and_seals_it_only_at_prepare() {
    let tracker = track(j(r#"{"left":0,"nested":{"right":0}}"#)).unwrap();
    let change = tracker.begin_change();
    change.state().unwrap().set("left", 1).unwrap();
    tokio::task::yield_now().await;
    change
        .state()
        .unwrap()
        .child("nested")
        .unwrap()
        .set("right", 2)
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value(), &j(r#"{"left":1,"nested":{"right":2}}"#));
    assert_eq!(
        change.state().unwrap_err().to_string(),
        "Cannot use a settled overlay"
    );
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn lets_settled_drafts_be_inspected_without_reporting_a_false_failure() {
    let tracker = track(j(r#"{"then":"document-value","value":1}"#)).unwrap();
    let change = tracker.begin_change();
    let draft = change.state().unwrap();
    assert_eq!(text(&draft, "then"), "document-value");
    draft.set("value", 2).unwrap();
    let prepared = change.prepare().unwrap();
    assert!(!draft.is_array());
    assert_eq!(
        draft.get("value").unwrap_err().to_string(),
        "Cannot use a settled overlay"
    );
    tracker.adopt(&prepared).unwrap();
    assert_eq!(tracker.value()["then"], JsonValue::from("document-value"));
    assert_eq!(tracker.value()["value"], JsonValue::from(2));

    let large = track(with(
        "rows",
        rows(4_100, |value| format!(r#"{{"value":{value}}}"#)),
    ))
    .unwrap();
    let large_change = large.begin_change();
    let large_draft = large_change.state().unwrap();
    let draft_rows = large_draft.child("rows").unwrap();
    for index in 0..4_100 {
        assert!(number(&draft_rows.child(index).unwrap(), "value") >= 0.0);
    }
    draft_rows.child(0).unwrap().set("value", -1).unwrap();
    let large_prepared = large_change.prepare().unwrap();
    assert_eq!(
        large_draft.get("rows").unwrap_err().to_string(),
        "Cannot use a settled overlay"
    );
    large.adopt(&large_prepared).unwrap();
}

#[test]
fn aborts_idempotently_and_revokes_held_descendants() {
    let tracker = track(j(r#"{"child":{"value":1}}"#)).unwrap();
    let change = tracker.begin_change();
    let child = change.state().unwrap().child("child").unwrap();
    child.set("value", 2).unwrap();
    change.abort();
    change.abort();
    assert_eq!(tracker.value()["child"]["value"], JsonValue::from(1));
    assert_eq!(
        child.get("value").unwrap_err(),
        TrackerError::SettledOverlay
    );
    assert_eq!(
        change.prepare().unwrap_err().to_string(),
        "Change has already been settled"
    );
}

#[test]
fn allows_competing_contexts_and_invalidates_loser_views() {
    let tracker = track(j(r#"{"value":0}"#)).unwrap();
    let first = tracker.begin_change();
    let second = tracker.begin_change();
    first.state().unwrap().set("value", 1).unwrap();
    second.state().unwrap().set("value", 2).unwrap();
    let first_prepared = first.prepare().unwrap();
    let second_prepared = second.prepare().unwrap();
    let held = second_prepared.value().clone();
    tracker.adopt(&first_prepared).unwrap();
    assert_eq!(tracker.value()["value"], JsonValue::from(1));
    assert_eq!(held["value"], JsonValue::from(2));
    assert_eq!(
        tracker.adopt(&second_prepared).unwrap_err().to_string(),
        "Prepared change is stale"
    );
    assert_eq!(
        tracker.adopt(&first_prepared).unwrap_err().to_string(),
        "Prepared change has already been used"
    );
}

#[test]
fn invalidates_competing_open_overlays_without_changing_their_base_revision() {
    let initial = j(r#"{"rows":[{"value":0},{"value":1}]}"#);
    let tracker = track(initial.clone()).unwrap();
    let stale_change = tracker.begin_change();
    let held = stale_change
        .state()
        .unwrap()
        .child("rows")
        .unwrap()
        .child(1)
        .unwrap();
    held.set("value", 2).unwrap();

    let winner = tracker.begin_change();
    winner
        .state()
        .unwrap()
        .child("rows")
        .unwrap()
        .child(0)
        .unwrap()
        .set("value", 3)
        .unwrap();
    let prepared = winner.prepare().unwrap();
    tracker.adopt(&prepared).unwrap();

    assert_eq!(initial, j(r#"{"rows":[{"value":0},{"value":1}]}"#));
    assert_eq!(tracker.value(), j(r#"{"rows":[{"value":3},{"value":1}]}"#));
    assert_eq!(
        held.get("value").unwrap_err().to_string(),
        "Cannot use a settled overlay"
    );
    assert_eq!(
        stale_change.prepare().unwrap_err().to_string(),
        "Cannot use a settled overlay"
    );
    stale_change.abort();
}

#[test]
fn adopts_object_edits_as_ordinary_immutable_revisions() {
    let initial = j(r#"{"first":1,"second":2}"#);
    let tracker = track(initial.clone()).unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.set("first", 3).unwrap();
    state.delete("second").unwrap();
    state.set("third", 4).unwrap();
    let prepared = change.prepare().unwrap();
    tracker.adopt(&prepared).unwrap();
    assert!(!tracker.value().strict_equals(&initial));
    assert_eq!(initial, j(r#"{"first":1,"second":2}"#));
    assert_eq!(tracker.value(), j(r#"{"first":3,"third":4}"#));
    assert_eq!(
        tracker
            .value()
            .as_object()
            .unwrap()
            .keys()
            .collect::<Vec<_>>(),
        ["first", "third"]
    );
}

#[test]
fn supports_adopt_then_publish_ordering_and_retained_publication_reads() {
    let tracker = track(j(r#"{"value":0,"nested":{"count":0}}"#)).unwrap();
    let change = tracker.begin_change();
    change.state().unwrap().set("value", 1).unwrap();
    change
        .state()
        .unwrap()
        .child("nested")
        .unwrap()
        .set("count", 1)
        .unwrap();
    let prepared = change.prepare().unwrap();
    let operations = prepared.ops().to_vec();
    tracker.adopt(&prepared).unwrap();
    assert_eq!(prepared.ops(), operations);
    let published = (!prepared.ops().is_empty()).then(|| prepared.value().clone());
    assert_eq!(operations.len(), 2);
    let published = published.unwrap();
    assert!(published.strict_equals(&tracker.value()));
    assert_eq!(clone(&published), j(r#"{"value":1,"nested":{"count":1}}"#));

    let next = tracker.begin_change();
    next.state().unwrap().set("value", 2).unwrap();
    let next_prepared = next.prepare().unwrap();
    tracker.adopt(&next_prepared).unwrap();
    assert!(!published.strict_equals(&tracker.value()));
    assert_eq!(prepared.value(), &j(r#"{"value":1,"nested":{"count":1}}"#));
    assert_eq!(tracker.value(), j(r#"{"value":2,"nested":{"count":1}}"#));
}

#[test]
fn keeps_replacement_base_value_structurally_compatible_and_readable_after_adoption() {
    let original = j(r#"{"value":0}"#);
    let replacement = j(r#"{"value":1}"#);
    let tracker = track(original.clone()).unwrap();
    let prepared = tracker.prepare_replace(replacement.clone()).unwrap();
    assert!(prepared.base().strict_equals(&original));
    assert!(prepared.value().strict_equals(&replacement));
    tracker.adopt(&prepared).unwrap();
    assert!(prepared.base().strict_equals(&original));
    assert!(prepared.value().strict_equals(&replacement));
    assert!(prepared.value().strict_equals(&tracker.value()));
}

#[test]
fn keeps_aborted_and_stale_materialized_candidates_readable() {
    let tracker = track(j(r#"{"value":0}"#)).unwrap();
    let aborted_change = tracker.begin_change();
    aborted_change.state().unwrap().set("value", 1).unwrap();
    let aborted = aborted_change.prepare().unwrap();
    let aborted_view = aborted.value().clone();
    aborted.abort();
    assert_eq!(aborted_view["value"], JsonValue::from(1));
    assert_eq!(aborted.value()["value"], JsonValue::from(1));

    let loser_change = tracker.begin_change();
    loser_change.state().unwrap().set("value", 2).unwrap();
    let loser = loser_change.prepare().unwrap();
    let loser_view = loser.value().clone();
    let winner = tracker.prepare_replace(j(r#"{"value":3}"#)).unwrap();
    tracker.adopt(&winner).unwrap();
    assert_eq!(loser_view["value"], JsonValue::from(2));
    assert_eq!(loser.value()["value"], JsonValue::from(2));
}

#[test]
fn lets_a_settled_change_abort_its_prepared_result_without_retaining_its_context() {
    let tracker = track(j(r#"{"value":0,"nested":{"value":1}}"#)).unwrap();
    let change = tracker.begin_change();
    change.state().unwrap().set("value", 1).unwrap();
    let prepared = change.prepare().unwrap();
    let operations = prepared.ops().to_vec();
    change.abort();
    change.abort();
    assert_eq!(prepared.ops(), operations);
    assert_eq!(prepared.value(), &j(r#"{"value":1,"nested":{"value":1}}"#));
    assert_eq!(
        tracker.adopt(&prepared).unwrap_err().to_string(),
        "Prepared change has been aborted"
    );
}

#[test]
fn rejects_foreign_and_aborted_prepared_values() {
    let first = track(j(r#"{"value":0}"#)).unwrap();
    let second = track(j(r#"{"value":0}"#)).unwrap();
    let prepared = first.prepare_replace(j(r#"{"value":1}"#)).unwrap();
    assert_eq!(
        second.adopt(&prepared).unwrap_err().to_string(),
        "Prepared change belongs to a different tracker"
    );
    prepared.abort();
    prepared.abort();
    assert_eq!(first.adopt(&prepared).unwrap_err(), TrackerError::Aborted);
}

#[test]
fn reads_deleted_own_properties_as_absent() {
    let tracker = track(j(r#"{"value":1}"#)).unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.delete("value").unwrap();
    state.set("trackerInherited", 1).unwrap();
    state.delete("trackerInherited").unwrap();
    assert!(state.get("value").unwrap().is_none());
    assert!(state.get("trackerInherited").unwrap().is_none());
    let prepared = change.prepare().unwrap();
    assert!(prepared.value().get("value").is_none());
    tracker.adopt(&prepared).unwrap();
    assert_eq!(tracker.value().as_object().unwrap().len(), 0);
}

#[test]
fn detaches_old_handles_for_deeply_equal_object_and_array_assignments_before_normalizing() {
    let initial =
        j(r#"{"object":{"nested":{"value":1}},"array":[{"value":1}],"rows":[{"value":1}]}"#);
    let tracker = track(initial.clone()).unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    let old_object = state.child("object").unwrap();
    let old_array = state.child("array").unwrap();
    let old_row = state.child("rows").unwrap().child(0).unwrap();
    state.set("object", j(r#"{"nested":{"value":1}}"#)).unwrap();
    state.set("array", j(r#"[{"value":1}]"#)).unwrap();
    state
        .child("rows")
        .unwrap()
        .set(0, j(r#"{"value":1}"#))
        .unwrap();
    assert_ne!(state.child("object").unwrap(), old_object);
    assert_ne!(state.child("array").unwrap(), old_array);
    assert_ne!(state.child("rows").unwrap().child(0).unwrap(), old_row);
    old_object.child("nested").unwrap().set("value", 9).unwrap();
    old_array.child(0).unwrap().set("value", 9).unwrap();
    old_row.set("value", 9).unwrap();
    assert_eq!(state.value().unwrap(), initial);
    let prepared = change.prepare().unwrap();
    assert!(prepared.ops().is_empty());
    tracker.adopt(&prepared).unwrap();
    let value = tracker.value();
    assert!(value.strict_equals(&initial));
    assert!(value["object"].strict_equals(&initial["object"]));
    assert!(value["array"].strict_equals(&initial["array"]));
    assert!(value["rows"][0].strict_equals(&initial["rows"][0]));
}

#[test]
fn normalizes_a_deeply_equal_replacement_without_changing_committed_identity() {
    let initial = j(r#"{"nested":{"value":1},"rows":[1,2,3]}"#);
    let tracker = track(initial.clone()).unwrap();
    let prepared = tracker
        .prepare_replace(j(r#"{"nested":{"value":1},"rows":[1,2,3]}"#))
        .unwrap();
    assert!(prepared.ops().is_empty());
    tracker.adopt(&prepared).unwrap();
    assert!(tracker.value().strict_equals(&initial));
}

#[test]
fn takes_o1_immutable_ownership_for_replacement_and_its_operation_payload() {
    let tracker = track(j(r#"{"value":0,"rows":[]}"#)).unwrap();
    let replacement = j(r#"{"value":1,"rows":[{"value":2}]}"#);
    let prepared = tracker.prepare_replace(replacement.clone()).unwrap();
    assert!(prepared.base().strict_equals(&tracker.value()));
    assert!(prepared.value().strict_equals(&replacement));
    assert_eq!(prepared.ops(), [Op::Replace(replacement.clone())]);
    let Op::Replace(payload) = &prepared.ops()[0] else {
        panic!("expected replacement");
    };
    assert!(payload.strict_equals(&replacement));
    tracker.adopt(&prepared).unwrap();
    assert!(tracker.value().strict_equals(&replacement));
}

#[test]
fn rejects_non_container_roots() {
    assert_eq!(
        track(JsonValue::from(1)).unwrap_err(),
        TrackerError::RootNotContainer
    );
    let tracker = track(j("{}")).unwrap();
    assert_eq!(
        tracker.prepare_replace(JsonValue::Null).unwrap_err(),
        TrackerError::RootNotContainer
    );
}

// ─── Policy view ─────────────────────────────────────────────────────────────

#[test]
fn supports_native_reads_keys_iteration_and_json() {
    let tracker = track(j(r#"{"values":[1,2,3],"object":{"a":1}}"#)).unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    let values = state.child("values").unwrap();
    values.splice(1, 1, [4, 5]).unwrap();
    state.child("object").unwrap().set("b", 2).unwrap();
    assert!(values.is_array());
    assert_eq!(values.len().unwrap(), 4);
    assert_eq!(values.value().unwrap(), j("[1,4,5,3]"));
    let doubled: Vec<f64> = (0..4).map(|index| number(&values, index) * 2.0).collect();
    assert_eq!(doubled, [2.0, 8.0, 10.0, 6.0]);
    assert_eq!(values.keys().unwrap(), ["0", "1", "2", "3"]);
    assert_eq!(read(&values, "2"), JsonValue::from(5));
    assert_eq!(state.child("object").unwrap().keys().unwrap(), ["a", "b"]);
    assert_eq!(
        state.value().unwrap(),
        j(r#"{"values":[1,4,5,3],"object":{"a":1,"b":2}}"#)
    );
    change.abort();
}

#[test]
fn keeps_document_keys_distinct_from_object_proxy_target_fields() {
    let tracker = track(j(
        r#"{"object":{"context":1,"base":2,"parent":3,"dirty":4,"target":5,"proxy":6}}"#,
    ))
    .unwrap();
    let change = tracker.begin_change();
    let object = change.state().unwrap().child("object").unwrap();
    object.set("context", 7).unwrap();
    object.set("proxy", 8).unwrap();
    assert_eq!(
        object.keys().unwrap(),
        ["context", "base", "parent", "dirty", "target", "proxy"]
    );
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value()["object"],
        j(r#"{"context":7,"base":2,"parent":3,"dirty":4,"target":5,"proxy":8}"#)
    );
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn keeps_string_operation_forms() {
    let tracker = track(j(r#"{"text":"abcdefgh","values":[1,2,3],"marker":0}"#)).unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    let current = text(&state, "text");
    state.set("text", format!("{}xyz", &current[3..])).unwrap();
    // The TS case sets `marker` from a `valueOf` coercion callback.
    state.set("marker", 1).unwrap();
    state.child("values").unwrap().splice(1, 1, [4]).unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value(),
        &j(r#"{"text":"defghxyz","values":[1,4,3],"marker":1}"#)
    );
    assert!(prepared.ops().contains(&ops(r#"[["t",["text"],3]]"#)[0]));
    assert!(prepared
        .ops()
        .contains(&ops(r#"[["a",["text"],"xyz"]]"#)[0]));
    let decoded = decoder().decode(&encoder().encode(prepared.ops())).unwrap();
    assert_eq!(&replay(&tracker.value(), &decoded), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn emits_deletion_and_supports_root_arrays() {
    let object_tracker = track(j(r#"{"keep":1,"remove":2}"#)).unwrap();
    settle(&object_tracker, |draft| draft.delete("remove").unwrap());
    assert_eq!(object_tracker.value(), j(r#"{"keep":1}"#));

    let array_tracker = track(j("[1,2,3]")).unwrap();
    settle(&array_tracker, |draft| {
        draft.reverse().unwrap();
        draft.push([4]).unwrap();
    });
    assert_eq!(array_tracker.value(), j("[3,2,1,4]"));
}

#[test]
fn preserves_native_object_key_order_after_delete_and_readd() {
    let tracker = track(j(r#"{"first":1,"second":2}"#)).unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.delete("first").unwrap();
    state.set("first", 1).unwrap();
    assert_eq!(state.keys().unwrap(), ["second", "first"]);
    let prepared = change.prepare().unwrap();
    tracker.adopt(&prepared).unwrap();
    assert_eq!(
        tracker
            .value()
            .as_object()
            .unwrap()
            .keys()
            .collect::<Vec<_>>(),
        ["second", "first"]
    );
}

#[test]
fn orders_new_integer_like_object_keys_before_strings_for_recipe_visible_reads() {
    let tracker = track(j(r#"{"object":{"label":"x"},"first":""}"#)).unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    let object = state.child("object").unwrap();
    object.set("2", "two").unwrap();
    object.set("1", "one").unwrap();
    assert_eq!(object.keys().unwrap(), ["1", "2", "label"]);
    state
        .set("first", object.keys().unwrap()[0].clone())
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value()["first"], JsonValue::from("1"));
    assert_eq!(
        prepared.value()["object"]
            .as_object()
            .unwrap()
            .keys()
            .collect::<Vec<_>>(),
        ["1", "2", "label"]
    );
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    assert_eq!(
        replay(&base, prepared.ops()).to_string(),
        prepared.value().to_string()
    );
    tracker.adopt(&prepared).unwrap();
    assert_eq!(tracker.value()["first"], JsonValue::from("1"));
}

#[test]
fn orders_integer_like_keys_on_null_prototype_objects() {
    // Prototypes are not represented: a null-prototype object is a plain object.
    let tracker = track(j(r#"{"object":{"label":"x"}}"#)).unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let object = change.state().unwrap().child("object").unwrap();
    object.set("2", "two").unwrap();
    object.set("1", "one").unwrap();
    assert_eq!(object.keys().unwrap(), ["1", "2", "label"]);
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value()["object"]
            .as_object()
            .unwrap()
            .keys()
            .collect::<Vec<_>>(),
        ["1", "2", "label"]
    );
    assert_eq!(
        replay(&base, prepared.ops()).to_string(),
        prepared.value().to_string()
    );
    tracker.adopt(&prepared).unwrap();
    assert_eq!(
        tracker.value()["object"]
            .as_object()
            .unwrap()
            .keys()
            .collect::<Vec<_>>(),
        ["1", "2", "label"]
    );
}

#[test]
fn normalizes_deeply_equal_container_assignments_before_direct_candidate_materialization() {
    let initial = j(r#"{"child":{"a":1,"b":2},"count":0}"#);
    let tracker = track(initial.clone()).unwrap();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .set("child", j(r#"{"b":2,"a":1}"#))
        .unwrap();
    change.state().unwrap().set("count", 1).unwrap();
    let prepared = change.prepare().unwrap();
    let replayed = replay(&initial, prepared.ops());
    assert_eq!(prepared.ops(), ops(r#"[["s",["count"],1]]"#));
    assert_eq!(
        prepared.value()["child"]
            .as_object()
            .unwrap()
            .keys()
            .collect::<Vec<_>>(),
        ["a", "b"]
    );
    assert_eq!(
        replayed["child"]
            .as_object()
            .unwrap()
            .keys()
            .collect::<Vec<_>>(),
        ["a", "b"]
    );
    assert_eq!(prepared.value(), &replayed);
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn keeps_native_integer_and_string_ordering_across_deletion_and_readdition() {
    let tracker = track(j(
        r#"{"object":{"1":"one","2":"two","first":"a","second":"b"}}"#,
    ))
    .unwrap();
    let change = tracker.begin_change();
    let object = change.state().unwrap().child("object").unwrap();
    object.delete("2").unwrap();
    object.set("2", "two").unwrap();
    object.delete("first").unwrap();
    object.set("first", "a").unwrap();
    object.set("3", "three").unwrap();
    object.set("0", "zero").unwrap();
    let expected = ["0", "1", "2", "3", "second", "first"];
    assert_eq!(object.keys().unwrap(), expected);
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value()["object"]
            .as_object()
            .unwrap()
            .keys()
            .collect::<Vec<_>>(),
        expected
    );
    tracker.adopt(&prepared).unwrap();
    assert_eq!(
        tracker.value()["object"]
            .as_object()
            .unwrap()
            .keys()
            .collect::<Vec<_>>(),
        expected
    );
}

#[test]
fn matches_native_splice_fill_and_copy_within_semantics() {
    let compare = |native: &str, mutate: &dyn Fn(&Draft)| {
        let tracker = track(j(r#"{"values":[1,2,3]}"#)).unwrap();
        settle(&tracker, |draft| mutate(&draft.child("values").unwrap()));
        assert_eq!(tracker.value()["values"], j(native));
    };
    // Native results of `[1,2,3]` with these arguments.
    compare("[1,9,3]", &|values| {
        values.splice(1, 1, [9]).unwrap();
    });
    compare("[1,7,7]", &|values| {
        values.fill(7, 1, i64::MAX).unwrap();
    });
    compare("[1,1,2]", &|values| {
        values.copy_within(1, 0, 2).unwrap();
    });
    compare("[1,2,9]", &|values| {
        values.splice(-1, 1, [9]).unwrap();
    });
    compare("[7,2,3]", &|values| {
        values.fill(7, -3, -2).unwrap();
    });
    compare("[3,2,3]", &|values| {
        values.copy_within(-3, -1, i64::MAX).unwrap();
    });
}

#[test]
fn does_not_report_inherited_methods_as_own_array_properties() {
    let tracker = track(j(r#"{"values":[1]}"#)).unwrap();
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    assert!(!values.keys().unwrap().contains(&"map".to_owned()));
    assert!(values.get("map").unwrap().is_none());
    assert!(values.has("map").unwrap());
    change.abort();
}

#[test]
fn keeps_repeated_identical_writes_instead_of_reverting_their_pending_override() {
    let tracker = track(j(r#"{"value":0,"values":[0]}"#)).unwrap();
    settle(&tracker, |draft| {
        draft.set("value", 1).unwrap();
        draft.set("value", 1).unwrap();
        let values = draft.child("values").unwrap();
        values.set(0, JsonValue::Null).unwrap();
        values.set(0, JsonValue::Null).unwrap();
        values.push([2]).unwrap();
        values.set(1, JsonValue::Null).unwrap();
        values.set(1, JsonValue::Null).unwrap();
    });
    assert_eq!(tracker.value(), j(r#"{"value":1,"values":[null,null]}"#));
}

#[test]
fn rejects_array_index_gaps_without_mutation_while_allowing_replacement_and_append() {
    let tracker = track(j(r#"{"values":[1,2]}"#)).unwrap();
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    assert_eq!(
        values.set(3, 4).unwrap_err().to_string(),
        "Overlay arrays cannot contain holes"
    );
    assert_eq!(values.value().unwrap(), j("[1,2]"));
    assert_eq!(tracker.value()["values"], j("[1,2]"));
    values.set(1, 9).unwrap();
    values.set(2, 3).unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value()["values"], j("[1,9,3]"));
    assert_eq!(&replay(&tracker.value(), prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
    assert_eq!(tracker.value()["values"], j("[1,9,3]"));
}

#[test]
fn supports_optional_deletion_explicit_null_length_growth_shrinking_and_default_sort() {
    let tracker = track(j(r#"{"optional":"remove","values":[3,1,2]}"#)).unwrap();
    settle(&tracker, |draft| {
        draft.delete("optional").unwrap();
        let values = draft.child("values").unwrap();
        values.set_len(5).unwrap();
        assert_eq!(values.value().unwrap(), j("[3,1,2,null,null]"));
        values.set_len(4).unwrap();
        values.sort().unwrap();
        assert_eq!(values.delete(0).unwrap_err(), TrackerError::ArrayHoles);
    });
    assert_eq!(tracker.value(), j(r#"{"values":[1,2,3,null]}"#));
}

#[test]
fn enumerates_wide_objects_without_duplicate_keys() {
    let tracker = track(j(r#"{"values":{}}"#)).unwrap();
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    for index in 0..20_000 {
        values.set(format!("field{index}"), index).unwrap();
    }
    let keys = values.keys().unwrap();
    assert_eq!(keys.len(), 20_000);
    assert_eq!(keys[0], "field0");
    assert_eq!(keys[keys.len() - 1], "field19999");
    change.abort();
}

#[test]
fn does_not_dirty_read_only_traversals() {
    let tracker = track(j(r#"{"nested":{"rows":[{"value":1}]}}"#)).unwrap();
    let change = tracker.begin_change();
    let row = change
        .state()
        .unwrap()
        .child("nested")
        .unwrap()
        .child("rows")
        .unwrap()
        .child(0)
        .unwrap();
    assert_eq!(read(&row, "value"), JsonValue::from(1));
    let prepared = change.prepare().unwrap();
    assert!(prepared.ops().is_empty());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn uses_one_proxy_identity_per_accessed_container() {
    let tracker = track(j(r#"{"nested":{"value":1},"rows":[{"value":2}]}"#)).unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    assert_eq!(
        state.child("nested").unwrap(),
        state.child("nested").unwrap()
    );
    assert_eq!(state.child("rows").unwrap(), state.child("rows").unwrap());
    assert_eq!(
        state.child("rows").unwrap().child(0).unwrap(),
        state.child("rows").unwrap().child(0).unwrap()
    );
    change.abort();
}

// ─── By-value placements ─────────────────────────────────────────────────────

#[test]
fn clones_property_index_push_unshift_splice_fill_and_copy_within_placements() {
    let tracker = track(j(
        r#"{"property":null,"values":[{"value":0},{"value":1},{"value":2}]}"#,
    ))
    .unwrap();
    let mut external = j(r#"{"value":5}"#);
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    let values = state.child("values").unwrap();
    state.set("property", external.clone()).unwrap();
    values.set(0, external.clone()).unwrap();
    values.push([external.clone()]).unwrap();
    values.unshift([external.clone()]).unwrap();
    values.splice(2, 0, [external.clone()]).unwrap();
    external
        .as_object_mut()
        .unwrap()
        .insert("value", JsonValue::from(99));
    values.fill(values.child(0).unwrap(), 1, 3).unwrap();
    values.copy_within(3, 0, 2).unwrap();
    let prepared = change.prepare().unwrap();
    let candidate = clone(prepared.value());
    assert_eq!(candidate["property"], j(r#"{"value":5}"#));
    assert_eq!(
        JsonValue::from(candidate["values"].as_array().unwrap()[..5].to_vec()),
        j(r#"[{"value":5},{"value":5},{"value":5},{"value":5},{"value":5}]"#)
    );
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn deletes_and_accepts_valid_placements_before_changing_the_draft() {
    let initial = j(r#"{"optional":"remove","payload":null,"number":0,"values":[1,2]}"#);
    let tracker = track(initial.clone()).unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    assert_eq!(state.value().unwrap(), initial);
    state.delete("optional").unwrap();
    state.set("payload", j(r#"{"valid":true}"#)).unwrap();
    state
        .child("values")
        .unwrap()
        .push([j(r#"{"valid":true}"#)])
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value(),
        &j(r#"{"payload":{"valid":true},"number":0,"values":[1,2,{"valid":true}]}"#)
    );
    assert_eq!(&replay(&initial, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn expands_repeated_source_aliases_into_independent_placements() {
    let tracker = track(j(r#"{"left":null,"right":null,"rows":[]}"#)).unwrap();
    let shared = j(r#"{"nested":{"value":1}}"#);
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.set("left", shared.clone()).unwrap();
    state.set("right", shared.clone()).unwrap();
    state
        .child("rows")
        .unwrap()
        .push([shared.clone(), shared])
        .unwrap();
    state
        .child("left")
        .unwrap()
        .child("nested")
        .unwrap()
        .set("value", 9)
        .unwrap();
    state
        .child("rows")
        .unwrap()
        .child(0)
        .unwrap()
        .child("nested")
        .unwrap()
        .set("value", 8)
        .unwrap();
    let prepared = change.prepare().unwrap();
    let value = prepared.value();
    assert_eq!(
        value,
        &j(
            r#"{"left":{"nested":{"value":9}},"right":{"nested":{"value":1}},"rows":[{"nested":{"value":8}},{"nested":{"value":1}}]}"#
        )
    );
    assert!(!value["left"].strict_equals(&value["right"]));
    assert!(!value["rows"][0].strict_equals(&value["rows"][1]));
    assert_eq!(&replay(&tracker.value(), prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn deep_clones_draft_sourced_placements_within_and_across_revisions() {
    let tracker =
        track(j(r#"{"a":{"child":{"value":1}},"b":null,"rows":[{"child":{"value":1}},{"child":{"value":2}}]}"#)).unwrap();
    let first = tracker.begin_change();
    let state = first.state().unwrap();
    state.set("b", state.child("a").unwrap()).unwrap();
    state
        .child("b")
        .unwrap()
        .child("child")
        .unwrap()
        .set("value", 3)
        .unwrap();
    let rows = state.child("rows").unwrap();
    rows.set(1, rows.child(0).unwrap()).unwrap();
    let first_prepared = first.prepare().unwrap();
    let value = first_prepared.value();
    assert_eq!(value["a"]["child"]["value"], JsonValue::from(1));
    assert_eq!(value["b"]["child"]["value"], JsonValue::from(3));
    assert!(!value["a"].strict_equals(&value["b"]));
    assert!(!value["a"]["child"].strict_equals(&value["b"]["child"]));
    assert!(!value["rows"][0].strict_equals(&value["rows"][1]));
    assert!(!value["rows"][0]["child"].strict_equals(&value["rows"][1]["child"]));
    expect_alias_free(value);
    tracker.adopt(&first_prepared).unwrap();

    let base = clone(&tracker.value());
    let second = tracker.begin_change();
    second
        .state()
        .unwrap()
        .child("rows")
        .unwrap()
        .child(1)
        .unwrap()
        .child("child")
        .unwrap()
        .set("value", 4)
        .unwrap();
    let second_prepared = second.prepare().unwrap();
    let values: Vec<JsonValue> = second_prepared.value()["rows"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row["child"]["value"].clone())
        .collect();
    assert_eq!(values, [JsonValue::from(1), JsonValue::from(4)]);
    assert_eq!(
        &replay(&base, second_prepared.ops()),
        second_prepared.value()
    );
    expect_alias_free(second_prepared.value());
    tracker.adopt(&second_prepared).unwrap();
}

#[test]
fn distinguishes_raw_committed_references_from_draft_references() {
    let tracker = track(j(
        r#"{"source":{"value":1},"rawCopy":null,"draftCopy":null}"#,
    ))
    .unwrap();
    let raw = tracker.value()["source"].clone();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.child("source").unwrap().set("value", 2).unwrap();
    state.set("rawCopy", raw).unwrap();
    state
        .set("draftCopy", state.child("source").unwrap())
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value(),
        &j(r#"{"source":{"value":2},"rawCopy":{"value":1},"draftCopy":{"value":2}}"#)
    );
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn folds_edits_to_introduced_object_and_array_subtrees_into_placement_payloads() {
    let tracker = track(j(r#"{"nested":null,"rows":[]}"#)).unwrap();
    let change = tracker.begin_change();
    let state = change.state().unwrap();
    state.set("nested", j(r#"{"rows":[{"value":1}]}"#)).unwrap();
    let nested_rows = state.child("nested").unwrap().child("rows").unwrap();
    nested_rows.child(0).unwrap().set("value", 2).unwrap();
    nested_rows.push([j(r#"{"value":3}"#)]).unwrap();
    let rows = state.child("rows").unwrap();
    rows.push([j(r#"{"values":[1]}"#)]).unwrap();
    rows.child(0)
        .unwrap()
        .child("values")
        .unwrap()
        .push([2])
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.ops(),
        ops(
            r#"[["s",["nested"],{"rows":[{"value":2},{"value":3}]}],["p",["rows"],0,0,[{"values":[1,2]}]]]"#
        )
    );
    assert_eq!(&replay(&tracker.value(), prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn folds_pathological_operation_counts_without_payload_cost_estimation() {
    let wide: JsonValue = (0..5_000)
        .map(|index| (format!("field{index}"), JsonValue::from(0)))
        .collect::<JsonObject>()
        .into();
    let wide_tracker = track(wide).unwrap();
    let wide_base = clone(&wide_tracker.value());
    let wide_change = wide_tracker.begin_change();
    let wide_state = wide_change.state().unwrap();
    for index in 0..5_000 {
        wide_state.set(format!("field{index}"), 1).unwrap();
    }
    let wide_prepared = wide_change.prepare().unwrap();
    assert_eq!(wide_prepared.ops().len(), 1);
    assert_eq!(wide_prepared.ops()[0].verb(), "r");
    assert_eq!(
        &replay(&wide_base, wide_prepared.ops()),
        wide_prepared.value()
    );
    wide_tracker.adopt(&wide_prepared).unwrap();

    let sparse_tracker = track(with(
        "rows",
        rows(15_000, |value| format!(r#"{{"value":{value}}}"#)),
    ))
    .unwrap();
    let sparse_base = clone(&sparse_tracker.value());
    let sparse_change = sparse_tracker.begin_change();
    let sparse_rows = sparse_change.state().unwrap().child("rows").unwrap();
    for index in (0..15_000).step_by(3) {
        let negative = -f64::from(u32::try_from(index).unwrap()) - 1.0;
        sparse_rows
            .child(index)
            .unwrap()
            .set("value", int(negative))
            .unwrap();
    }
    let sparse_prepared = sparse_change.prepare().unwrap();
    assert_eq!(sparse_prepared.ops().len(), 1);
    assert_eq!(sparse_prepared.ops()[0].verb(), "r");
    assert_eq!(
        &replay(&sparse_base, sparse_prepared.ops()),
        sparse_prepared.value()
    );
    sparse_tracker.adopt(&sparse_prepared).unwrap();
}

#[test]
fn shares_immutable_operation_placements_with_the_materialized_candidate() {
    let tracker = track(j(r#"{"rows":[]}"#)).unwrap();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .child("rows")
        .unwrap()
        .push([j(r#"{"value":1}"#)])
        .unwrap();
    let prepared = change.prepare().unwrap();
    let Op::Splice(_, _, _, items) = &prepared.ops()[0] else {
        panic!("expected splice");
    };
    assert!(items[0].strict_equals(&prepared.value()["rows"][0]));
    tracker.adopt(&prepared).unwrap();
    assert!(tracker.value().strict_equals(prepared.value()));
}

// ─── Piece arrays ────────────────────────────────────────────────────────────

#[test]
fn keeps_adoption_independent_from_detached_permutation_metadata() {
    let tracker = track(j(r#"{"values":[3,1,2]}"#)).unwrap();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .child("values")
        .unwrap()
        .sort_by(compare_numbers)
        .unwrap();
    let prepared = change.prepare().unwrap();
    let mut detached = prepared.ops().to_vec();
    let permutation = detached.iter_mut().find_map(|operation| match operation {
        Op::Move(_, permutation) => Some(permutation),
        _ => None,
    });
    permutation.expect("expected permutation").reverse();
    tracker.adopt(&prepared).unwrap();
    assert_eq!(tracker.value()["values"], j("[1,2,3]"));
}

fn compare_numbers(left: &DraftItem, right: &DraftItem) -> Ordering {
    let left = left.as_value().and_then(JsonValue::as_f64).unwrap();
    let right = right.as_value().and_then(JsonValue::as_f64).unwrap();
    left.partial_cmp(&right).unwrap()
}

#[test]
fn matches_native_splice_with_zero_or_one_argument() {
    let no_arguments = track(j(r#"{"values":[1,2,3]}"#)).unwrap();
    let change = no_arguments.begin_change();
    let removed = change
        .state()
        .unwrap()
        .child("values")
        .unwrap()
        .splice(0, 0, Vec::<JsonValue>::new())
        .unwrap();
    assert!(removed.is_empty());
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value()["values"], j("[1,2,3]"));
    assert!(prepared.ops().is_empty());
    no_arguments.adopt(&prepared).unwrap();

    let one_argument = track(j(r#"{"values":[1,2,3,4]}"#)).unwrap();
    let change = one_argument.begin_change();
    let removed = change
        .state()
        .unwrap()
        .child("values")
        .unwrap()
        .splice(1, i64::MAX, Vec::<JsonValue>::new())
        .unwrap();
    let removed: Vec<JsonValue> = removed
        .iter()
        .map(|item| item.to_value().unwrap())
        .collect();
    assert_eq!(JsonValue::from(removed), j("[2,3,4]"));
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value()["values"], j("[1]"));
    assert_eq!(
        &replay(&one_argument.value(), prepared.ops()),
        prepared.value()
    );
    one_argument.adopt(&prepared).unwrap();

    let past_end = track(j(r#"{"values":[1,2,3]}"#)).unwrap();
    let change = past_end.begin_change();
    let removed = change
        .state()
        .unwrap()
        .child("values")
        .unwrap()
        .splice(3, i64::MAX, Vec::<JsonValue>::new())
        .unwrap();
    assert!(removed.is_empty());
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value()["values"], j("[1,2,3]"));
    past_end.adopt(&prepared).unwrap();
}

#[test]
fn supports_all_structural_mutators_and_native_return_values() {
    let tracker = track(j(r#"{"values":[3,1,2]}"#)).unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    assert_eq!(values.push([4]).unwrap(), 4);
    assert_eq!(
        values.pop().unwrap(),
        Some(DraftItem::Value(JsonValue::from(4)))
    );
    assert_eq!(values.unshift([0]).unwrap(), 4);
    assert_eq!(
        values.shift().unwrap(),
        Some(DraftItem::Value(JsonValue::from(0)))
    );
    assert_eq!(
        values.splice(1, 1, [5, 4]).unwrap(),
        [DraftItem::Value(JsonValue::from(1))]
    );
    assert_eq!(values.sort_by(compare_numbers).unwrap(), values);
    assert_eq!(values.reverse().unwrap(), values);
    values.fill(9, 1, 3).unwrap();
    values.copy_within(1, 0, 2).unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value(), &j(r#"{"values":[5,5,9,2]}"#));
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn tracks_held_handles_after_reindex_and_suppresses_detached_writes() {
    let tracker = track(j(
        r#"{"values":[{"value":"a"},{"value":"b"},{"value":"c"}]}"#,
    ))
    .unwrap();
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    let held = values.child(1).unwrap();
    values.unshift([j(r#"{"value":"front"}"#)]).unwrap();
    held.set("value", "moved").unwrap();
    assert_eq!(text(&values.child(2).unwrap(), "value"), "moved");
    values.splice(2, 1, Vec::<JsonValue>::new()).unwrap();
    held.set("value", "detached").unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value(),
        &j(r#"{"values":[{"value":"front"},{"value":"a"},{"value":"c"}]}"#)
    );
    assert_eq!(&replay(&tracker.value(), prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn replays_introduced_moved_then_edited_array_descendants() {
    let tracker = track(j(r#"{"values":[]}"#)).unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    values.push([j(r#"{"id":1,"nested":[1]}"#)]).unwrap();
    let held = values.child(0).unwrap();
    values.unshift([j(r#"{"id":0,"nested":[]}"#)]).unwrap();
    held.child("nested").unwrap().push([2]).unwrap();
    values.reverse().unwrap();
    held.child("nested").unwrap().push([3]).unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value(),
        &j(r#"{"values":[{"id":1,"nested":[1,2,3]},{"id":0,"nested":[]}]}"#)
    );
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

fn compare_field(field: &'static str) -> impl Fn(&DraftItem, &DraftItem) -> Ordering {
    move |left, right| {
        let left = number(left.as_draft().unwrap(), field);
        let right = number(right.as_draft().unwrap(), field);
        left.partial_cmp(&right).unwrap()
    }
}

#[test]
fn combines_movement_and_edits_with_permutation_plus_final_paths() {
    let tracker = track(j(
        r#"{"values":[{"rank":3,"edited":0},{"rank":1,"edited":0},{"rank":2,"edited":0}]}"#,
    ))
    .unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    let held = values.child(0).unwrap();
    values.sort_by(compare_field("rank")).unwrap();
    held.set("edited", 1).unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.ops()[0], ops(r#"[["m",["values"],[1,2,0]]]"#)[0]);
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn keeps_comparator_writes_and_structurally_reentrant_appends() {
    let tracker = track(j(
        r#"{"values":[{"rank":2,"comparisons":0},{"rank":1,"comparisons":0}]}"#,
    ))
    .unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    let mut appended = false;
    values
        .sort_by(|left, right| {
            let (left, right) = (left.as_draft().unwrap(), right.as_draft().unwrap());
            left.set("comparisons", int(number(left, "comparisons") + 1.0))
                .unwrap();
            right
                .set("comparisons", int(number(right, "comparisons") + 1.0))
                .unwrap();
            if !appended {
                appended = true;
                values.set(0, j(r#"{"rank":9,"comparisons":0}"#)).unwrap();
                values.push([j(r#"{"rank":3,"comparisons":0}"#)]).unwrap();
            }
            number(left, "rank")
                .partial_cmp(&number(right, "rank"))
                .unwrap()
        })
        .unwrap();
    let prepared = change.prepare().unwrap();
    let field = |name: &str| -> Vec<JsonValue> {
        prepared.value()["values"]
            .as_array()
            .unwrap()
            .iter()
            .map(|value| value[name].clone())
            .collect()
    };
    assert_eq!(
        field("rank"),
        [JsonValue::from(1), JsonValue::from(2), JsonValue::from(3)]
    );
    assert_eq!(
        field("comparisons"),
        [JsonValue::from(1), JsonValue::from(1), JsonValue::from(0)]
    );
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn normalizes_duplicate_entries_created_by_structurally_reentrant_sort_callbacks() {
    let tracker = track(j(
        r#"{"values":[{"rank":2,"edited":0,"nested":{"value":0}},{"rank":1,"edited":0,"nested":{"value":0}}]}"#,
    ))
    .unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    let mut inserted = false;
    values
        .sort_by(|left, right| {
            for item in [left, right] {
                let draft = item.as_draft().unwrap();
                let rank = number(draft, "rank");
                draft.set("edited", int(rank * 10.0)).unwrap();
                draft
                    .child("nested")
                    .unwrap()
                    .set("value", int(rank * 100.0))
                    .unwrap();
            }
            if !inserted {
                inserted = true;
                values
                    .unshift([j(r#"{"rank":4,"edited":0,"nested":{"value":0}}"#)])
                    .unwrap();
            }
            let (left, right) = (left.as_draft().unwrap(), right.as_draft().unwrap());
            number(left, "rank")
                .partial_cmp(&number(right, "rank"))
                .unwrap()
        })
        .unwrap();
    let prepared = change.prepare().unwrap();
    let items = prepared.value()["values"].as_array().unwrap().to_vec();
    let field = |pick: &dyn Fn(&JsonValue) -> JsonValue| -> Vec<JsonValue> {
        items.iter().map(pick).collect()
    };
    assert_eq!(
        field(&|value| value["rank"].clone()),
        [1, 2, 1].map(JsonValue::from)
    );
    assert_eq!(
        field(&|value| value["edited"].clone()),
        [10, 20, 10].map(JsonValue::from)
    );
    assert_eq!(
        field(&|value| value["nested"]["value"].clone()),
        [100, 200, 100].map(JsonValue::from)
    );
    assert!(!items[0].strict_equals(&items[2]));
    assert!(!items[0]["nested"].strict_equals(&items[2]["nested"]));
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    expect_alias_free(prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn folds_dense_child_and_direct_index_edits_into_one_full_array_operation() {
    let rows_tracker = track(with(
        "rows",
        rows(1_000, |value| format!(r#"{{"value":{value}}}"#)),
    ))
    .unwrap();
    let rows_base = clone(&rows_tracker.value());
    let rows_change = rows_tracker.begin_change();
    let draft_rows = rows_change.state().unwrap().child("rows").unwrap();
    for index in 0..1_000 {
        let row = draft_rows.child(index).unwrap();
        row.set("value", int(number(&row, "value") + 1.0)).unwrap();
    }
    let rows_prepared = rows_change.prepare().unwrap();
    assert_eq!(rows_prepared.ops().len(), 1);
    assert_eq!(rows_prepared.ops()[0].verb(), "p");
    assert_eq!(
        &replay(&rows_base, rows_prepared.ops()),
        rows_prepared.value()
    );
    rows_tracker.adopt(&rows_prepared).unwrap();

    let values_tracker = track(with("values", rows(1_000, |value| value.to_string()))).unwrap();
    let values_base = clone(&values_tracker.value());
    let values_change = values_tracker.begin_change();
    let values = values_change.state().unwrap().child("values").unwrap();
    for index in 0..600_u32 {
        values
            .set(
                usize::try_from(index).unwrap(),
                int(-f64::from(index) - 1.0),
            )
            .unwrap();
    }
    let values_prepared = values_change.prepare().unwrap();
    assert_eq!(values_prepared.ops().len(), 1);
    assert_eq!(values_prepared.ops()[0].verb(), "p");
    assert_eq!(
        &replay(&values_base, values_prepared.ops()),
        values_prepared.value()
    );
    values_tracker.adopt(&values_prepared).unwrap();
}

#[test]
fn folds_only_a_deeply_nested_dense_array_region() {
    let tracker = track(with(
        "rows",
        rows(2_000, |value| {
            format!(r#"{{"nested":{{"value":{value}}}}}"#)
        }),
    ))
    .unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let draft_rows = change.state().unwrap().child("rows").unwrap();
    draft_rows
        .child(0)
        .unwrap()
        .child("nested")
        .unwrap()
        .set("value", -1)
        .unwrap();
    for index in 500..1_000_u32 {
        let row = draft_rows.child(usize::try_from(index).unwrap()).unwrap();
        row.child("nested")
            .unwrap()
            .set("value", int(-f64::from(index)))
            .unwrap();
    }
    let prepared = change.prepare().unwrap();
    let splice = prepared
        .ops()
        .iter()
        .find(|operation| operation.verb() == "p")
        .unwrap();
    let Op::Splice(path, index, remove, items) = splice else {
        panic!("expected regional splice");
    };
    assert_eq!(
        (path.clone(), *index, *remove),
        (vec!["rows".into()], 500, 500)
    );
    assert_eq!(items.len(), 500);
    assert_eq!(prepared.ops().len(), 2);
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn does_not_cache_emission_paths_for_nested_reserved_key_folds_covered_by_an_outer_region() {
    let mut rows_value: Vec<JsonValue> = (0..400).map(|_| j(r#"{"flag":0}"#)).collect();
    let special_values: Vec<String> = (0..400).map(|value: i32| value.to_string()).collect();
    let special = j(&format!(
        r#"{{"__proto__":{{"values":[{}]}}}}"#,
        special_values.join(",")
    ));
    rows_value[100]
        .as_object_mut()
        .unwrap()
        .insert("special", special);
    let tracker = track(with("rows", JsonValue::from(rows_value))).unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let draft_rows = change.state().unwrap().child("rows").unwrap();
    for index in 0..256 {
        draft_rows.child(index).unwrap().set("flag", 1).unwrap();
    }
    let values = draft_rows
        .child(100)
        .unwrap()
        .child("special")
        .unwrap()
        .child("__proto__")
        .unwrap()
        .child("values")
        .unwrap();
    for index in 0..256_u32 {
        values
            .set(
                usize::try_from(index).unwrap(),
                int(-f64::from(index) - 1.0),
            )
            .unwrap();
    }
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.ops().len(), 1);
    let Op::Splice(path, index, remove, _) = &prepared.ops()[0] else {
        panic!("expected splice");
    };
    assert_eq!(
        (path.clone(), *index, *remove),
        (vec!["rows".into()], 0, 256)
    );
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn suppresses_nested_structural_and_leaf_operations_covered_by_an_outer_dense_region() {
    let big: Vec<String> = (0..400)
        .map(|value| format!(r#"{{"value":{value}}}"#))
        .collect();
    let tracker = track(with(
        "rows",
        rows(400, |index| {
            if index == 100 {
                format!(r#"{{"flag":0,"values":[{}]}}"#, big.join(","))
            } else {
                r#"{"flag":0,"values":[]}"#.to_owned()
            }
        }),
    ))
    .unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let draft_rows = change.state().unwrap().child("rows").unwrap();
    for index in 0..256 {
        draft_rows.child(index).unwrap().set("flag", 1).unwrap();
    }
    let values = draft_rows.child(100).unwrap().child("values").unwrap();
    for index in 0..256_u32 {
        values
            .child(usize::try_from(index).unwrap())
            .unwrap()
            .set("value", int(-f64::from(index) - 1.0))
            .unwrap();
    }
    values.push([j(r#"{"value":999}"#)]).unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.ops().len(), 1);
    let Op::Splice(path, index, remove, _) = &prepared.ops()[0] else {
        panic!("expected splice");
    };
    assert_eq!(
        (path.clone(), *index, *remove),
        (vec!["rows".into()], 0, 256)
    );
    assert_eq!(
        prepared.value()["rows"][100]["values"]
            .as_array()
            .unwrap()
            .len(),
        401
    );
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn emits_multiple_disjoint_dense_regions_and_preserves_operations_outside_their_boundaries() {
    let tracker = track(with(
        "values",
        rows(1_400, |value| format!(r#"{{"value":{value}}}"#)),
    ))
    .unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    let edit = |index: u32| {
        values
            .child(usize::try_from(index).unwrap())
            .unwrap()
            .set("value", int(-f64::from(index) - 1.0))
            .unwrap();
    };
    for index in [97, 358, 897, 1_158] {
        edit(index);
    }
    for index in 100..356 {
        edit(index);
    }
    for index in 900..1_156 {
        edit(index);
    }
    let prepared = change.prepare().unwrap();
    let splices: Vec<(usize, usize)> = prepared
        .ops()
        .iter()
        .filter_map(|operation| match operation {
            Op::Splice(_, index, remove, _) => Some((*index, *remove)),
            _ => None,
        })
        .collect();
    assert_eq!(splices, [(100, 256), (900, 256)]);
    for index in [97_u32, 358, 897, 1_158] {
        let expected = Op::Set(
            vec![
                "values".into(),
                usize::try_from(index).unwrap().into(),
                "value".into(),
            ],
            int(-f64::from(index) - 1.0),
        );
        assert!(prepared.ops().contains(&expected));
    }
    assert_eq!(prepared.ops().len(), 6);
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn normalizes_a_20000_operation_queue_transaction_to_two_operations() {
    let tracker = track(with(
        "values",
        rows(20_000, |value| format!(r#"{{"value":{value}}}"#)),
    ))
    .unwrap();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    for index in 0..10_000 {
        values.shift().unwrap();
        values
            .push([j(&format!(r#"{{"value":{}}}"#, 20_000 + index))])
            .unwrap();
    }
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.ops().len(), 2);
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn handles_adversarial_fragmentation_and_resolves_held_handles() {
    let size = 20_000;
    let tracker = track(with(
        "values",
        rows(size, |value| format!(r#"{{"value":{value}}}"#)),
    ))
    .unwrap();
    let mut expected: Vec<JsonValue> = tracker.value()["values"].as_array().unwrap().to_vec();
    let base = clone(&tracker.value());
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    let held_indices = [1, 1_001, 5_001, 10_001, 15_001, 19_999];
    let held: Vec<Draft> = held_indices
        .iter()
        .map(|index| values.child(*index).unwrap())
        .collect();
    for index in (0..size).step_by(2) {
        let replacement = j(&format!(
            r#"{{"value":{}}}"#,
            -i64::try_from(index).unwrap() - 1
        ));
        values
            .splice(i64::try_from(index).unwrap(), 1, [replacement.clone()])
            .unwrap();
        expected[index] = replacement;
    }
    for handle in &held {
        handle
            .set("value", int(number(handle, "value") + 100_000.0))
            .unwrap();
    }
    for index in held_indices {
        let value = expected[index]["value"].as_f64().unwrap() + 100_000.0;
        expected[index] = with("value", int(value));
    }
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value(), &with("values", JsonValue::from(expected)));
    assert_eq!(&replay(&base, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn normalizes_restored_overrides_and_cancelled_structural_edits_to_no_operations() {
    let tracker = track(j(r#"{"values":[1,2,3]}"#)).unwrap();
    let change = tracker.begin_change();
    let values = change.state().unwrap().child("values").unwrap();
    values.set(1, 9).unwrap();
    values.set(1, 2).unwrap();
    values.reverse().unwrap();
    values.reverse().unwrap();
    values.push([4]).unwrap();
    assert_eq!(
        values.pop().unwrap(),
        Some(DraftItem::Value(JsonValue::from(4)))
    );
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.value(), &j(r#"{"values":[1,2,3]}"#));
    assert!(prepared.ops().is_empty());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn handles_null_sparse_overrides_without_confusing_absence() {
    let tracker = track(with("values", rows(10_000, |value| value.to_string()))).unwrap();
    settle(&tracker, |draft| {
        let values = draft.child("values").unwrap();
        values.set(17, JsonValue::Null).unwrap();
        values.set(9_000, JsonValue::Null).unwrap();
    });
    assert!(tracker.value()["values"][17].is_null());
    assert!(tracker.value()["values"][9_000].is_null());
}

#[test]
fn supports_self_overlapping_fill_and_copy_within_by_value() {
    let tracker = track(j(r#"{"values":[{"n":0},{"n":1},{"n":2},{"n":3}]}"#)).unwrap();
    settle(&tracker, |draft| {
        let values = draft.child("values").unwrap();
        values.copy_within(1, 0, 3).unwrap();
        values.fill(values.child(1).unwrap(), 0, 2).unwrap();
        values.child(0).unwrap().set("n", 9).unwrap();
    });
    let value = tracker.value();
    let numbers: Vec<JsonValue> = value["values"]
        .as_array()
        .unwrap()
        .iter()
        .map(|item| item["n"].clone())
        .collect();
    assert_eq!(numbers, [9, 0, 1, 2].map(JsonValue::from));
    assert!(!value["values"][0].strict_equals(&value["values"][1]));
}

#[test]
fn inserts_100000_items_with_unshift_and_splice() {
    for method in ["unshift", "splice"] {
        let tracker = track(j(r#"{"values":[-1]}"#)).unwrap();
        let base = clone(&tracker.value());
        let change = tracker.begin_change();
        let values = change.state().unwrap().child("values").unwrap();
        let items: Vec<JsonValue> = (0..100_000).map(JsonValue::from).collect();
        if method == "unshift" {
            values.unshift(items).unwrap();
        } else {
            values.splice(1, 0, items).unwrap();
        }
        let prepared = change.prepare().unwrap();
        let result = prepared.value()["values"].as_array().unwrap();
        assert_eq!(result.len(), 100_001);
        assert_eq!(
            result[if method == "unshift" { 99_999 } else { 100_000 }],
            JsonValue::from(99_999)
        );
        assert_eq!(&replay(&base, prepared.ops()), prepared.value());
        tracker.adopt(&prepared).unwrap();
    }
}

// ─── Randomized transactions ─────────────────────────────────────────────────

/// The TS test's mulberry32 generator.
fn random(mut seed: i32) -> impl FnMut() -> f64 {
    move || {
        #[allow(clippy::cast_possible_wrap)] // the TS `| 0` reinterprets the constant as int32
        let increment = 0x6d2b_79f5_u32 as i32;
        seed = seed.wrapping_add(increment);
        #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
        // JS int32/uint32 reinterpretation
        {
            let mut value = (seed ^ ((seed as u32 >> 15) as i32)).wrapping_mul(1 | seed);
            value = value
                .wrapping_add((value ^ ((value as u32 >> 7) as i32)).wrapping_mul(0x3d | value))
                ^ value;
            f64::from((value ^ ((value as u32 >> 14) as i32)) as u32) / 4_294_967_296.0
        }
    }
}

fn item(value: i64) -> JsonValue {
    j(&format!(r#"{{"id":{value},"score":{}}}"#, value % 7))
}

/// The TS `mutate` on a plain document.
#[allow(clippy::cast_precision_loss)] // values stay far below 2^53
fn mutate_model(document: &mut JsonValue, choice: u32, value: i64) {
    let object = document.as_object_mut().unwrap();
    match choice {
        0 => {
            let text = object.get("text").unwrap().as_str().unwrap().to_owned();
            object.insert("text", JsonValue::from(format!("{text}-{value}")));
        }
        9 => {
            let meta = object.get_mut("meta").unwrap().as_object_mut().unwrap();
            let revision = meta.get("revision").unwrap().as_f64().unwrap();
            meta.insert("revision", int(revision + 1.0));
            meta.insert("label", JsonValue::from(format!("r-{value}")));
        }
        10 => {
            object
                .get_mut("meta")
                .unwrap()
                .as_object_mut()
                .unwrap()
                .remove("label");
        }
        _ => {
            let values = object.get_mut("values").unwrap().as_array_mut().unwrap();
            let length = i64::try_from(values.len()).unwrap();
            match choice {
                1 => values.push(item(value)),
                2 => values.insert(0, item(value)),
                3 if length > 0 => {
                    values.remove(0);
                }
                4 if length > 0 => {
                    values.pop();
                }
                5 => {
                    let index = if length == 0 { 0 } else { value % (length + 1) };
                    let remove = if length == 0 { 0 } else { value % 2 };
                    let index = usize::try_from(index).unwrap();
                    let end = (index + usize::try_from(remove).unwrap()).min(values.len());
                    values.splice(index..end, [item(value)]);
                }
                6 => values.reverse(),
                7 => values.sort_by(|left, right| {
                    left["id"]
                        .as_f64()
                        .partial_cmp(&right["id"].as_f64())
                        .unwrap()
                }),
                8 if length > 0 => {
                    let index = usize::try_from(value % length).unwrap();
                    values[index]
                        .as_object_mut()
                        .unwrap()
                        .insert("score", int(value as f64));
                }
                _ => {}
            }
        }
    }
}

/// The TS `mutate` on a draft.
#[allow(clippy::cast_precision_loss)] // values stay far below 2^53
fn mutate_draft(document: &Draft, choice: u32, value: i64) {
    let values = document.child("values").unwrap();
    let length = i64::try_from(values.len().unwrap()).unwrap();
    match choice {
        0 => document
            .set("text", format!("{}-{value}", text(document, "text")))
            .unwrap(),
        1 => {
            values.push([item(value)]).unwrap();
        }
        2 => {
            values.unshift([item(value)]).unwrap();
        }
        3 if length > 0 => {
            values.shift().unwrap();
        }
        4 if length > 0 => {
            values.pop().unwrap();
        }
        5 => {
            let index = if length == 0 { 0 } else { value % (length + 1) };
            let remove = if length == 0 { 0 } else { value % 2 };
            values.splice(index, remove, [item(value)]).unwrap();
        }
        6 => {
            values.reverse().unwrap();
        }
        7 => {
            values.sort_by(compare_field("id")).unwrap();
        }
        8 if length > 0 => {
            values
                .child(usize::try_from(value % length).unwrap())
                .unwrap()
                .set("score", int(value as f64))
                .unwrap();
        }
        9 => {
            let meta = document.child("meta").unwrap();
            meta.set("revision", int(number(&meta, "revision") + 1.0))
                .unwrap();
            meta.set("label", format!("r-{value}")).unwrap();
        }
        10 => document.child("meta").unwrap().delete("label").unwrap(),
        _ => {}
    }
}

#[test]
fn matches_policy_detached_replay_and_adopted_state_after_multi_operation_transactions() {
    for seed in 1..=40 {
        let mut rng = random(seed);
        let initial = j(
            r#"{"values":[{"id":0,"score":0},{"id":1,"score":0},{"id":2,"score":0},{"id":3,"score":0}],"text":"start","meta":{"revision":0}}"#,
        );
        let tracker = track(initial.clone()).unwrap();
        let mut expected = clone(&initial);
        for transaction in 0..25 {
            let base_root = tracker.value();
            let base = clone(&base_root);
            let change = tracker.begin_change();
            let state = change.state().unwrap();
            for operation in 0..5 {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                // floor of [0, 11)
                let choice = (rng() * 11.0).floor() as u32;
                let value = i64::from(seed) * 10_000 + transaction * 10 + operation;
                mutate_model(&mut expected, choice, value);
                mutate_draft(&state, choice, value);
            }
            let prepared = change.prepare().unwrap();
            let policy = clone(prepared.value());
            assert_eq!(
                base_root, base,
                "prepare changed base seed {seed} transaction {transaction}"
            );
            assert_eq!(
                policy, expected,
                "policy seed {seed} transaction {transaction}"
            );
            assert_eq!(
                replay(&base, prepared.ops()),
                policy,
                "replay seed {seed} transaction {transaction}"
            );
            tracker.adopt(&prepared).unwrap();
            assert_eq!(
                base_root, base,
                "adopt changed base seed {seed} transaction {transaction}"
            );
            assert!(tracker.value().strict_equals(prepared.value()));
            assert_eq!(
                tracker.value(),
                policy,
                "adopt seed {seed} transaction {transaction}"
            );
            expect_alias_free(&tracker.value());
        }
    }
}

// ─── Object emission scaling ─────────────────────────────────────────────────

#[test]
fn orders_many_reverse_depth_object_edits_through_the_bounded_fallback() {
    let mut initial = j(r#"{"value":0}"#);
    for _ in 0..512 {
        initial = JsonValue::from(JsonObject::from_iter([
            ("value", JsonValue::from(0)),
            ("next", initial),
        ]));
    }
    let tracker = track(initial.clone()).unwrap();
    let change = tracker.begin_change();
    let mut nodes = Vec::new();
    let mut node = Some(change.state().unwrap());
    while let Some(current) = node {
        node = match current.get("next").unwrap() {
            Some(DraftItem::Draft(next)) => Some(next),
            _ => None,
        };
        nodes.push(current);
    }
    for (index, node) in nodes.iter().enumerate().rev() {
        node.set("value", JsonValue::try_from(index + 1).unwrap())
            .unwrap();
    }
    let prepared = change.prepare().unwrap();
    assert_eq!(prepared.ops().len(), nodes.len());
    assert_eq!(&replay(&initial, prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
    expect_alias_free(&tracker.value());
}

// ─── Security and storage-style cloning ─────────────────────────────────────

#[test]
fn defines_own_properties() {
    let tracker = track(j("{}")).unwrap();
    settle(&tracker, |draft| draft.set("trap", 1).unwrap());
    assert_eq!(tracker.value(), j(r#"{"trap":1}"#));
}

#[test]
fn handles_reserved_own_keys_without_prototype_pollution() {
    let initial = j(r#"{"safe":{"__proto__":{"value":1}}}"#);
    let tracker = track(initial).unwrap();
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .child("safe")
        .unwrap()
        .child("__proto__")
        .unwrap()
        .set("value", 2)
        .unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value()["safe"]["__proto__"]["value"],
        JsonValue::from(2)
    );
    assert_eq!(
        prepared.ops(),
        [Op::Set(
            vec!["safe".into()],
            j(r#"{"__proto__":{"value":2}}"#)
        )]
    );
    assert_eq!(&replay(&tracker.value(), prepared.ops()), prepared.value());
    tracker.adopt(&prepared).unwrap();
}

#[test]
fn supports_a_memory_storage_style_recursive_clone_of_prepared_value() {
    let tracker = track(j(r#"{"rows":[{"value":1}]}"#)).unwrap();
    let change = tracker.begin_change();
    let rows = change.state().unwrap().child("rows").unwrap();
    rows.child(0).unwrap().set("value", 2).unwrap();
    rows.push([j(r#"{"value":3}"#)]).unwrap();
    let prepared = change.prepare().unwrap();
    assert_eq!(
        eukhe_chord::json::copy_json(prepared.value()),
        j(r#"{"rows":[{"value":2},{"value":3}]}"#)
    );
    tracker.adopt(&prepared).unwrap();
}
