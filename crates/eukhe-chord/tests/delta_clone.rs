//! Port of `test/delta-clone.test.ts`.
//!
//! Mapped: null prototypes are not represented (plain objects); the
//! untrusted-accessor root has no Rust counterpart, so the O(1) ownership
//! check uses container identity.

mod common;

use common::{clone, j};
use eukhe_chord::delta::{apply, track};
use eukhe_chord::json::JsonValue;

#[test]
fn takes_immutable_ownership_of_the_imported_revision_in_o1() {
    let input = j(
        r#"{"point":{"x":3,"y":7,"pressure":0.1},"rows":[{"values":[0,false,null,"text",{"n":1}]}]}"#,
    );
    let tracker = track(input.clone()).unwrap();
    let value = tracker.value();
    assert!(value.strict_equals(&input));
    assert!(value["point"].strict_equals(&input["point"]));
    assert!(value["rows"][0]["values"][4].strict_equals(&input["rows"][0]["values"][4]));
}

#[test]
fn preserves_an_alias_free_owned_root() {
    let dictionary = j(r#"{"enabled":true,"child":{"n":1}}"#);
    let input = j(r#"{"left":{"nested":[{"n":1}]},"right":{"nested":[{"n":1}]}}"#);
    let mut root = input;
    root.as_object_mut()
        .unwrap()
        .insert("dictionary", dictionary.clone());
    let tracker = track(root).unwrap();
    let value = tracker.value();
    assert!(value["dictionary"].strict_equals(&dictionary));
    assert!(!value["left"].strict_equals(&value["right"]));
    assert!(!value["left"]["nested"][0].strict_equals(&value["right"]["nested"][0]));
}

#[test]
fn does_not_traverse_a_trusted_root_while_taking_ownership() {
    let input = j(r#"{"untrustedAccessor":{"deep":[1,2,3]}}"#);
    let tracker = track(input.clone()).unwrap();
    assert!(tracker.value().strict_equals(&input));
}

#[test]
fn copies_assigned_and_inserted_values_immediately() {
    let tracker = track(j(r#"{"rows":[]}"#)).unwrap();
    let mut assigned = j(r#"{"nested":{"value":1}}"#);
    let change = tracker.begin_change();
    change
        .state()
        .unwrap()
        .child("rows")
        .unwrap()
        .push([assigned.clone()])
        .unwrap();
    assigned
        .as_object_mut()
        .unwrap()
        .get_mut("nested")
        .and_then(JsonValue::as_object_mut)
        .unwrap()
        .insert("value", JsonValue::from(9));
    let row = change
        .state()
        .unwrap()
        .child("rows")
        .unwrap()
        .child(0)
        .unwrap();
    assert_eq!(
        row.child("nested")
            .unwrap()
            .get("value")
            .unwrap()
            .unwrap()
            .to_value()
            .unwrap(),
        JsonValue::from(1)
    );
    let prepared = change.prepare().unwrap();
    assert_eq!(
        prepared.value()["rows"][0]["nested"]["value"],
        JsonValue::from(1)
    );
    let replica = apply(clone(prepared.base()), prepared.ops()).unwrap();
    assert_eq!(&replica, prepared.value());
}
