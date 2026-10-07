//! Port of `test/json.test.ts`.
//!
//! Not portable (no Rust value has the shape): `isJsonValue` of
//! `{ omitted: undefined }`, a `Uint8Array`, `Infinity` (a
//! `serde_json::Value` number is always finite), and a cyclic object; the
//! `copyJson` strict-JSON throws for `undefined` properties and `[undefined]`;
//! the null-prototype check; and "rejects cycles and non-strict container
//! properties" (cycles, sparse arrays, extra array properties, `Array`
//! subclasses, accessors, non-enumerable and symbol keys). The
//! `omitUndefinedProperties` copy is `to_json` of a record whose optional
//! fields use `skip_serializing_if`.

use serde::Serialize;
use serde_json::json as j;

use super::json;
use crate::json::{copy_json, is_json_value, to_json, JsonObject, JsonValue};

#[test]
fn checks_strict_json_without_normalizing_it() {
    assert!(is_json_value(&j!({ "nested": [1, true, null] })));
}

#[test]
fn copies_strict_json_without_retaining_aliases() {
    let shared = json(j!({ "value": 1 }));
    let input = JsonValue::from(
        [("left", shared.clone()), ("right", shared.clone())]
            .into_iter()
            .collect::<JsonObject>(),
    );
    let copied = copy_json(&input);
    assert_eq!(copied, input);
    assert!(!copied.strict_equals(&input));
    assert!(!copied["left"].strict_equals(&shared));
    assert!(!copied["right"].strict_equals(&shared));
    assert!(!copied["left"].strict_equals(&copied["right"]));
}

#[test]
fn optionally_omits_undefined_object_properties_without_normalizing_arrays() {
    #[derive(Serialize)]
    struct Nested {
        #[serde(skip_serializing_if = "Option::is_none")]
        omitted: Option<bool>,
        kept: bool,
    }
    #[derive(Serialize)]
    struct Input {
        kept: i32,
        #[serde(skip_serializing_if = "Option::is_none")]
        omitted: Option<i32>,
        nested: Nested,
    }
    let input = Input {
        kept: 1,
        omitted: None,
        nested: Nested {
            omitted: None,
            kept: true,
        },
    };
    assert_eq!(
        to_json(&input).unwrap(),
        json(j!({ "kept": 1, "nested": { "kept": true } }))
    );
}

#[test]
fn preserves_null_prototypes_and_own_proto_data_properties() {
    let mut input = JsonObject::new();
    input.insert("__proto__", json(j!({ "safe": true })));
    let copied = copy_json(&JsonValue::from(input));
    let object = copied.as_object().unwrap();
    assert!(object.contains_key("__proto__"));
    assert_eq!(object.get("__proto__"), Some(&json(j!({ "safe": true }))));
}
