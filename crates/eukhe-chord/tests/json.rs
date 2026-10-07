//! Port of `test/json.test.ts`, plus the JS-semantics checks of
//! [`JsonValue`] that the TS runtime provides for free.
//!
//! Not representable in Rust (and so not testable): `undefined`, typed
//! arrays, cycles, sparse or subclassed arrays, accessors, hidden and symbol
//! properties. The non-finite number case maps to construction failures.

use std::sync::Arc;

use eukhe_chord::json::{
    copy_json, from_json, is_json_value, to_json, utf16_len, utf16_skip, JsonError, JsonObject,
    JsonValue,
};
use serde::{Deserialize, Serialize};

fn parse(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid json")
}

#[test]
fn is_json_value_checks_strict_json_without_normalizing_it() {
    assert!(is_json_value(
        &serde_json::json!({ "nested": [1, true, null] })
    ));
    assert!(JsonValue::try_from(f64::INFINITY).is_err());
    assert!(matches!(
        JsonValue::parse("1e400"),
        Err(JsonError::Parse(_))
    ));
}

#[test]
fn copy_json_copies_strict_json_without_retaining_aliases() {
    let shared = parse(r#"{"value":1}"#);
    let input = JsonValue::from(JsonObject::from_iter([
        ("left", shared.clone()),
        ("right", shared.clone()),
    ]));
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
        omitted: Option<u8>,
        kept: bool,
    }
    #[derive(Serialize)]
    struct Input {
        kept: u8,
        #[serde(skip_serializing_if = "Option::is_none")]
        omitted: Option<u8>,
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
        to_json(&input).expect("strict"),
        parse(r#"{"kept":1,"nested":{"kept":true}}"#)
    );
    assert!(matches!(
        to_json(&vec![f64::NAN]),
        Err(JsonError::NonFinite)
    ));
}

#[test]
fn preserves_own_proto_data_properties() {
    let input = parse(r#"{"__proto__":{"safe":true}}"#);
    let copied = copy_json(&input);
    assert!(copied
        .as_object()
        .expect("object")
        .contains_key("__proto__"));
    assert_eq!(copied["__proto__"], parse(r#"{"safe":true}"#));
}

#[test]
fn rejects_non_strict_values_at_construction() {
    assert!(matches!(
        JsonValue::try_from(f64::NAN),
        Err(JsonError::NonFinite)
    ));
    assert!(matches!(
        JsonValue::try_from(9_007_199_254_740_993_u64),
        Err(JsonError::UnsafeInteger)
    ));
    assert!(serde_json::from_str::<JsonValue>("[1, 2").is_err());
}

#[test]
fn objects_keep_js_own_property_order() {
    let mut object = JsonObject::new();
    object.insert("first", JsonValue::from(1));
    object.insert("second", JsonValue::from(2));
    object.insert("2", JsonValue::from("two"));
    object.insert("1", JsonValue::from("one"));
    object.insert("4294967295", JsonValue::from("not an index"));
    object.insert("01", JsonValue::from("not canonical"));
    assert_eq!(
        object.keys().collect::<Vec<_>>(),
        ["1", "2", "first", "second", "4294967295", "01"]
    );
    object.remove("first");
    object.insert("first", JsonValue::from(3));
    object.insert("second", JsonValue::from(4));
    assert_eq!(
        object.keys().collect::<Vec<_>>(),
        ["1", "2", "second", "4294967295", "01", "first"]
    );
    assert_eq!(
        parse(r#"{"b":1,"a":2,"b":3}"#).to_string(),
        r#"{"b":3,"a":2}"#,
        "duplicate keys keep the first position and the last value"
    );
}

#[test]
fn equality_ignores_key_order_and_signed_zero() {
    assert_eq!(parse(r#"{"a":1,"b":[0]}"#), parse(r#"{"b":[-0],"a":1}"#));
    assert_ne!(parse(r#"{"a":1}"#), parse(r#"{"a":1,"b":2}"#));
    assert_ne!(parse("[1,2]"), parse("[2,1]"));
}

#[test]
fn displays_like_json_stringify() {
    let value = parse(
        r#"{"s":"q\"\\\b\f\n\r\t\u0001\u001fé😀\u2028","n":[-0,1e21,1e-7,0.000001,1.5,-2e-308]}"#,
    );
    assert_eq!(
        value.to_string(),
        "{\"s\":\"q\\\"\\\\\\b\\f\\n\\r\\t\\u0001\\u001fé😀\u{2028}\",\"n\":[0,1e+21,1e-7,0.000001,1.5,-2e-308]}"
    );
}

#[test]
fn round_trips_js_number_formatting() {
    // `JSON.stringify` of random finite doubles, extremes, and edge cases.
    let corpus = include_str!("fixtures/js_numbers.json");
    let value = parse(corpus);
    let expected: Vec<&str> = corpus.trim_matches(['[', ']']).split(',').collect();
    let items = value.as_array().expect("array");
    assert_eq!(items.len(), expected.len());
    for (item, text) in items.iter().zip(expected) {
        assert_eq!(item.to_string(), text);
    }
}

#[test]
fn converts_typed_records_and_serde_json_values() {
    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    #[serde(rename_all = "camelCase")]
    struct Record {
        input_tokens: u32,
        label: String,
        ratio: f64,
        tags: Vec<String>,
    }
    let record = Record {
        input_tokens: 3,
        label: "x".to_owned(),
        ratio: 0.5,
        tags: vec!["a".to_owned()],
    };
    let value = to_json(&record).expect("strict");
    assert_eq!(
        value.to_string(),
        r#"{"inputTokens":3,"label":"x","ratio":0.5,"tags":["a"]}"#
    );
    assert_eq!(from_json::<Record>(&value).expect("typed"), record);
    let serde_value = serde_json::Value::from(&value);
    assert_eq!(
        serde_json::to_string(&serde_value).expect("json"),
        value.to_string()
    );
    assert_eq!(JsonValue::from(serde_value), value);
    assert_eq!(
        serde_json::to_string(&value).expect("json"),
        value.to_string()
    );
    assert_eq!(
        serde_json::from_str::<JsonValue>(&value.to_string()).expect("json"),
        value
    );
}

#[test]
fn accessors_are_exact() {
    let value = parse(r#"{"n":3,"f":1.5,"big":9007199254740992,"neg":-4,"s":"x","a":[true]}"#);
    assert_eq!(value["n"].as_u64(), Some(3));
    assert_eq!(value["f"].as_u64(), None);
    assert_eq!(value["f"].as_f64(), Some(1.5));
    assert_eq!(value["neg"].as_u64(), None);
    assert_eq!(value["neg"].as_i64(), Some(-4));
    assert_eq!(value["big"].as_u64(), Some(9_007_199_254_740_992));
    assert_eq!(value["s"].as_str(), Some("x"));
    assert_eq!(value["a"][0].as_bool(), Some(true));
    assert!(value["missing"].is_null());
    assert!(value["a"][5].is_null());
}

#[test]
fn copy_on_write_never_affects_other_holders() {
    let original = parse(r#"{"rows":[1,2]}"#);
    let mut edited = original.clone();
    edited
        .as_object_mut()
        .expect("object")
        .get_mut("rows")
        .and_then(JsonValue::as_array_mut)
        .expect("rows")
        .push(JsonValue::from(3));
    assert_eq!(original.to_string(), r#"{"rows":[1,2]}"#);
    assert_eq!(edited.to_string(), r#"{"rows":[1,2,3]}"#);
    let shared = JsonValue::Array(Arc::new(vec![JsonValue::from(1)]));
    assert!(shared.clone().strict_equals(&shared));
}

#[test]
fn utf16_helpers_count_code_units() {
    assert_eq!(utf16_len("a😀"), 3);
    assert_eq!(utf16_skip("a😀b", 3), "b");
}
