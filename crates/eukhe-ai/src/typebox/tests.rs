//! Builder outputs against `TypeBox` 1.3.27 under Node 26: the serialized
//! schema (`JSON.stringify`) and every own property, hidden markers included,
//! in own-key order.

use serde_json::json;

use super::{EnumValue, Options, TSchema, Type};
use crate::utils::typebox_helpers::string_enum;
use eukhe_types::pi_ai::{JsonObject, JsonValue};

fn object(value: JsonValue) -> JsonObject {
    match value {
        JsonValue::Object(map) => map,
        _ => JsonObject::new(),
    }
}

fn opts(value: JsonValue) -> Options {
    Options::from(object(value))
}

#[test]
fn builders_match_typebox() {
    let cases: Vec<(&str, TSchema, &str, &str)> = vec![
        ("object_options", Type::object_with([("a", Type::string()), ("b", Type::optional(Type::number()))], opts(json!({ "description": "d", "additionalProperties": false }))), "{\"type\":\"object\",\"required\":[\"a\"],\"properties\":{\"a\":{\"type\":\"string\"},\"b\":{\"type\":\"number\"}},\"description\":\"d\",\"additionalProperties\":false}", "{\"type\":\"object\",\"required\":[\"a\"],\"properties\":{\"a\":{\"type\":\"string\",\"~kind\":\"String\"},\"b\":{\"type\":\"number\",\"~kind\":\"Number\",\"~optional\":true}},\"description\":\"d\",\"additionalProperties\":false,\"~kind\":\"Object\"}"),
        ("string_options", Type::string_with(opts(json!({ "minLength": 1, "description": "x", "default": "y" }))), "{\"type\":\"string\",\"minLength\":1,\"description\":\"x\",\"default\":\"y\"}", "{\"type\":\"string\",\"minLength\":1,\"description\":\"x\",\"default\":\"y\",\"~kind\":\"String\"}"),
        ("number_options", Type::number_with(opts(json!({ "minimum": 1 }))), "{\"type\":\"number\",\"minimum\":1}", "{\"type\":\"number\",\"minimum\":1,\"~kind\":\"Number\"}"),
        ("integer", Type::integer(), "{\"type\":\"integer\"}", "{\"type\":\"integer\",\"~kind\":\"Integer\"}"),
        ("boolean", Type::boolean(), "{\"type\":\"boolean\"}", "{\"type\":\"boolean\",\"~kind\":\"Boolean\"}"),
        ("null", Type::null(), "{\"type\":\"null\"}", "{\"type\":\"null\",\"~kind\":\"Null\"}"),
        ("literal_string", Type::literal("x"), "{\"type\":\"string\",\"const\":\"x\"}", "{\"type\":\"string\",\"const\":\"x\",\"~kind\":\"Literal\"}"),
        ("literal_number", Type::literal(1.5), "{\"type\":\"number\",\"const\":1.5}", "{\"type\":\"number\",\"const\":1.5,\"~kind\":\"Literal\"}"),
        ("literal_boolean", Type::literal(true), "{\"type\":\"boolean\",\"const\":true}", "{\"type\":\"boolean\",\"const\":true,\"~kind\":\"Literal\"}"),
        ("union_options", Type::union_with([Type::string(), Type::number()], opts(json!({ "description": "u" }))), "{\"anyOf\":[{\"type\":\"string\"},{\"type\":\"number\"}],\"description\":\"u\"}", "{\"anyOf\":[{\"type\":\"string\",\"~kind\":\"String\"},{\"type\":\"number\",\"~kind\":\"Number\"}],\"description\":\"u\",\"~kind\":\"Union\"}"),
        ("optional", Type::optional(Type::string()), "{\"type\":\"string\"}", "{\"type\":\"string\",\"~kind\":\"String\",\"~optional\":true}"),
        ("readonly", Type::readonly(Type::string()), "{\"type\":\"string\"}", "{\"type\":\"string\",\"~kind\":\"String\",\"~readonly\":true}"),
        ("readonly_optional", Type::readonly(Type::optional(Type::string())), "{\"type\":\"string\"}", "{\"type\":\"string\",\"~kind\":\"String\",\"~optional\":true,\"~readonly\":true}"),
        ("array_options", Type::array_with(Type::string(), opts(json!({ "minItems": 1 }))), "{\"type\":\"array\",\"items\":{\"type\":\"string\"},\"minItems\":1}", "{\"type\":\"array\",\"items\":{\"type\":\"string\",\"~kind\":\"String\"},\"minItems\":1,\"~kind\":\"Array\"}"),
        ("record_string", Type::record(Type::string(), Type::number()), "{\"type\":\"object\",\"patternProperties\":{\"^.*$\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"patternProperties\":{\"^.*$\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Record\"}"),
        ("record_number", Type::record(Type::number(), Type::number()), "{\"type\":\"object\",\"patternProperties\":{\"^-?(?:0|[1-9][0-9]*)(?:\\\\.[0-9]+)?$\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"patternProperties\":{\"^-?(?:0|[1-9][0-9]*)(?:\\\\.[0-9]+)?$\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Record\"}"),
        ("record_integer", Type::record(Type::integer(), Type::number()), "{\"type\":\"object\",\"patternProperties\":{\"^-?(?:0|[1-9][0-9]*)$\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"patternProperties\":{\"^-?(?:0|[1-9][0-9]*)$\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Record\"}"),
        ("record_literal_union", Type::record(Type::union([Type::literal("a"), Type::literal("b")]), Type::number()), "{\"type\":\"object\",\"required\":[\"a\",\"b\"],\"properties\":{\"a\":{\"type\":\"number\"},\"b\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"required\":[\"a\",\"b\"],\"properties\":{\"a\":{\"type\":\"number\",\"~kind\":\"Number\"},\"b\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Object\"}"),
        ("record_literal", Type::record(Type::literal("k"), Type::number()), "{\"type\":\"object\",\"required\":[\"k\"],\"properties\":{\"k\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"required\":[\"k\"],\"properties\":{\"k\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Object\"}"),
        ("record_boolean", Type::record(Type::boolean(), Type::number()), "{\"type\":\"object\",\"required\":[\"true\",\"false\"],\"properties\":{\"true\":{\"type\":\"number\"},\"false\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"required\":[\"true\",\"false\"],\"properties\":{\"true\":{\"type\":\"number\",\"~kind\":\"Number\"},\"false\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Object\"}"),
        ("record_pattern", Type::record(Type::string_with(opts(json!({ "pattern": "^x" }))), Type::number()), "{\"type\":\"object\",\"patternProperties\":{\"^x\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"patternProperties\":{\"^x\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Record\"}"),
        ("record_enum", Type::record(Type::enum_(["a", "b", "a"]), Type::number()), "{\"type\":\"object\",\"required\":[\"a\",\"b\"],\"properties\":{\"a\":{\"type\":\"number\"},\"b\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"required\":[\"a\",\"b\"],\"properties\":{\"a\":{\"type\":\"number\",\"~kind\":\"Number\"},\"b\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Object\"}"),
        ("record_any", Type::record(Type::any(), Type::number()), "{\"type\":\"object\",\"patternProperties\":{\"^.*$\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"patternProperties\":{\"^.*$\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Record\"}"),
        ("record_options", Type::record_with(Type::string(), Type::number(), opts(json!({ "description": "r" }))), "{\"type\":\"object\",\"patternProperties\":{\"^.*$\":{\"type\":\"number\"}},\"description\":\"r\"}", "{\"type\":\"object\",\"patternProperties\":{\"^.*$\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Record\",\"description\":\"r\"}"),
        ("record_mixed_union", Type::record(Type::union([Type::literal("a"), Type::string()]), Type::number()), "{\"type\":\"object\",\"patternProperties\":{\"^.*$\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"patternProperties\":{\"^.*$\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Record\"}"),
        ("record_intersect_key", Type::record(Type::intersect([Type::string(), Type::literal("k")]), Type::number()), "{\"type\":\"object\",\"required\":[\"k\"],\"properties\":{\"k\":{\"type\":\"number\"}}}", "{\"type\":\"object\",\"required\":[\"k\"],\"properties\":{\"k\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Object\"}"),
        ("tuple", Type::tuple([Type::string(), Type::number()]), "{\"type\":\"array\",\"additionalItems\":false,\"items\":[{\"type\":\"string\"},{\"type\":\"number\"}],\"minItems\":2}", "{\"type\":\"array\",\"additionalItems\":false,\"items\":[{\"type\":\"string\",\"~kind\":\"String\"},{\"type\":\"number\",\"~kind\":\"Number\"}],\"minItems\":2,\"~kind\":\"Tuple\"}"),
        ("intersect", Type::intersect([Type::object([("x", Type::number())]), Type::object([("y", Type::number())])]), "{\"allOf\":[{\"type\":\"object\",\"required\":[\"x\"],\"properties\":{\"x\":{\"type\":\"number\"}}},{\"type\":\"object\",\"required\":[\"y\"],\"properties\":{\"y\":{\"type\":\"number\"}}}]}", "{\"allOf\":[{\"type\":\"object\",\"required\":[\"x\"],\"properties\":{\"x\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Object\"},{\"type\":\"object\",\"required\":[\"y\"],\"properties\":{\"y\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"~kind\":\"Object\"}],\"~kind\":\"Intersect\"}"),
        ("enum_strings", Type::enum_(["a", "b"]), "{\"enum\":[\"a\",\"b\"]}", "{\"enum\":[\"a\",\"b\"],\"~kind\":\"Enum\"}"),
        ("enum_mixed", Type::enum_([EnumValue::from("a"), EnumValue::from(1)]), "{\"enum\":[\"a\",1]}", "{\"enum\":[\"a\",1],\"~kind\":\"Enum\"}"),
        ("unsafe", Type::unsafe_(object(json!({ "type": "string", "enum": ["a"] }))), "{\"type\":\"string\",\"enum\":[\"a\"]}", "{\"type\":\"string\",\"enum\":[\"a\"],\"~unsafe\":null}"),
        ("any", Type::any(), "{}", "{\"~kind\":\"Any\"}"),
        ("unknown", Type::unknown(), "{}", "{\"~kind\":\"Unknown\"}"),
        ("never", Type::never(), "{\"not\":{}}", "{\"not\":{},\"~kind\":\"Never\"}"),
        ("object_index_keys", Type::object([("b", Type::string()), ("1", Type::string()), ("a", Type::string())]), "{\"type\":\"object\",\"required\":[\"1\",\"b\",\"a\"],\"properties\":{\"1\":{\"type\":\"string\"},\"b\":{\"type\":\"string\"},\"a\":{\"type\":\"string\"}}}", "{\"type\":\"object\",\"required\":[\"1\",\"b\",\"a\"],\"properties\":{\"1\":{\"type\":\"string\",\"~kind\":\"String\"},\"b\":{\"type\":\"string\",\"~kind\":\"String\"},\"a\":{\"type\":\"string\",\"~kind\":\"String\"}},\"~kind\":\"Object\"}"),
        ("object_empty", Type::object(Vec::<(String, TSchema)>::new()), "{\"type\":\"object\",\"properties\":{}}", "{\"type\":\"object\",\"properties\":{},\"~kind\":\"Object\"}"),
        ("nested_option_order", Type::string_with(Options::new().set("default", json!({ "b": 1, "1": 2 }))), "{\"type\":\"string\",\"default\":{\"1\":2,\"b\":1}}", "{\"type\":\"string\",\"default\":{\"1\":2,\"b\":1},\"~kind\":\"String\"}"),
        ("object_additional_schema", Type::object_with([("a", Type::number())], Options::new().schema("additionalProperties", Type::integer())), "{\"type\":\"object\",\"required\":[\"a\"],\"properties\":{\"a\":{\"type\":\"number\"}},\"additionalProperties\":{\"type\":\"integer\"}}", "{\"type\":\"object\",\"required\":[\"a\"],\"properties\":{\"a\":{\"type\":\"number\",\"~kind\":\"Number\"}},\"additionalProperties\":{\"type\":\"integer\",\"~kind\":\"Integer\"},\"~kind\":\"Object\"}"),
        ("string_enum_helper", string_enum(&["add", "sub"], Some("op"), Some("add")), "{\"type\":\"string\",\"enum\":[\"add\",\"sub\"],\"description\":\"op\",\"default\":\"add\"}", "{\"type\":\"string\",\"enum\":[\"add\",\"sub\"],\"description\":\"op\",\"default\":\"add\",\"~unsafe\":null}"),
    ];
    for (name, schema, json, view) in cases {
        assert_eq!(
            serde_json::to_string(schema.json()).ok().as_deref(),
            Some(json),
            "json of {name}"
        );
        assert_eq!(
            serde_json::to_string(schema.typebox()).ok().as_deref(),
            Some(view),
            "view of {name}"
        );
    }
}

#[test]
fn partial_makes_every_object_property_optional() {
    let record = Type::record(
        Type::enum_(["short", "long"]),
        Type::number_with(Options::new().set("exclusiveMinimum", 0)),
    );
    assert_eq!(record.json()["required"], json!(["short", "long"]));
    let partial = Type::partial_with(record, Options::new().set("description", "tiers"));
    assert_eq!(
        partial.json(),
        &json!({
            "type": "object",
            "properties": {
                "short": { "type": "number", "exclusiveMinimum": 0 },
                "long": { "type": "number", "exclusiveMinimum": 0 }
            },
            "description": "tiers"
        })
    );
    assert_eq!(
        partial.typebox()["properties"]["short"]["~optional"],
        json!(true)
    );
}
