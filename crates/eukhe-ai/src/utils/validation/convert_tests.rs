//! `Value.Convert` on `TypeBox`-built tool schemas: `validateToolArguments`
//! outputs of pi-ai 1.0.4 on `TypeBox` 1.3.27 under Node 26 for the same
//! schemas built with `Type`, asserted verbatim.

use eukhe_types::pi_ai::{JsonObject, JsonValue, Tool, ToolCall};
use serde_json::json;

use super::{validate_tool_arguments, ValidationError};
use crate::typebox::{EnumValue, Options, TSchema, Type};
use crate::utils::typebox_helpers::string_enum;

enum Expected {
    Ok(&'static str),
    Invalid(&'static str),
}

fn object(value: JsonValue) -> JsonObject {
    match value {
        JsonValue::Object(map) => map,
        _ => JsonObject::new(),
    }
}

fn parse(text: &str) -> JsonValue {
    serde_json::from_str(text).unwrap_or_else(|error| panic!("invalid JSON {text}: {error}"))
}

#[test]
fn typebox_schemas_convert_like_node() {
    let cases: Vec<(&str, TSchema, &str, Expected)> = vec![
        ("number_from_string", Type::object([("count", Type::number())]), "{\"count\":\"42\"}", Expected::Ok("{\"count\":42}")),
        ("integer_from_string", Type::object([("n", Type::integer())]), "{\"n\":\"42\"}", Expected::Ok("{\"n\":42}")),
        ("integer_truncates", Type::object([("n", Type::integer())]), "{\"n\":\"42.7\"}", Expected::Ok("{\"n\":42}")),
        ("integer_from_bool", Type::object([("n", Type::integer())]), "{\"n\":true}", Expected::Ok("{\"n\":1}")),
        ("integer_bigint_literal", Type::object([("n", Type::integer())]), "{\"n\":\"12n\"}", Expected::Ok("{\"n\":12}")),
        ("integer_unconvertible", Type::object([("n", Type::integer())]), "{\"n\":\"abc\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - n: must be integer\n\nReceived arguments:\n{\n  \"n\": \"abc\"\n}")),
        ("boolean_variants", Type::object([("a", Type::boolean()), ("b", Type::boolean()), ("c", Type::boolean()), ("d", Type::boolean())]), "{\"a\":\"TRUE\",\"b\":\"0\",\"c\":1,\"d\":\"False\"}", Expected::Ok("{\"a\":true,\"b\":false,\"c\":true,\"d\":false}")),
        ("null_variants", Type::object([("a", Type::null()), ("b", Type::null()), ("c", Type::null())]), "{\"a\":\"null\",\"b\":\"UNDEFINED\",\"c\":false}", Expected::Ok("{\"a\":null,\"b\":null,\"c\":null}")),
        ("string_variants", Type::object([("a", Type::string()), ("b", Type::string()), ("c", Type::string())]), "{\"a\":5,\"b\":null,\"c\":false}", Expected::Ok("{\"a\":\"5\",\"b\":\"null\",\"c\":\"false\"}")),
        ("literal_conversions", Type::object([("a", Type::literal("x")), ("b", Type::literal(1)), ("c", Type::literal(true)), ("d", Type::literal(2))]), "{\"a\":\"x\",\"b\":\"1\",\"c\":\"true\",\"d\":\"3\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - d: must be equal to constant\n\nReceived arguments:\n{\n  \"a\": \"x\",\n  \"b\": \"1\",\n  \"c\": \"true\",\n  \"d\": \"3\"\n}")),
        ("union_number_boolean", Type::object([("v", Type::union([Type::number(), Type::boolean()]))]), "{\"v\":\"true\"}", Expected::Ok("{\"v\":1}")),
        ("union_literals", Type::object([("v", Type::union([Type::literal("a"), Type::literal(1)]))]), "{\"v\":\"1\"}", Expected::Ok("{\"v\":1}")),
        ("union_objects", Type::object([("v", Type::union([Type::object([("a", Type::number())]), Type::object([("b", Type::string())])]))]), "{\"v\":{\"a\":\"1\"}}", Expected::Ok("{\"v\":{\"a\":1}}")),
        ("array_items", Type::object([("v", Type::array(Type::integer()))]), "{\"v\":[\"1\",\"2.5\",\"x\"]}", Expected::Invalid("Validation failed for tool \"echo\":\n  - v.2: must be integer\n\nReceived arguments:\n{\n  \"v\": [\n    \"1\",\n    \"2.5\",\n    \"x\"\n  ]\n}")),
        ("array_wraps_scalar", Type::object([("v", Type::array(Type::number()))]), "{\"v\":\"5\"}", Expected::Ok("{\"v\":[5]}")),
        ("tuple_items", Type::object([("v", Type::tuple([Type::number(), Type::string()]))]), "{\"v\":[\"1\",2,\"extra\"]}", Expected::Invalid("Validation failed for tool \"echo\":\n  - v.2: schema is false\n\nReceived arguments:\n{\n  \"v\": [\n    \"1\",\n    2,\n    \"extra\"\n  ]\n}")),
        ("record_values", Type::object([("v", Type::record(Type::string(), Type::integer()))]), "{\"v\":{\"a\":\"1\",\"b\":\"2.9\"}}", Expected::Ok("{\"v\":{\"a\":1,\"b\":2}}")),
        ("record_number_keys", Type::object([("v", Type::record(Type::number(), Type::boolean()))]), "{\"v\":{\"1\":\"true\",\"x\":\"true\"}}", Expected::Ok("{\"v\":{\"1\":true,\"x\":\"true\"}}")),
        ("intersect_objects", Type::intersect([Type::object([("x", Type::number())]), Type::object([("y", Type::integer())])]), "{\"x\":\"1\",\"y\":\"2.5\"}", Expected::Ok("{\"x\":1,\"y\":2}")),
        ("intersect_overlap", Type::intersect([Type::object([("x", Type::number())]), Type::object([("x", Type::integer())])]), "{\"x\":\"2.5\"}", Expected::Ok("{\"x\":2}")),
        ("intersect_property", Type::object([("v", Type::intersect([Type::object([("a", Type::integer())]), Type::object([("b", Type::optional(Type::boolean()))])]))]), "{\"v\":{\"a\":\"3\",\"b\":\"true\"}}", Expected::Ok("{\"v\":{\"a\":3,\"b\":true}}")),
        ("enum_mixed", Type::object([("v", Type::enum_([EnumValue::from("a"), EnumValue::from(1)]))]), "{\"v\":\"1\"}", Expected::Ok("{\"v\":1}")),
        ("enum_strings_error", Type::object([("v", Type::enum_(["a", "b"]))]), "{\"v\":\"c\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - v: must be equal to one of the allowed values\n\nReceived arguments:\n{\n  \"v\": \"c\"\n}")),
        ("intersect_union_string", Type::intersect([Type::object([("x", Type::union([Type::string(), Type::number()]))]), Type::object([("x", Type::string())])]), "{\"x\":5}", Expected::Ok("{\"x\":\"5\"}")),
        ("intersect_number_integer_optional", Type::intersect([Type::object([("a", Type::optional(Type::number()))]), Type::object([("a", Type::optional(Type::integer()))])]), "{\"a\":\"2.5\"}", Expected::Ok("{\"a\":2}")),
        ("intersect_literal_string", Type::intersect([Type::object([("a", Type::literal("x"))]), Type::object([("a", Type::string())])]), "{\"a\":\"x\"}", Expected::Ok("{\"a\":\"x\"}")),
        ("intersect_disjoint_never", Type::intersect([Type::object([("a", Type::number())]), Type::object([("a", Type::string())])]), "{\"a\":\"1\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - a: must be number\n\nReceived arguments:\n{\n  \"a\": \"1\"\n}")),
        ("intersect_union_distribution", Type::intersect([Type::union([Type::object([("a", Type::number())]), Type::object([("b", Type::number())])]), Type::object([("c", Type::integer())])]), "{\"a\":\"1\",\"c\":\"2.5\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - c: must be integer\n\nReceived arguments:\n{\n  \"a\": \"1\",\n  \"c\": \"2.5\"\n}")),
        ("intersect_any", Type::intersect([Type::any(), Type::object([("a", Type::integer())])]), "{\"a\":\"2.5\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - a: must be integer\n\nReceived arguments:\n{\n  \"a\": \"2.5\"\n}")),
        ("intersect_unknown", Type::intersect([Type::unknown(), Type::object([("a", Type::integer())])]), "{\"a\":\"2.5\"}", Expected::Ok("{\"a\":2}")),
        ("intersect_tuple_object", Type::object([("v", Type::intersect([Type::tuple([Type::integer()]), Type::object([("x", Type::integer())])]))]), "{\"v\":{\"0\":\"1.5\",\"x\":\"2.5\"}}", Expected::Invalid("Validation failed for tool \"echo\":\n  - v: must be array\n\nReceived arguments:\n{\n  \"v\": {\n    \"0\": \"1.5\",\n    \"x\": \"2.5\"\n  }\n}")),
        ("intersect_arrays", Type::object([("v", Type::intersect([Type::array(Type::number()), Type::array(Type::integer())]))]), "{\"v\":[\"2.5\"]}", Expected::Ok("{\"v\":[2]}")),
        ("intersect_record", Type::object([("v", Type::intersect([Type::record(Type::string(), Type::integer())]))]), "{\"v\":{\"k\":\"3.5\"}}", Expected::Ok("{\"v\":{\"k\":3}}")),
        ("intersect_enum_literal", Type::object([("v", Type::intersect([Type::enum_(["a", "b"]), Type::literal("b")]))]), "{\"v\":\"b\"}", Expected::Ok("{\"v\":\"b\"}")),
        ("enum_duplicates", Type::object([("v", Type::enum_([1, 1, 2]))]), "{\"v\":\"2\"}", Expected::Ok("{\"v\":2}")),
        ("union_enum_literal", Type::object([("v", Type::union([Type::enum_([1, 2]), Type::literal("z")]))]), "{\"v\":\"2\"}", Expected::Ok("{\"v\":2}")),
        ("intersect_readonly_optional", Type::intersect([Type::object([("a", Type::readonly(Type::optional(Type::integer())))]), Type::object([("a", Type::readonly(Type::optional(Type::number())))])]), "{\"a\":\"7.9\"}", Expected::Ok("{\"a\":7}")),
        ("intersect_nested_objects", Type::intersect([Type::object([("m", Type::object([("a", Type::integer())]))]), Type::object([("m", Type::object([("b", Type::boolean())]))])]), "{\"m\":{\"a\":\"1\",\"b\":\"true\"}}", Expected::Ok("{\"m\":{\"a\":1,\"b\":true}}")),
        ("nested_objects", Type::object([("meta", Type::object([("n", Type::integer()), ("tags", Type::array(Type::string()))]))]), "{\"meta\":{\"n\":\"3\",\"tags\":[1,true]}}", Expected::Ok("{\"meta\":{\"n\":3,\"tags\":[\"1\",\"true\"]}}")),
        ("key_regex_quirk", Type::object([("a.b", Type::number())]), "{\"axb\":\"1\",\"a.b\":\"2\"}", Expected::Ok("{\"axb\":1,\"a.b\":2}")),
        ("additional_schema_option", Type::object_with([("a", Type::number())], Options::new().schema("additionalProperties", Type::integer())), "{\"a\":\"1\",\"b\":\"2.5\"}", Expected::Ok("{\"a\":1,\"b\":2}")),
        ("optional_null_removed", Type::object([("n", Type::optional(Type::integer())), ("s", Type::string())]), "{\"n\":null,\"s\":\"x\"}", Expected::Ok("{\"s\":\"x\"}")),
        ("readonly_property", Type::object([("r", Type::readonly(Type::integer()))]), "{\"r\":\"9\"}", Expected::Ok("{\"r\":9}")),
        ("unsafe_untouched", Type::object([("op", string_enum(&["add", "sub"], None, None))]), "{\"op\":\"mul\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - op: must be equal to one of the allowed values\n\nReceived arguments:\n{\n  \"op\": \"mul\"\n}")),
        ("unsafe_coerced_by_json_rules", Type::object([("n", Type::unsafe_(object(json!({ "type": "integer" }))))]), "{\"n\":\"42.1\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - n: must be integer\n\nReceived arguments:\n{\n  \"n\": \"42.1\"\n}")),
        ("any_unknown_untouched", Type::object([("a", Type::any()), ("u", Type::unknown())]), "{\"a\":\"1\",\"u\":\"2\"}", Expected::Ok("{\"a\":\"1\",\"u\":\"2\"}")),
        ("string_null_vs_coerce", Type::object([("s", Type::optional(Type::string()))]), "{\"s\":null}", Expected::Ok("{}")),
        ("union_array_or_null", Type::object([("v", Type::union([Type::array(Type::integer()), Type::null()]))]), "{\"v\":[\"1\"]}", Expected::Ok("{\"v\":[1]}")),
        ("literal_mismatch_error", Type::object([("v", Type::literal("on"))]), "{\"v\":\"off\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - v: must be equal to constant\n\nReceived arguments:\n{\n  \"v\": \"off\"\n}")),
        ("object_non_object_value", Type::object([("o", Type::object([("a", Type::integer())]))]), "{\"o\":\"5\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - o: must be object\n\nReceived arguments:\n{\n  \"o\": \"5\"\n}")),
        ("tool_like_schema", Type::object([("path", Type::string_with(Options::new().set("description", "File path"))), ("offset", Type::optional(Type::integer_with(Options::new().set("description", "Start line").set("minimum", 1)))), ("limit", Type::optional(Type::integer())), ("mode", Type::optional(Type::union([Type::literal("read"), Type::literal("write")])))]), "{\"path\":\"a.txt\",\"offset\":\"0\",\"limit\":\"10\",\"mode\":\"read\"}", Expected::Invalid("Validation failed for tool \"echo\":\n  - offset: must be >= 1\n\nReceived arguments:\n{\n  \"path\": \"a.txt\",\n  \"offset\": \"0\",\n  \"limit\": \"10\",\n  \"mode\": \"read\"\n}")),
    ];
    for (name, schema, args, expected) in cases {
        let tool = Tool {
            name: "echo".to_owned(),
            description: "Echo tool".to_owned(),
            parameters: schema.into(),
            constrained_sampling: None,
        };
        let call = ToolCall {
            id: "tool-1".to_owned(),
            name: "echo".to_owned(),
            arguments: object(parse(args)),
            ..ToolCall::default()
        };
        let actual = validate_tool_arguments(&tool, &call);
        let expected = match expected {
            Expected::Ok(value) => Ok(parse(value)),
            Expected::Invalid(message) => Err(ValidationError::InvalidArguments {
                message: message.to_owned(),
            }),
        };
        assert_eq!(
            actual
                .as_ref()
                .map(|value| serde_json::to_string(value).unwrap_or_default()),
            expected
                .as_ref()
                .map(|value| serde_json::to_string(value).unwrap_or_default()),
            "case {name}"
        );
    }
}

/// The same JSON as plain parameters (no `TypeBox` markers) skips
/// `Value.Convert`: `Type.Integer()` truncates `"42.7"`, `{ type: "integer" }`
/// rejects it.
#[test]
fn plain_json_parameters_do_not_convert() {
    let schema = Type::object([("n", Type::integer())]);
    let plain = Tool {
        name: "echo".to_owned(),
        description: "Echo tool".to_owned(),
        parameters: schema.json().clone().into(),
        constrained_sampling: None,
    };
    let kinded = Tool {
        parameters: schema.into(),
        ..plain.clone()
    };
    let call = ToolCall {
        id: "tool-1".to_owned(),
        name: "echo".to_owned(),
        arguments: object(json!({ "n": "42.7" })),
        ..ToolCall::default()
    };
    assert_eq!(
        validate_tool_arguments(&kinded, &call),
        Ok(json!({ "n": 42 }))
    );
    assert!(matches!(
        validate_tool_arguments(&plain, &call),
        Err(ValidationError::InvalidArguments { .. })
    ));
}
