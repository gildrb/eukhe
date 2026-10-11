//! Port of `test/validation.test.ts`.

use eukhe_types::pi_ai::{JsonValue, Tool, ToolCall, ToolSchema};
use serde_json::json;

use super::compile::Validator;
use super::engine::{Engine, Mode};
use super::js_value::JsValue;
use super::regexp::RegExpCache;
use super::{validate_tool_arguments, validate_tool_call, ValidationError};
use crate::typebox::Type;

fn tool(parameters: impl Into<ToolSchema>) -> Tool {
    Tool {
        name: "echo".to_owned(),
        description: "Echo tool".to_owned(),
        parameters: parameters.into(),
        constrained_sampling: None,
    }
}

fn tool_call(arguments: JsonValue) -> ToolCall {
    let JsonValue::Object(arguments) = arguments else {
        panic!("tool call arguments are an object");
    };
    ToolCall {
        id: "tool-1".to_owned(),
        name: "echo".to_owned(),
        arguments,
        ..ToolCall::default()
    }
}

/// `createToolCallWithPlainSchema(schema, value)`.
fn create_tool_call_with_plain_schema(schema: JsonValue, value: JsonValue) -> (Tool, ToolCall) {
    let mut parameters = json!({ "type": "object", "properties": {}, "required": ["value"] });
    parameters["properties"]["value"] = schema;
    let mut arguments = json!({});
    arguments["value"] = value;
    (tool(parameters), tool_call(arguments))
}

/// JS-only: the TS replaces `globalThis.Function` to force `TypeBox`'s
/// interpreted fallback. Rust has no code generation; the observable
/// equivalent is that the `Type.Object` schema converts and passes under both
/// evaluators the port carries (compiled and interpreted).
#[test]
fn still_validates_when_function_constructor_is_unavailable() {
    let parameters = Type::object([("count", Type::number())]);
    let schema = JsValue::from_json(parameters.typebox());
    let tool = tool(parameters);
    let call = tool_call(json!({ "count": "42" }));

    assert_eq!(
        validate_tool_arguments(&tool, &call),
        Ok(json!({ "count": 42 }))
    );

    let value = JsValue::from_json(&json!({ "count": 42 }));
    let regexps = RegExpCache::default();
    let mut interpreted = Engine::new(&schema, &regexps, Mode::Interpreted);
    assert_eq!(
        interpreted.check_schema(&mut super::context::CheckContext::new(), &schema, &value),
        Ok(true)
    );
}

#[test]
fn coerces_serialized_plain_json_schemas_with_ajv_compatible_primitive_rules() {
    let passing_cases = [
        (json!({ "type": "number" }), json!("42"), json!(42)),
        (json!({ "type": "number" }), json!(true), json!(1)),
        (json!({ "type": "number" }), json!(null), json!(0)),
        (json!({ "type": "integer" }), json!("42"), json!(42)),
        (json!({ "type": "boolean" }), json!("true"), json!(true)),
        (json!({ "type": "boolean" }), json!("false"), json!(false)),
        (json!({ "type": "boolean" }), json!(1), json!(true)),
        (json!({ "type": "boolean" }), json!(0), json!(false)),
        (json!({ "type": "string" }), json!(null), json!("")),
        (json!({ "type": "string" }), json!(true), json!("true")),
        (json!({ "type": "null" }), json!(""), json!(null)),
        (json!({ "type": "null" }), json!(0), json!(null)),
        (json!({ "type": "null" }), json!(false), json!(null)),
        (
            json!({ "type": ["number", "string"] }),
            json!("1"),
            json!("1"),
        ),
        (
            json!({ "type": ["boolean", "number"] }),
            json!("1"),
            json!(1),
        ),
    ];

    for (schema, input, expected) in passing_cases {
        let (tool, call) = create_tool_call_with_plain_schema(schema, input);
        assert_eq!(
            validate_tool_arguments(&tool, &call),
            Ok(json!({ "value": expected }))
        );
    }
}

#[test]
fn treats_null_as_omission_for_optional_non_nullable_properties() {
    let tool = tool(Type::object([
        ("path", Type::string()),
        ("offset", Type::optional(Type::number())),
        (
            "nullable",
            Type::optional(Type::union([Type::string(), Type::null()])),
        ),
        (
            "metadata",
            Type::object([("enabled", Type::optional(Type::boolean()))]),
        ),
    ]));
    let call = tool_call(
        json!({ "path": "file.txt", "offset": null, "nullable": null, "metadata": { "enabled": null } }),
    );

    assert_eq!(
        validate_tool_arguments(&tool, &call),
        Ok(json!({ "path": "file.txt", "nullable": null, "metadata": {} }))
    );
}

#[test]
fn preserves_optional_nulls_whose_referenced_schema_is_nullable() {
    let tool = tool(json!({
        "type": "object",
        "properties": { "value": { "$ref": "#/$defs/value" } },
        "$defs": { "value": { "anyOf": [{ "type": "number" }, { "type": "null" }] } }
    }));
    let call = tool_call(json!({ "value": null }));

    assert_eq!(
        validate_tool_arguments(&tool, &call),
        Ok(json!({ "value": null }))
    );
}

#[test]
fn preserves_a_value_that_already_matches_a_nullable_union_arm() {
    let tool = tool(Type::object([(
        "value",
        Type::union([Type::number(), Type::null()]),
    )]));
    let call = tool_call(json!({ "value": null }));

    assert_eq!(
        validate_tool_arguments(&tool, &call),
        Ok(json!({ "value": null }))
    );
}

#[test]
fn preserves_a_value_that_already_matches_a_one_of_nullable_union_arm() {
    let (tool, call) = create_tool_call_with_plain_schema(
        json!({ "oneOf": [{ "type": "number" }, { "type": "null" }] }),
        json!(null),
    );

    assert_eq!(
        validate_tool_arguments(&tool, &call),
        Ok(json!({ "value": null }))
    );
}

#[test]
fn still_coerces_nullable_unions_when_the_original_value_does_not_match_any_arm() {
    let (tool, call) = create_tool_call_with_plain_schema(
        json!({ "anyOf": [{ "type": "number" }, { "type": "null" }] }),
        json!("42"),
    );

    assert_eq!(
        validate_tool_arguments(&tool, &call),
        Ok(json!({ "value": 42 }))
    );
}

/// The TS also runs `TypeBox`'s generated code (`new Function(Compile(..).Code())`)
/// because its CSP test pins the interpreted fallback; the Rust equivalent
/// checks the compiled validator directly.
#[test]
fn accepts_null_for_nullable_array_schemas_with_items() {
    let (tool, call) = create_tool_call_with_plain_schema(
        json!({ "type": ["array", "null"], "items": { "type": "string" } }),
        json!(null),
    );
    let schema = JsValue::from_json(&tool.parameters);
    let validator = Validator::compile(&schema).expect("compiles");

    assert_eq!(
        validator.check(&JsValue::from_json(&JsonValue::Object(
            call.arguments.clone()
        ))),
        Ok(true)
    );
    assert_eq!(
        validate_tool_arguments(&tool, &call),
        Ok(json!({ "value": null }))
    );
}

#[test]
fn rejects_invalid_coercions_for_serialized_plain_json_schemas() {
    let failing_cases = [
        (json!({ "type": "boolean" }), json!("1")),
        (json!({ "type": "boolean" }), json!("0")),
        (json!({ "type": "null" }), json!("null")),
        (json!({ "type": "integer" }), json!("42.1")),
    ];

    for (schema, input) in failing_cases {
        let (tool, call) = create_tool_call_with_plain_schema(schema, input);
        let error = validate_tool_arguments(&tool, &call).expect_err("validation fails");
        assert!(
            matches!(error, ValidationError::InvalidArguments { .. }),
            "{error:?}"
        );
        assert!(error.to_string().contains("Validation failed"), "{error}");
    }
}

#[test]
fn validate_tool_call_reports_unknown_tools() {
    let tools = [tool(json!({ "type": "object" }))];
    let mut call = tool_call(json!({}));
    assert_eq!(validate_tool_call(&tools, &call), Ok(json!({})));
    call.name = "missing".to_owned();
    let error = validate_tool_call(&tools, &call).expect_err("unknown tool");
    assert_eq!(
        error,
        ValidationError::ToolNotFound {
            name: "missing".to_owned()
        }
    );
    assert_eq!(error.to_string(), "Tool \"missing\" not found");
}

/// A `$ref` cycle that never consumes the value overflows V8's stack in the
/// TS; the port reports the same `RangeError` instead of crashing.
#[test]
fn self_referencing_ref_cycles_throw_range_error() {
    let tool = tool(json!({ "$ref": "#" }));
    let error = validate_tool_arguments(&tool, &tool_call(json!({}))).expect_err("cycle");
    assert_eq!(
        error,
        ValidationError::Thrown {
            kind: super::JsErrorKind::RangeError,
            message: "Maximum call stack size exceeded".to_owned()
        }
    );
}

/// `TypeBox` compiles `pattern` at build time, so an invalid pattern throws V8's
/// `SyntaxError` (`Invalid regular expression: /(/u: Unterminated group`); the
/// port keeps the class and prefix, with the regex engine's reason.
#[test]
fn invalid_patterns_throw_syntax_error() {
    let (tool, call) =
        create_tool_call_with_plain_schema(json!({ "type": "string", "pattern": "(" }), json!("x"));
    let error = validate_tool_arguments(&tool, &call).expect_err("invalid pattern");
    let ValidationError::Thrown { kind, message } = error else {
        panic!("expected a thrown SyntaxError, got {error:?}");
    };
    assert_eq!(kind, super::JsErrorKind::SyntaxError);
    assert!(
        message.starts_with("Invalid regular expression: /(/u: "),
        "{message}"
    );
}
