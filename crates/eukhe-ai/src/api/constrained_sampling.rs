//! Port of `api/constrained-sampling.ts`: strict JSON-schema conversion and
//! grammar constrained-sampling resolution for tool declarations.

use std::collections::HashSet;

use eukhe_types::pi_ai::{
    ConstrainedSamplingConfig, GrammarFormat, IndexMap, JsonObject, JsonSchemaStrictness,
    JsonValue, Tool, ToolConstrainedSampling,
};

use crate::utils::js::{js_trim, json_stringify};

/// Errors of constrained-sampling resolution. Both variants display the TS
/// message verbatim.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ConstrainedSamplingError {
    /// TS `UnsupportedStrictJsonSchemaError`: the schema is outside the
    /// strict subset.
    #[error("{0}")]
    UnsupportedStrictJsonSchema(String),
    /// A plain TS `Error`.
    #[error("{0}")]
    Invalid(String),
}

impl From<ConstrainedSamplingError> for crate::utils::diagnostics::Thrown {
    fn from(error: ConstrainedSamplingError) -> Self {
        std::sync::Arc::new(error)
    }
}

/// Returns true when a provider's strict mode rejects this schema keyword with this value.
pub type UnsupportedStrictSchemaKeywordCheck<'a> = &'a dyn Fn(&str, &JsonValue) -> bool;

const UNSUPPORTED_STRICT_SCHEMA_KEYS: [&str; 16] = [
    "$ref",
    "$defs",
    "definitions",
    "allOf",
    "oneOf",
    "patternProperties",
    "dependentSchemas",
    "dependencies",
    "unevaluatedProperties",
    "propertyNames",
    "contains",
    "prefixItems",
    "not",
    "if",
    "then",
    "else",
];

fn unsupported(message: impl Into<String>) -> ConstrainedSamplingError {
    ConstrainedSamplingError::UnsupportedStrictJsonSchema(message.into())
}

fn is_structured_schema(schema: &JsonValue) -> bool {
    let Some(schema) = schema.as_object() else {
        return false;
    };
    let has_type = |name: &str| match schema.get("type") {
        Some(JsonValue::String(kind)) => kind == name,
        Some(JsonValue::Array(kinds)) => kinds.iter().any(|kind| kind.as_str() == Some(name)),
        _ => false,
    };
    has_type("object")
        || has_type("array")
        || schema.contains_key("properties")
        || schema.contains_key("items")
}

fn schema_allows_null(schema: &JsonValue) -> bool {
    let Some(schema) = schema.as_object() else {
        return false;
    };
    match schema.get("type") {
        Some(JsonValue::String(kind)) if kind == "null" => return true,
        Some(JsonValue::Array(kinds)) if kinds.iter().any(|kind| kind.as_str() == Some("null")) => {
            return true
        }
        _ => {}
    }
    if matches!(schema.get("const"), Some(JsonValue::Null)) {
        return true;
    }
    if let Some(JsonValue::Array(values)) = schema.get("enum") {
        if values.iter().any(JsonValue::is_null) {
            return true;
        }
    }
    matches!(schema.get("anyOf"), Some(JsonValue::Array(variants)) if variants.iter().any(schema_allows_null))
}

fn make_json_schema_node_strict(
    schema: &mut JsonValue,
    is_unsupported_keyword: Option<UnsupportedStrictSchemaKeywordCheck<'_>>,
) -> Result<(), ConstrainedSamplingError> {
    let Some(object) = schema.as_object_mut() else {
        return Err(unsupported("boolean schemas are unsupported"));
    };
    for key in UNSUPPORTED_STRICT_SCHEMA_KEYS {
        if object.contains_key(key) {
            return Err(unsupported(format!("{key} schemas are unsupported")));
        }
    }
    if let Some(check) = is_unsupported_keyword {
        for (key, value) in object.iter() {
            if check(key, value) {
                return Err(unsupported(format!(
                    "{key}: {} is unsupported",
                    json_stringify(value)
                )));
            }
        }
    }

    if let Some(any_of) = object.get_mut("anyOf") {
        let variants = match any_of {
            JsonValue::Array(variants) if !variants.is_empty() => variants,
            _ => return Err(unsupported("anyOf must contain at least one schema")),
        };
        for variant in variants {
            if is_structured_schema(variant) {
                return Err(unsupported("object and array unions are unsupported"));
            }
            make_json_schema_node_strict(variant, is_unsupported_keyword)?;
        }
    }

    if let Some(items) = object.get_mut("items") {
        if items.is_array() {
            return Err(unsupported("tuple schemas are unsupported"));
        }
        make_json_schema_node_strict(items, is_unsupported_keyword)?;
    }

    let is_object_schema = object.get("type").and_then(JsonValue::as_str) == Some("object");
    if object.contains_key("properties") && !is_object_schema {
        return Err(unsupported("properties require type object"));
    }
    if !is_object_schema {
        return Ok(());
    }
    if object
        .get("additionalProperties")
        .is_some_and(|value| *value != JsonValue::Bool(false))
    {
        return Err(unsupported(
            "schema-valued or true additionalProperties is unsupported",
        ));
    }
    if object
        .get("properties")
        .is_some_and(|properties| !properties.is_object())
    {
        return Err(unsupported("object properties must be a schema map"));
    }
    let required: HashSet<String> = match object.get("required") {
        None => HashSet::new(),
        Some(JsonValue::Array(keys)) => {
            let mut set = HashSet::new();
            for key in keys {
                let JsonValue::String(key) = key else {
                    return Err(unsupported("object required must be a string array"));
                };
                set.insert(key.clone());
            }
            set
        }
        Some(_) => return Err(unsupported("object required must be a string array")),
    };

    let mut property_names = Vec::new();
    if let Some(JsonValue::Object(properties)) = object.get_mut("properties") {
        property_names.extend(properties.keys().cloned());
        if required.iter().any(|key| !properties.contains_key(key)) {
            return Err(unsupported("required contains an unknown property"));
        }
        for (key, property) in properties.iter_mut() {
            make_json_schema_node_strict(property, is_unsupported_keyword)?;
            if !required.contains(key) && !schema_allows_null(property) {
                let inner = property.take();
                *property = serde_json::json!({ "anyOf": [inner, { "type": "null" }] });
            }
        }
    } else if !required.is_empty() {
        return Err(unsupported("required contains an unknown property"));
    }
    object.insert(
        "required".to_owned(),
        JsonValue::Array(property_names.into_iter().map(JsonValue::String).collect()),
    );
    object.insert("additionalProperties".to_owned(), JsonValue::Bool(false));
    Ok(())
}

/// Convert a tool schema to the strict subset expected by provider constrained sampling.
///
/// # Errors
///
/// [`ConstrainedSamplingError::UnsupportedStrictJsonSchema`] when the schema
/// is outside the strict subset or rejected by `is_unsupported_keyword`.
pub fn make_strict_json_schema(
    schema: &JsonValue,
    is_unsupported_keyword: Option<UnsupportedStrictSchemaKeywordCheck<'_>>,
) -> Result<JsonObject, ConstrainedSamplingError> {
    let mut cloned = schema.clone();
    if !cloned.is_object() {
        return Err(unsupported("root schema must have type object"));
    }
    make_json_schema_node_strict(&mut cloned, is_unsupported_keyword)?;
    match cloned {
        JsonValue::Object(object)
            if object.get("type").and_then(JsonValue::as_str) == Some("object") =>
        {
            Ok(object)
        }
        _ => Err(unsupported("root schema must have type object")),
    }
}

/// Whether a JSON-schema tool is sent in strict mode (TS `strict: boolean | undefined`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrictToolParameters {
    /// `strict === true`: send the strict schema.
    Strict,
    /// Send the declared schema unchanged.
    AsDeclared,
}

/// The tool parameters to send: the strict schema when `strict` is
/// [`StrictToolParameters::Strict`], else the declared parameters.
///
/// # Errors
///
/// As [`make_strict_json_schema`].
pub fn get_json_schema_tool_parameters(
    tool: &Tool,
    strict: StrictToolParameters,
) -> Result<JsonValue, ConstrainedSamplingError> {
    match strict {
        StrictToolParameters::Strict => {
            make_strict_json_schema(&tool.parameters, None).map(JsonValue::Object)
        }
        StrictToolParameters::AsDeclared => Ok(tool.parameters.json().clone()),
    }
}

/// Grammar syntax of a resolved grammar tool (TS `"lark" | "regex"`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum GrammarSyntax {
    #[serde(rename = "lark")]
    Lark,
    #[serde(rename = "regex")]
    Regex,
}

/// TS `GrammarConstrainedSampling`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrammarConstrainedSampling {
    pub format: GrammarSyntax,
    pub definition: String,
    pub input_property: String,
}

/// TS `GrammarToolInputJsonBuffer`: streaming state of a grammar tool's
/// synthesized JSON arguments.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GrammarToolInputJsonBuffer {
    pub input: String,
    pub started: bool,
    pub closed: bool,
}

/// The raw grammar input string of a grammar tool call.
///
/// # Errors
///
/// When `arguments[input_property]` is not a string.
pub fn get_grammar_tool_input<'a>(
    tool_name: &str,
    arguments: &'a JsonObject,
    input_property: &str,
) -> Result<&'a str, ConstrainedSamplingError> {
    arguments
        .get(input_property)
        .and_then(JsonValue::as_str)
        .ok_or_else(|| {
            ConstrainedSamplingError::Invalid(format!(
                "Grammar tool call \"{tool_name}\" requires argument \"{input_property}\" to be a string."
            ))
        })
}

/// Whether [`append_grammar_tool_input_json_delta`] closes the JSON object.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GrammarInputClose {
    Close,
    KeepOpen,
}

/// Extend the synthesized `{"<property>":"<input>"}` JSON by the growth of
/// `next_input`; returns the JSON delta, `None` when nothing changed.
///
/// # Errors
///
/// When the input changed after closing or did not grow monotonically.
pub fn append_grammar_tool_input_json_delta(
    buffer: &mut GrammarToolInputJsonBuffer,
    input_property: &str,
    next_input: &str,
    close: GrammarInputClose,
) -> Result<Option<String>, ConstrainedSamplingError> {
    let close = close == GrammarInputClose::Close;
    if buffer.closed {
        if close && next_input == buffer.input {
            return Ok(None);
        }
        return Err(ConstrainedSamplingError::Invalid(format!(
            "grammar tool input for property \"{input_property}\" changed after it was closed"
        )));
    }
    let Some(input_delta) = next_input.strip_prefix(buffer.input.as_str()) else {
        return Err(ConstrainedSamplingError::Invalid(format!(
            "grammar tool input for property \"{input_property}\" changed non-monotonically"
        )));
    };
    if !close && input_delta.is_empty() {
        return Ok(None);
    }

    let mut delta = String::new();
    if !buffer.started {
        delta.push('{');
        delta.push_str(&json_stringify(&JsonValue::String(
            input_property.to_owned(),
        )));
        delta.push_str(":\"");
        buffer.started = true;
    }
    let quoted = json_stringify(&JsonValue::String(input_delta.to_owned()));
    delta.push_str(&quoted[1..quoted.len() - 1]);
    next_input.clone_into(&mut buffer.input);

    if close {
        delta.push_str("\"}");
        buffer.closed = true;
    }
    Ok(Some(delta))
}

/// JS truthiness of a JSON value.
fn is_truthy(value: &JsonValue) -> bool {
    match value {
        JsonValue::Null => false,
        JsonValue::Bool(flag) => *flag,
        JsonValue::Number(number) => number.as_f64().is_some_and(|n| n != 0.0 && !n.is_nan()),
        JsonValue::String(text) => !text.is_empty(),
        JsonValue::Array(_) | JsonValue::Object(_) => true,
    }
}

fn infer_grammar_input_property(tool: &Tool) -> Result<String, String> {
    let Some(schema) = tool
        .parameters
        .as_object()
        .filter(|schema| schema.get("type").and_then(JsonValue::as_str) == Some("object"))
    else {
        return Err("grammar constrained sampling requires an object parameter schema".to_owned());
    };
    let input_property =
        match schema.get("required") {
            Some(JsonValue::Array(required)) if required.len() == 1 => match &required[0] {
                JsonValue::String(name) => name.clone(),
                _ => return Err(
                    "grammar constrained sampling requires exactly one required string property"
                        .to_owned(),
                ),
            },
            _ => {
                return Err(
                    "grammar constrained sampling requires exactly one required string property"
                        .to_owned(),
                )
            }
        };
    let property = schema
        .get("properties")
        .and_then(JsonValue::as_object)
        .and_then(|properties| properties.get(&input_property))
        .filter(|property| is_truthy(property));
    let Some(property) = property else {
        return Err(format!(
            "grammar constrained sampling requires a properties entry for {input_property}"
        ));
    };
    if property.get("type").and_then(JsonValue::as_str) != Some("string") {
        return Err(format!(
            "grammar constrained sampling property {input_property} must have type string"
        ));
    }
    Ok(input_property)
}

fn json_schema_config(tool: &Tool) -> Option<JsonSchemaStrictness> {
    match &tool.constrained_sampling {
        Some(ToolConstrainedSampling::Config(ConstrainedSamplingConfig::JsonSchema { strict })) => {
            Some(*strict)
        }
        Some(
            ToolConstrainedSampling::Disabled
            | ToolConstrainedSampling::Config(ConstrainedSamplingConfig::Grammar { .. }),
        )
        | None => None,
    }
}

/// Decide whether a JSON-schema tool is sent in strict mode (`Some(true)`)
/// or not (`None`). `is_unsupported_keyword` lets a provider reject extra
/// keywords its strict mode does not accept, so "prefer" tools fall back to
/// non-strict.
///
/// # Errors
///
/// When the tool requires strict sampling that cannot be provided.
pub fn resolve_json_schema_strict_sampling(
    tool: &Tool,
    supports_strict_mode: bool,
    is_unsupported_keyword: Option<UnsupportedStrictSchemaKeywordCheck<'_>>,
) -> Result<Option<bool>, ConstrainedSamplingError> {
    let Some(strict) = json_schema_config(tool) else {
        return Ok(None);
    };
    if supports_strict_mode {
        return match make_strict_json_schema(&tool.parameters, is_unsupported_keyword) {
            Ok(_) => Ok(Some(true)),
            Err(ConstrainedSamplingError::UnsupportedStrictJsonSchema(message)) => match strict {
                JsonSchemaStrictness::Prefer => Ok(None),
                JsonSchemaStrictness::Require => Err(ConstrainedSamplingError::Invalid(format!(
                    "Tool \"{}\" requires JSON-schema constrained sampling, but {message}.",
                    tool.name
                ))),
            },
            Err(error @ ConstrainedSamplingError::Invalid(_)) => Err(error),
        };
    }
    match strict {
        JsonSchemaStrictness::Require => Err(ConstrainedSamplingError::Invalid(format!(
            "Tool \"{}\" requires JSON-schema constrained sampling, but strict tools are unsupported.",
            tool.name
        ))),
        JsonSchemaStrictness::Prefer => Ok(None),
    }
}

/// Resolve a grammar tool's `OpenAI` grammar (Lark preferred over regex).
///
/// # Errors
///
/// When no usable variant is given or the parameter schema is not a single
/// required string property.
pub fn resolve_grammar_constrained_sampling(
    tool: &Tool,
    supports_openai_grammar_tools: bool,
) -> Result<Option<GrammarConstrainedSampling>, ConstrainedSamplingError> {
    let variants = match &tool.constrained_sampling {
        Some(ToolConstrainedSampling::Config(ConstrainedSamplingConfig::Grammar { variants })) => {
            variants
        }
        Some(
            ToolConstrainedSampling::Disabled
            | ToolConstrainedSampling::Config(ConstrainedSamplingConfig::JsonSchema { .. }),
        )
        | None => return Ok(None),
    };
    if !supports_openai_grammar_tools {
        return Ok(None);
    }
    let usable = |format: GrammarFormat| {
        variants
            .get(&format)
            .filter(|definition| !js_trim(definition).is_empty())
    };
    let (format, definition) = match (
        usable(GrammarFormat::OpenAILark),
        usable(GrammarFormat::OpenAIRegex),
    ) {
        (Some(lark), _) => (GrammarSyntax::Lark, lark),
        (None, Some(regex)) => (GrammarSyntax::Regex, regex),
        (None, None) => {
            return Err(ConstrainedSamplingError::Invalid(format!(
                "Tool \"{}\" cannot use grammar constrained sampling: no supported grammar variant was provided.",
                tool.name
            )))
        }
    };
    let input_property = infer_grammar_input_property(tool).map_err(|message| {
        ConstrainedSamplingError::Invalid(format!(
            "Tool \"{}\" cannot use grammar constrained sampling: {message}.",
            tool.name
        ))
    })?;
    Ok(Some(GrammarConstrainedSampling {
        format,
        definition: definition.clone(),
        input_property,
    }))
}

/// Map of grammar tool name → input property.
///
/// # Errors
///
/// As [`resolve_grammar_constrained_sampling`].
pub fn create_grammar_tool_input_properties(
    tools: Option<&[Tool]>,
    supports_openai_grammar_tools: bool,
) -> Result<IndexMap<String, String>, ConstrainedSamplingError> {
    let mut properties = IndexMap::new();
    for tool in tools.unwrap_or_default() {
        if let Some(grammar) =
            resolve_grammar_constrained_sampling(tool, supports_openai_grammar_tools)?
        {
            properties.insert(tool.name.clone(), grammar.input_property);
        }
    }
    Ok(properties)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn tool(parameters: &JsonValue, strict: JsonSchemaStrictness) -> Tool {
        serde_json::from_value(json!({
            "name": "sample_tool",
            "description": "Sample tool",
            "parameters": parameters,
            "constrainedSampling": { "type": "json_schema", "strict": strict.as_str() },
        }))
        .expect("tool")
    }

    /// `TypeBox` schemas are written as the JSON `TypeBox` serializes.
    #[test]
    fn derives_strict_provider_schemas_without_changing_tool_definitions() {
        let parameters = json!({
            "type": "object",
            "properties": {
                "path": { "type": "string" },
                "offset": { "type": "number" },
                "metadata": {
                    "type": "object",
                    "properties": { "enabled": { "type": "boolean" } },
                },
                "nullable": { "anyOf": [{ "type": "string" }, { "type": "null" }] },
            },
            "required": ["path", "metadata"],
        });
        let original = parameters.clone();

        let strict = make_strict_json_schema(&parameters, None).expect("strict");

        assert_eq!(parameters, original);
        assert_eq!(
            JsonValue::Object(strict),
            json!({
                "type": "object",
                "properties": {
                    "path": { "type": "string" },
                    "offset": { "anyOf": [{ "type": "number" }, { "type": "null" }] },
                    "metadata": {
                        "type": "object",
                        "properties": { "enabled": { "anyOf": [{ "type": "boolean" }, { "type": "null" }] } },
                        "required": ["enabled"],
                        "additionalProperties": false,
                    },
                    "nullable": { "anyOf": [{ "type": "string" }, { "type": "null" }] },
                },
                "required": ["path", "offset", "metadata", "nullable"],
                "additionalProperties": false,
            })
        );
    }

    /// The `constrained-sampling.ts` assertions of this case; the
    /// `convertResponsesTools` assertions live with openai-responses-shared.
    #[test]
    fn falls_back_or_rejects_schemas_that_cannot_be_safely_converted() {
        let cases = [
            (
                json!({
                    "type": "object",
                    "properties": {
                        "metadata": { "type": "object", "properties": {}, "additionalProperties": { "type": "string" } },
                    },
                    "required": ["metadata"],
                }),
                "additionalProperties is unsupported",
            ),
            (
                json!({
                    "allOf": [
                        { "type": "object", "properties": { "a": { "type": "string" } }, "required": ["a"] },
                        { "type": "object", "properties": { "b": { "type": "number" } }, "required": ["b"] },
                    ],
                }),
                "allOf schemas are unsupported",
            ),
            (
                json!({
                    "type": "object",
                    "properties": {
                        "value": {
                            "anyOf": [
                                { "type": "object", "properties": { "nested": { "type": "string" } }, "required": ["nested"] },
                                { "type": "null" },
                            ],
                        },
                    },
                    "required": ["value"],
                }),
                "object and array unions are unsupported",
            ),
            (
                json!({
                    "type": "object",
                    "properties": { "child": { "$ref": "https://example.com/child.json" } },
                    "required": ["child"],
                }),
                "$ref schemas are unsupported",
            ),
        ];

        for (parameters, error) in cases {
            let message = make_strict_json_schema(&parameters, None)
                .expect_err("unsupported")
                .to_string();
            assert!(message.contains(error), "{message}");

            let prefer = tool(&parameters, JsonSchemaStrictness::Prefer);
            assert_eq!(
                resolve_json_schema_strict_sampling(&prefer, true, None),
                Ok(None)
            );

            let require = tool(&parameters, JsonSchemaStrictness::Require);
            let message = resolve_json_schema_strict_sampling(&require, true, None)
                .expect_err("required")
                .to_string();
            assert!(message.contains(error), "{message}");
        }
    }

    #[test]
    fn keeps_grammar_input_json_deltas_append_only() {
        let mut buffer = GrammarToolInputJsonBuffer::default();
        let first = append_grammar_tool_input_json_delta(
            &mut buffer,
            "payload",
            "a\"",
            GrammarInputClose::KeepOpen,
        )
        .expect("first")
        .expect("delta");
        let second = append_grammar_tool_input_json_delta(
            &mut buffer,
            "payload",
            "a\"\nb",
            GrammarInputClose::Close,
        )
        .expect("second")
        .expect("delta");

        assert_eq!(
            serde_json::from_str::<JsonValue>(&format!("{first}{second}")).expect("json"),
            json!({ "payload": "a\"\nb" })
        );
        assert_eq!(
            append_grammar_tool_input_json_delta(
                &mut buffer,
                "payload",
                "a\"\nb",
                GrammarInputClose::Close
            ),
            Ok(None)
        );
        assert_eq!(
            append_grammar_tool_input_json_delta(
                &mut buffer,
                "payload",
                "changed",
                GrammarInputClose::Close
            )
            .expect_err("closed")
            .to_string(),
            "grammar tool input for property \"payload\" changed after it was closed"
        );
    }
}
