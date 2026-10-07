//! Port of `src/utils/validation.ts`: tool-call argument validation against
//! the tool's JSON Schema, on a port of `TypeBox` 1.3.27's validator.
//!
//! The pipeline is the TS one: clone the arguments, drop `null`s that stand
//! for omitted optional properties, `Value.Convert`, coerce primitives along
//! the JSON Schema (AJV-compatible rules), then `Check`; on failure, `TypeBox`'s
//! `Errors` become the message.
//!
//! Tool parameters carry `TypeBox`'s non-enumerable markers when they were
//! built with [`crate::typebox::Type`] (`ToolSchema::typebox`). Validation
//! runs on that view: `Value.Convert` dispatches on its `~kind` markers, so
//! `TypeBox`-built schemas convert (`Type.Integer()` turns `"42"` into `42`)
//! while plain JSON schemas pass through it untouched, as in the TS. The
//! markers are inert for every other step. The `TYPEBOX_KIND`
//! (`Symbol.for("TypeBox.Kind")`) symbol of the TS check belongs to older
//! `TypeBox` versions and is never present, so the `coerceWithJsonSchema`
//! branch always runs.
//!
//! The TS caches compiled validators in a `WeakMap` keyed by schema identity;
//! here each call compiles the validators it needs once, keyed by the
//! sub-schema's address within the call's schema document.

mod check;
mod compile;
mod context;
mod convert;
mod engine;
mod errors;
mod format;
mod idna;
pub(crate) mod js_value;
mod keywords;
mod regexp;
mod resolve;
mod stack;

#[cfg(test)]
mod convert_tests;
#[cfg(test)]
mod differential_tests;
#[cfg(test)]
mod tests;

use std::borrow::Cow;
use std::collections::HashMap;
use std::rc::Rc;

use eukhe_types::pi_ai::{JsonValue, Tool, ToolCall};

use self::compile::Validator;
use self::context::SchemaError;
use self::convert::Converter;
pub use self::js_value::JsErrorKind;
use self::js_value::{strict_equals, string_to_number, JsError, JsObject, JsValue};
use crate::utils::js::{js_trim, json_stringify_pretty, number_to_js_string};

/// Errors of [`validate_tool_call`] / [`validate_tool_arguments`]; `Display`
/// is the TS `Error.message`.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ValidationError {
    /// No tool with the call's name.
    #[error("Tool \"{name}\" not found")]
    ToolNotFound { name: String },
    /// The arguments fail the schema: `Validation failed for tool ...` with
    /// one line per `TypeBox` error and the received arguments.
    #[error("{message}")]
    InvalidArguments { message: String },
    /// An exception the TS lets escape for a malformed schema (an invalid
    /// `pattern`, an unresolvable `$ref` URL, a `null` sub-schema, a
    /// self-referencing `$ref` cycle, ...).
    #[error("{message}")]
    Thrown { kind: JsErrorKind, message: String },
}

impl From<JsError> for ValidationError {
    fn from(error: JsError) -> Self {
        Self::Thrown {
            kind: error.kind,
            message: error.message,
        }
    }
}

/// Finds a tool by name and validates the tool call arguments against its
/// schema, returning the validated (and possibly coerced) arguments.
///
/// # Errors
///
/// [`ValidationError::ToolNotFound`] when no tool matches, otherwise the
/// errors of [`validate_tool_arguments`].
pub fn validate_tool_call(
    tools: &[Tool],
    tool_call: &ToolCall,
) -> Result<JsonValue, ValidationError> {
    let tool = tools
        .iter()
        .find(|tool| tool.name == tool_call.name)
        .ok_or_else(|| ValidationError::ToolNotFound {
            name: tool_call.name.clone(),
        })?;
    validate_tool_arguments(tool, tool_call)
}

/// Validates tool call arguments against the tool's schema, returning the
/// validated (and possibly coerced) arguments.
///
/// # Errors
///
/// [`ValidationError::InvalidArguments`] with the formatted `TypeBox` errors
/// when the arguments do not match, or [`ValidationError::Thrown`] for the
/// exceptions a malformed schema raises in the TS.
pub fn validate_tool_arguments(
    tool: &Tool,
    tool_call: &ToolCall,
) -> Result<JsonValue, ValidationError> {
    let source = tool.parameters.typebox().unwrap_or(tool.parameters.json());
    let schema = JsValue::from_json(source);
    let mut validators = Validators::default();
    let mut args = JsValue::Object(JsValue::object_from_json(&tool_call.arguments));
    normalize_optional_nulls(&mut args, &schema, &mut validators)?;
    Converter::default().convert(source, &mut args)?;
    let validator = validators.get(&schema).map_err(ValidationError::from)?;
    // `coerced` is always an object when `args` is, so the TS replaces the
    // contents of `args` with it.
    args = coerce_with_json_schema(args, &schema, &mut validators)?;
    if validator.check(&args)? {
        return Ok(args.to_json());
    }
    let errors = validator
        .errors(&args)?
        .iter()
        .map(|error| format!("  - {}: {}", format_validation_path(error), error.message))
        .collect::<Vec<_>>()
        .join("\n");
    let errors = if errors.is_empty() {
        "Unknown validation error".to_owned()
    } else {
        errors
    };
    let received = JsValue::Object(JsValue::object_from_json(&tool_call.arguments)).to_json();
    let message = format!(
        "Validation failed for tool \"{}\":\n{errors}\n\nReceived arguments:\n{}",
        tool_call.name,
        json_stringify_pretty(&received)
    );
    Err(ValidationError::InvalidArguments { message })
}

/// Compiled validators of one validation call, by sub-schema address.
#[derive(Default)]
struct Validators<'s> {
    compiled: HashMap<*const JsValue, Result<Rc<Validator<'s>>, JsError>>,
}

impl<'s> Validators<'s> {
    /// `getValidator(schema)`. The TS caches in a `WeakMap`, whose `set`
    /// throws for a primitive key, so a boolean schema compiles and then fails
    /// (other primitives already fail to compile).
    fn get(&mut self, schema: &'s JsValue) -> Result<Rc<Validator<'s>>, JsError> {
        self.compiled
            .entry(std::ptr::from_ref(schema))
            .or_insert_with(|| {
                let validator = Validator::compile(schema)?;
                if !schema.is_object() {
                    return Err(JsError::type_error("Invalid value used as weak map key"));
                }
                Ok(Rc::new(validator))
            })
            .clone()
    }

    /// `getSubSchemaValidator(schema)?.Check(value)`: `None` when the schema
    /// does not compile.
    fn check(&mut self, schema: &'s JsValue, value: &JsValue) -> Result<Option<bool>, JsError> {
        match self.get(schema) {
            Ok(validator) => validator.check(value).map(Some),
            Err(_) => Ok(None),
        }
    }
}

/// `typeof value === "object"` values' `Object.entries` (plain objects,
/// arrays, and strings, whose entries are their characters).
fn entries_of(value: &JsValue) -> Vec<(Cow<'_, str>, Cow<'_, JsValue>)> {
    match value {
        JsValue::Object(object) => object
            .entries()
            .into_iter()
            .map(|(key, value)| (Cow::Borrowed(key), Cow::Borrowed(value)))
            .collect(),
        JsValue::Array(items) => items
            .iter()
            .enumerate()
            .map(|(index, value)| (Cow::Owned(index.to_string()), Cow::Borrowed(value)))
            .collect(),
        JsValue::String(text) => text
            .chars()
            .enumerate()
            .map(|(index, c)| {
                (
                    Cow::Owned(index.to_string()),
                    Cow::Owned(JsValue::String(c.to_string())),
                )
            })
            .collect(),
        JsValue::Null | JsValue::Bool(_) | JsValue::Number(_) | JsValue::Function(_) => Vec::new(),
    }
}

/// `new Set(schema.required ?? [])` as the set of strings it can contain.
fn required_set(schema: &JsValue) -> Result<Vec<String>, JsError> {
    let not_iterable = |description: String| {
        JsError::type_error(format!(
            "{description} is not iterable (cannot read property Symbol(Symbol.iterator))"
        ))
    };
    match schema.get_keyword("required")? {
        None | Some(JsValue::Null) => Ok(Vec::new()),
        Some(JsValue::Array(items)) => Ok(items
            .iter()
            .filter_map(|item| match item {
                JsValue::String(text) => Some(text.clone()),
                _ => None,
            })
            .collect()),
        Some(JsValue::String(text)) => Ok(text.chars().map(String::from).collect()),
        Some(JsValue::Number(number)) => Err(not_iterable(format!(
            "number {}",
            number_to_js_string(*number)
        ))),
        Some(JsValue::Bool(flag)) => Err(not_iterable(format!("boolean {flag}"))),
        Some(JsValue::Object(_) | JsValue::Function(_)) => Err(not_iterable("object".to_owned())),
    }
}

/// Removes `null`s standing for omitted optional properties: a non-required
/// property is dropped when its schema rejects `null`. `$ref` property
/// schemas are kept, since a sub-schema validator cannot resolve them.
fn normalize_optional_nulls<'s>(
    value: &mut JsValue,
    schema: &'s JsValue,
    validators: &mut Validators<'s>,
) -> Result<(), JsError> {
    if let JsValue::Array(items) = value {
        match schema.get_keyword("items")? {
            Some(JsValue::Array(item_schemas)) => {
                for (item, item_schema) in items.iter_mut().zip(item_schemas) {
                    if item_schema.is_truthy() {
                        normalize_optional_nulls(item, item_schema, validators)?;
                    }
                }
            }
            Some(item_schema) if item_schema.is_truthy() => {
                for item in items {
                    normalize_optional_nulls(item, item_schema, validators)?;
                }
            }
            Some(_) | None => {}
        }
        return Ok(());
    }
    let JsValue::Object(object) = value else {
        return Ok(());
    };
    let Some(properties) = schema
        .get_keyword("properties")?
        .filter(|properties| properties.is_truthy())
    else {
        return Ok(());
    };
    let required = required_set(schema)?;
    for (key, property_schema) in entries_of(properties) {
        let Cow::Borrowed(property_schema) = property_schema else {
            // A string's characters are not schemas: `propertySchema.$ref` is
            // undefined and compiling them throws, so nothing is deleted, and
            // recursing into a character schema is a no-op.
            continue;
        };
        if !object.has_in(&key) {
            continue;
        }
        let Some(property_value) = object.get_own(&key) else {
            // Inherited members are functions, never `null`, and recursing
            // into a function is a no-op.
            continue;
        };
        let removable = matches!(property_value, JsValue::Null)
            && !required.iter().any(|name| *name == key)
            && !matches!(
                property_schema.get_keyword("$ref")?,
                Some(JsValue::String(_))
            )
            && validators.check(property_schema, &JsValue::Null)? == Some(false);
        if removable {
            object.remove(&key);
        } else if let Some(property_value) = object.get_own_mut(&key) {
            normalize_optional_nulls(property_value, property_schema, validators)?;
        }
    }
    Ok(())
}

/// `getSchemaTypes(schema)`.
fn schema_types(schema: &JsValue) -> Result<Vec<&str>, JsError> {
    Ok(match schema.get_keyword("type")? {
        Some(JsValue::String(name)) => vec![name.as_str()],
        Some(JsValue::Array(names)) => names
            .iter()
            .filter_map(|name| match name {
                JsValue::String(name) => Some(name.as_str()),
                _ => None,
            })
            .collect(),
        Some(_) | None => Vec::new(),
    })
}

/// `matchesJsonType(value, type)`.
fn matches_json_type(value: &JsValue, type_: &str) -> bool {
    match type_ {
        "number" => matches!(value, JsValue::Number(_)),
        "integer" => matches!(value, JsValue::Number(number) if js_value::is_integer(*number)),
        "boolean" => matches!(value, JsValue::Bool(_)),
        "string" => matches!(value, JsValue::String(_)),
        "null" => matches!(value, JsValue::Null),
        "array" => matches!(value, JsValue::Array(_)),
        "object" => matches!(value, JsValue::Object(_)),
        _ => false,
    }
}

/// `coercePrimitiveByType(value, type)`: `Some` with the coerced value when it
/// differs from `value`, `None` when the TS returns `value` itself.
fn coerce_primitive_by_type(value: &JsValue, type_: &str) -> Option<JsValue> {
    match (type_, value) {
        ("number" | "integer", JsValue::Null) => Some(JsValue::Number(0.0)),
        ("number" | "integer", JsValue::String(text)) if !js_trim(text).is_empty() => {
            let parsed = string_to_number(text);
            let accepted = if type_ == "number" {
                parsed.is_finite()
            } else {
                js_value::is_integer(parsed)
            };
            accepted.then_some(JsValue::Number(parsed))
        }
        ("number" | "integer", JsValue::Bool(flag)) => {
            Some(JsValue::Number(if *flag { 1.0 } else { 0.0 }))
        }
        ("boolean", JsValue::Null) => Some(JsValue::Bool(false)),
        ("boolean", JsValue::String(text)) => match text.as_str() {
            "true" => Some(JsValue::Bool(true)),
            "false" => Some(JsValue::Bool(false)),
            _ => None,
        },
        ("boolean", JsValue::Number(number)) if is_js_number(*number, 1.0) => {
            Some(JsValue::Bool(true))
        }
        ("boolean", JsValue::Number(number)) if is_js_number(*number, 0.0) => {
            Some(JsValue::Bool(false))
        }
        ("string", JsValue::Null) => Some(JsValue::String(String::new())),
        ("string", JsValue::Number(number)) => Some(JsValue::String(number_to_js_string(*number))),
        ("string", JsValue::Bool(flag)) => Some(JsValue::String(flag.to_string())),
        ("null", JsValue::Bool(false)) => Some(JsValue::Null),
        ("null", JsValue::String(text)) if text.is_empty() => Some(JsValue::Null),
        ("null", JsValue::Number(number)) if is_js_number(*number, 0.0) => Some(JsValue::Null),
        _ => None,
    }
}

/// `value === constant` for numbers (`-0 === 0`).
#[allow(clippy::float_cmp)] // JS strict equality on numbers is exact.
fn is_js_number(value: f64, constant: f64) -> bool {
    value == constant
}

/// `applySchemaObjectCoercion(value, schema)`.
fn apply_schema_object_coercion<'s>(
    object: &mut JsObject,
    schema: &'s JsValue,
    validators: &mut Validators<'s>,
) -> Result<(), JsError> {
    let properties = schema
        .get_keyword("properties")?
        .filter(|properties| properties.is_truthy());
    let defined_keys: Vec<String> = properties
        .map(entries_of)
        .unwrap_or_default()
        .into_iter()
        .map(|(key, _)| key.into_owned())
        .collect();
    if let Some(properties) = properties {
        for (key, property_schema) in entries_of(properties) {
            let Cow::Borrowed(property_schema) = property_schema else {
                // Characters of a string `properties` (see `entries_of`).
                continue;
            };
            if !object.has_in(&key) {
                continue;
            }
            // An inherited `__proto__` would be read and written through the
            // prototype accessor; plain JSON arguments never rely on it.
            let property_value = match object.take(&key) {
                Some(own) => own,
                None => match js_value::NativeFunction::inherited(&key) {
                    Some(function) => JsValue::Function(function),
                    None => continue,
                },
            };
            let coerced = coerce_with_json_schema(property_value, property_schema, validators)?;
            object.set(&key, coerced);
        }
    }
    if let Some(additional) = schema
        .get_keyword("additionalProperties")?
        .filter(|additional| additional.is_truthy() && additional.is_object())
    {
        let keys: Vec<String> = object.keys().into_iter().map(str::to_owned).collect();
        for key in keys {
            if defined_keys.contains(&key) {
                continue;
            }
            if let Some(property_value) = object.take(&key) {
                let coerced = coerce_with_json_schema(property_value, additional, validators)?;
                object.set(&key, coerced);
            }
        }
    }
    Ok(())
}

/// `applySchemaArrayCoercion(value, schema)`.
fn apply_schema_array_coercion<'s>(
    items: &mut [JsValue],
    schema: &'s JsValue,
    validators: &mut Validators<'s>,
) -> Result<(), JsError> {
    match schema.get_keyword("items")? {
        Some(JsValue::Array(item_schemas)) => {
            for (item, item_schema) in items.iter_mut().zip(item_schemas) {
                if !item_schema.is_truthy() {
                    continue;
                }
                let value = std::mem::replace(item, JsValue::Null);
                *item = coerce_with_json_schema(value, item_schema, validators)?;
            }
        }
        Some(item_schema @ JsValue::Object(_)) => {
            for item in items {
                let value = std::mem::replace(item, JsValue::Null);
                *item = coerce_with_json_schema(value, item_schema, validators)?;
            }
        }
        Some(_) | None => {}
    }
    Ok(())
}

/// `coerceWithUnionSchema(value, schemas)`: keep a value one arm accepts,
/// else the first arm's coercion that the arm accepts.
fn coerce_with_union_schema<'s>(
    value: JsValue,
    schemas: &'s [JsValue],
    validators: &mut Validators<'s>,
) -> Result<JsValue, JsError> {
    for schema in schemas {
        if validators.check(schema, &value)? == Some(true) {
            return Ok(value);
        }
    }
    for schema in schemas {
        let candidate = value.structured_clone()?;
        let coerced = coerce_with_json_schema(candidate, schema, validators)?;
        if validators.check(schema, &coerced)? == Some(true) {
            return Ok(coerced);
        }
    }
    Ok(value)
}

/// `coerceWithJsonSchema(value, schema)`: AJV-style primitive coercion along
/// `allOf`/`anyOf`/`oneOf`, `type`, object properties, and array items.
fn coerce_with_json_schema<'s>(
    value: JsValue,
    schema: &'s JsValue,
    validators: &mut Validators<'s>,
) -> Result<JsValue, JsError> {
    let mut next = value;
    if let Some(JsValue::Array(nested)) = schema.get_keyword("allOf")? {
        for nested in nested {
            next = coerce_with_json_schema(next, nested, validators)?;
        }
    }
    if let Some(JsValue::Array(schemas)) = schema.get_keyword("anyOf")? {
        next = coerce_with_union_schema(next, schemas, validators)?;
    }
    if let Some(JsValue::Array(schemas)) = schema.get_keyword("oneOf")? {
        next = coerce_with_union_schema(next, schemas, validators)?;
    }
    let types = schema_types(schema)?;
    let matches_union_member =
        types.len() > 1 && types.iter().any(|type_| matches_json_type(&next, type_));
    if !types.is_empty() && !matches_union_member {
        if let Some(candidate) = types
            .iter()
            .find_map(|type_| coerce_primitive_by_type(&next, type_))
        {
            debug_assert!(
                !strict_equals(&candidate, &next),
                "coercion always changes the value's type"
            );
            next = candidate;
        }
    }
    if types.contains(&"object") {
        if let JsValue::Object(object) = &mut next {
            apply_schema_object_coercion(object, schema, validators)?;
        }
    }
    if types.contains(&"array") {
        if let JsValue::Array(items) = &mut next {
            apply_schema_array_coercion(items, schema, validators)?;
        }
    }
    Ok(next)
}

/// `formatValidationPath(error)`: the instance path in dot notation, the
/// missing property appended for `required`, `root` when empty.
fn format_validation_path(error: &SchemaError) -> String {
    let path = error
        .instance_path
        .strip_prefix('/')
        .unwrap_or(&error.instance_path)
        .replace('/', ".");
    if error.keyword == "required" {
        if let Some(required) = error
            .required_properties
            .first()
            .filter(|required| !required.is_empty())
        {
            return if path.is_empty() {
                required.clone()
            } else {
                format!("{path}.{required}")
            };
        }
    }
    if path.is_empty() {
        "root".to_owned()
    } else {
        path
    }
}
