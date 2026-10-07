//! `TypeBox`'s schema keyword guards (`schema/types/*`): each returns the
//! keyword's value only when it has the shape `TypeBox` accepts. Keywords live
//! on schema objects; arrays and functions (reachable as `$ref` targets) carry
//! none.

use std::borrow::Cow;

use super::js_value::{JsObject, JsValue};

/// `Schema.IsSchemaObject`.
pub(crate) fn is_schema_object(value: &JsValue) -> bool {
    matches!(value, JsValue::Object(_))
}

/// `Schema.IsSchema`: a schema object or a boolean schema.
pub(crate) fn is_schema(value: &JsValue) -> bool {
    matches!(value, JsValue::Object(_) | JsValue::Bool(_))
}

/// `schema.key` when `key in schema`.
pub(crate) fn get<'s>(schema: &'s JsValue, key: &str) -> Option<&'s JsValue> {
    match schema {
        JsValue::Object(object) => object.get_own(key),
        JsValue::Null
        | JsValue::Bool(_)
        | JsValue::Number(_)
        | JsValue::String(_)
        | JsValue::Array(_)
        | JsValue::Function(_) => None,
    }
}

fn string<'s>(schema: &'s JsValue, key: &str) -> Option<&'s str> {
    match get(schema, key) {
        Some(JsValue::String(text)) => Some(text),
        _ => None,
    }
}

/// A finite number (`Guard.IsNumber`).
fn number(schema: &JsValue, key: &str) -> Option<f64> {
    match get(schema, key) {
        Some(JsValue::Number(number)) if number.is_finite() => Some(*number),
        _ => None,
    }
}

fn schema_value<'s>(schema: &'s JsValue, key: &str) -> Option<&'s JsValue> {
    get(schema, key).filter(|value| is_schema(value))
}

fn schema_array<'s>(schema: &'s JsValue, key: &str) -> Option<&'s [JsValue]> {
    match get(schema, key) {
        Some(JsValue::Array(items)) if items.iter().all(is_schema) => Some(items),
        _ => None,
    }
}

/// An array whose elements are all strings.
fn string_array(value: &JsValue) -> Option<&[JsValue]> {
    match value {
        JsValue::Array(items) if items.iter().all(|item| matches!(item, JsValue::String(_))) => {
            Some(items)
        }
        _ => None,
    }
}

/// The strings of a [`string_array`].
pub(crate) fn strings(items: &[JsValue]) -> impl Iterator<Item = &str> {
    items.iter().filter_map(|item| match item {
        JsValue::String(text) => Some(text.as_str()),
        _ => None,
    })
}

/// A keyword whose value `Guard.IsObject` accepts: a plain object or an array
/// (whose entries are its indices).
#[derive(Clone, Copy)]
pub(crate) enum Members<'s> {
    Object(&'s JsObject),
    Array(&'s [JsValue]),
}

impl<'s> Members<'s> {
    fn of(value: &'s JsValue) -> Option<Self> {
        match value {
            JsValue::Object(object) => Some(Self::Object(object)),
            JsValue::Array(items) => Some(Self::Array(items)),
            JsValue::Null
            | JsValue::Bool(_)
            | JsValue::Number(_)
            | JsValue::String(_)
            | JsValue::Function(_) => None,
        }
    }

    /// `Object.entries(value)`.
    pub(crate) fn entries(self) -> Vec<(Cow<'s, str>, &'s JsValue)> {
        match self {
            Self::Object(object) => object
                .entries()
                .into_iter()
                .map(|(key, value)| (Cow::Borrowed(key), value))
                .collect(),
            Self::Array(items) => items
                .iter()
                .enumerate()
                .map(|(index, value)| (Cow::Owned(index.to_string()), value))
                .collect(),
        }
    }

    /// `Object.getOwnPropertyNames(value)` (arrays add `length`).
    pub(crate) fn keys(self) -> Vec<Cow<'s, str>> {
        let mut keys: Vec<Cow<'s, str>> = self.entries().into_iter().map(|(key, _)| key).collect();
        if matches!(self, Self::Array(_)) {
            keys.push(Cow::Borrowed("length"));
        }
        keys
    }

    fn values(self) -> Vec<&'s JsValue> {
        self.entries().into_iter().map(|(_, value)| value).collect()
    }
}

fn members<'s>(
    schema: &'s JsValue,
    key: &str,
    valid: impl Fn(&JsValue) -> bool,
) -> Option<Members<'s>> {
    let members = Members::of(get(schema, key)?)?;
    members.values().into_iter().all(valid).then_some(members)
}

/// `type`: a string or an array of strings.
pub(crate) fn type_(schema: &JsValue) -> Option<&JsValue> {
    get(schema, "type")
        .filter(|value| matches!(value, JsValue::String(_)) || string_array(value).is_some())
}

/// `required`: an array of strings.
pub(crate) fn required(schema: &JsValue) -> Option<&[JsValue]> {
    get(schema, "required").and_then(string_array)
}

pub(crate) fn additional_properties(schema: &JsValue) -> Option<&JsValue> {
    schema_value(schema, "additionalProperties")
}

/// `dependencies`: each value a schema or an array of strings.
pub(crate) fn dependencies(schema: &JsValue) -> Option<Members<'_>> {
    members(schema, "dependencies", |value| {
        is_schema(value) || string_array(value).is_some()
    })
}

pub(crate) fn dependent_required(schema: &JsValue) -> Option<Members<'_>> {
    members(schema, "dependentRequired", |value| {
        string_array(value).is_some()
    })
}

pub(crate) fn dependent_schemas(schema: &JsValue) -> Option<Members<'_>> {
    members(schema, "dependentSchemas", is_schema)
}

pub(crate) fn pattern_properties(schema: &JsValue) -> Option<Members<'_>> {
    members(schema, "patternProperties", is_schema)
}

pub(crate) fn properties(schema: &JsValue) -> Option<Members<'_>> {
    members(schema, "properties", is_schema)
}

/// `propertyNames`: any object (arrays included) or boolean.
pub(crate) fn property_names(schema: &JsValue) -> Option<&JsValue> {
    get(schema, "propertyNames").filter(|value| value.is_object() || is_schema(value))
}

pub(crate) fn min_properties(schema: &JsValue) -> Option<f64> {
    number(schema, "minProperties")
}

pub(crate) fn max_properties(schema: &JsValue) -> Option<f64> {
    number(schema, "maxProperties")
}

pub(crate) fn additional_items(schema: &JsValue) -> Option<&JsValue> {
    schema_value(schema, "additionalItems")
}

pub(crate) fn contains(schema: &JsValue) -> Option<&JsValue> {
    schema_value(schema, "contains")
}

/// `items`: a schema (unsized) or an array of schemas (sized).
#[derive(Clone, Copy)]
pub(crate) enum Items<'s> {
    Unsized(&'s JsValue),
    Sized(&'s [JsValue]),
}

pub(crate) fn items(schema: &JsValue) -> Option<Items<'_>> {
    match get(schema, "items")? {
        value @ (JsValue::Object(_) | JsValue::Bool(_)) => Some(Items::Unsized(value)),
        JsValue::Array(items) if items.iter().all(is_schema) => Some(Items::Sized(items)),
        _ => None,
    }
}

pub(crate) fn max_contains(schema: &JsValue) -> Option<f64> {
    number(schema, "maxContains")
}

pub(crate) fn min_contains(schema: &JsValue) -> Option<f64> {
    number(schema, "minContains")
}

pub(crate) fn max_items(schema: &JsValue) -> Option<f64> {
    number(schema, "maxItems")
}

pub(crate) fn min_items(schema: &JsValue) -> Option<f64> {
    number(schema, "minItems")
}

pub(crate) fn prefix_items(schema: &JsValue) -> Option<&[JsValue]> {
    schema_array(schema, "prefixItems")
}

pub(crate) fn unique_items(schema: &JsValue) -> Option<bool> {
    match get(schema, "uniqueItems") {
        Some(JsValue::Bool(flag)) => Some(*flag),
        _ => None,
    }
}

pub(crate) fn max_length(schema: &JsValue) -> Option<f64> {
    number(schema, "maxLength")
}

pub(crate) fn min_length(schema: &JsValue) -> Option<f64> {
    number(schema, "minLength")
}

pub(crate) fn format(schema: &JsValue) -> Option<&str> {
    string(schema, "format")
}

pub(crate) fn pattern(schema: &JsValue) -> Option<&str> {
    string(schema, "pattern")
}

pub(crate) fn exclusive_maximum(schema: &JsValue) -> Option<f64> {
    number(schema, "exclusiveMaximum")
}

pub(crate) fn exclusive_minimum(schema: &JsValue) -> Option<f64> {
    number(schema, "exclusiveMinimum")
}

pub(crate) fn maximum(schema: &JsValue) -> Option<f64> {
    number(schema, "maximum")
}

pub(crate) fn minimum(schema: &JsValue) -> Option<f64> {
    number(schema, "minimum")
}

pub(crate) fn multiple_of(schema: &JsValue) -> Option<f64> {
    number(schema, "multipleOf")
}

pub(crate) fn ref_(schema: &JsValue) -> Option<&str> {
    string(schema, "$ref")
}

pub(crate) fn recursive_ref(schema: &JsValue) -> Option<&str> {
    string(schema, "$recursiveRef")
}

pub(crate) fn dynamic_ref(schema: &JsValue) -> Option<&str> {
    string(schema, "$dynamicRef")
}

/// `const` (any value, `null` included).
pub(crate) fn const_(schema: &JsValue) -> Option<&JsValue> {
    get(schema, "const")
}

pub(crate) fn enum_(schema: &JsValue) -> Option<&[JsValue]> {
    match get(schema, "enum") {
        Some(JsValue::Array(options)) => Some(options),
        _ => None,
    }
}

pub(crate) fn if_(schema: &JsValue) -> Option<&JsValue> {
    schema_value(schema, "if")
}

pub(crate) fn then(schema: &JsValue) -> Option<&JsValue> {
    schema_value(schema, "then")
}

pub(crate) fn else_(schema: &JsValue) -> Option<&JsValue> {
    schema_value(schema, "else")
}

pub(crate) fn not(schema: &JsValue) -> Option<&JsValue> {
    schema_value(schema, "not")
}

pub(crate) fn all_of(schema: &JsValue) -> Option<&[JsValue]> {
    schema_array(schema, "allOf")
}

pub(crate) fn any_of(schema: &JsValue) -> Option<&[JsValue]> {
    schema_array(schema, "anyOf")
}

pub(crate) fn one_of(schema: &JsValue) -> Option<&[JsValue]> {
    schema_array(schema, "oneOf")
}

pub(crate) fn unevaluated_items(schema: &JsValue) -> Option<&JsValue> {
    schema_value(schema, "unevaluatedItems")
}

pub(crate) fn unevaluated_properties(schema: &JsValue) -> Option<&JsValue> {
    schema_value(schema, "unevaluatedProperties")
}

/// `$id` on a schema object.
pub(crate) fn id(schema: &JsValue) -> Option<&str> {
    string(schema, "$id")
}

pub(crate) fn anchor(schema: &JsValue) -> Option<&str> {
    string(schema, "$anchor")
}

pub(crate) fn dynamic_anchor(schema: &JsValue) -> Option<&str> {
    string(schema, "$dynamicAnchor")
}

/// `$recursiveAnchor: true`.
pub(crate) fn is_recursive_anchor_true(schema: &JsValue) -> bool {
    matches!(get(schema, "$recursiveAnchor"), Some(JsValue::Bool(true)))
}
