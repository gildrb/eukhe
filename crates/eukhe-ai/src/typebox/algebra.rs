//! `TypeBox`'s type algebra over schema views (JSON with the non-enumerable
//! markers inline): node construction (`system/memory`), `Evaluate`
//! (`type/engine/evaluate`), `Instantiate` (`type/engine/instantiate.mjs`),
//! and the structural `Extends` relation (`type/extends`) they rely on.
//!
//! Covers the kinds [`super::Type`] builds: `Any`, `Array`, `Boolean`,
//! `Enum`, `Integer`, `Intersect`, `Literal`, `Never`, `Null`, `Number`,
//! `Object`, `Record`, `String`, `Tuple`, `Union`, `Unknown`, and `Unsafe`
//! schemas. Kinds outside that set (generics, refs, template literals,
//! functions, ...) take `TypeBox`'s fall-through branches.

use eukhe_types::pi_ai::{JsonObject, JsonValue};

use crate::utils::js::{array_index_key, number_to_js_string};
use crate::utils::validation::js_value::{JsError, JsErrorKind};

/// The non-enumerable `TypeBox` markers (never serialized).
pub(crate) const HIDDEN_KEYS: [&str; 5] =
    ["~kind", "~optional", "~readonly", "~immutable", "~unsafe"];

/// `Guard.IsUnsafePropertyKey`.
fn is_unsafe_key(key: &str) -> bool {
    matches!(key, "__proto__" | "constructor" | "prototype")
}

/// A JS object literal's key order: array-index keys ascending, then the
/// rest in insertion order.
pub(crate) fn js_ordered(map: JsonObject) -> JsonObject {
    let mut indexed: Vec<(u32, String, JsonValue)> = Vec::new();
    let mut named: Vec<(String, JsonValue)> = Vec::new();
    for (key, value) in map {
        match array_index_key(&key) {
            Some(index) => indexed.push((index, key, value)),
            None => named.push((key, value)),
        }
    }
    indexed.sort_by_key(|(index, _, _)| *index);
    indexed
        .into_iter()
        .map(|(_, key, value)| (key, value))
        .chain(named)
        .collect()
}

// ------------------------------------------------------------------
// Guards
// ------------------------------------------------------------------

/// `Type.IsKind(value, kind)` reads `value['~kind']`.
pub(crate) fn kind(value: &JsonValue) -> Option<&str> {
    value.as_object()?.get("~kind")?.as_str()
}

pub(crate) fn is_kind(value: &JsonValue, expected: &str) -> bool {
    kind(value) == Some(expected)
}

fn has_key(value: &JsonValue, key: &str) -> bool {
    value
        .as_object()
        .is_some_and(|object| object.contains_key(key))
}

/// `IsOptional`: the `~optional` marker.
pub(crate) fn is_optional(value: &JsonValue) -> bool {
    has_key(value, "~optional")
}

fn is_readonly(value: &JsonValue) -> bool {
    has_key(value, "~readonly")
}

fn is_immutable(value: &JsonValue) -> bool {
    has_key(value, "~immutable")
}

/// `IsUnsafe`: `~unsafe: null` on a schema object.
fn is_unsafe(value: &JsonValue) -> bool {
    value
        .as_object()
        .is_some_and(|object| object.get("~unsafe") == Some(&JsonValue::Null))
}

fn field<'a>(value: &'a JsonValue, key: &str) -> Option<&'a JsonValue> {
    value.as_object()?.get(key)
}

fn array_field<'a>(value: &'a JsonValue, key: &str) -> &'a [JsonValue] {
    field(value, key)
        .and_then(JsonValue::as_array)
        .map_or(&[], Vec::as_slice)
}

/// `Guard.Keys(object)` entries of a properties-like map, in JS order.
fn entries(value: Option<&JsonValue>) -> Vec<(String, JsonValue)> {
    match value {
        Some(JsonValue::Object(map)) => js_ordered(map.clone()).into_iter().collect(),
        _ => Vec::new(),
    }
}

// ------------------------------------------------------------------
// Memory (node construction)
// ------------------------------------------------------------------

/// `Memory.Clone` of a schema value: unsafe keys are skipped at every level.
pub(crate) fn memory_clone(value: &JsonValue) -> JsonValue {
    match value {
        JsonValue::Array(items) => JsonValue::Array(items.iter().map(memory_clone).collect()),
        JsonValue::Object(map) => JsonValue::Object(
            map.iter()
                .filter(|(key, _)| !is_unsafe_key(key))
                .map(|(key, value)| (key.clone(), memory_clone(value)))
                .collect(),
        ),
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::String(_) => {
            value.clone()
        }
    }
}

/// Sets `key` in place, or appends it (`Object.defineProperty` / assignment).
fn define(map: &mut JsonObject, key: &str, value: JsonValue) {
    match map.get_mut(key) {
        Some(slot) => *slot = value,
        None => {
            map.insert(key.to_owned(), value);
        }
    }
}

/// `{ ...enumerable, ...options }` in JS key order.
pub(crate) fn merge_options(enumerable: JsonObject, options: &JsonObject) -> JsonObject {
    let mut merged = enumerable;
    for (key, value) in options {
        define(&mut merged, key, value.clone());
    }
    js_ordered(merged)
}

/// `Memory.Create({ '~kind': kind }, enumerable, options)` as a view.
pub(crate) fn create(kind: &str, enumerable: JsonObject, options: &JsonObject) -> JsonValue {
    let mut view = merge_options(enumerable, options);
    define(&mut view, "~kind", JsonValue::String(kind.to_owned()));
    JsonValue::Object(view)
}

/// `Memory.Update(type, hidden, enumerable)`.
pub(crate) fn update(
    value: &JsonValue,
    hidden: &[(&str, JsonValue)],
    enumerable: &JsonObject,
) -> JsonValue {
    let JsonValue::Object(mut map) = memory_clone(value) else {
        return memory_clone(value);
    };
    for (key, value) in hidden {
        define(&mut map, key, value.clone());
    }
    for (key, value) in enumerable {
        define(&mut map, key, value.clone());
    }
    JsonValue::Object(js_ordered(map))
}

/// `Memory.Discard(type, keys)`.
fn discard(value: &JsonValue, keys: &[&str]) -> JsonObject {
    match value {
        JsonValue::Object(map) => map
            .iter()
            .filter(|(key, _)| !keys.contains(&key.as_str()))
            .map(|(key, value)| (key.clone(), memory_clone(value)))
            .collect(),
        _ => JsonObject::new(),
    }
}

/// The enumerable options a `Discard` keeps (spreading drops hidden keys).
fn options_of(value: &JsonValue, keys: &[&str]) -> JsonObject {
    discard(value, keys)
        .into_iter()
        .filter(|(key, _)| !HIDDEN_KEYS.contains(&key.as_str()))
        .collect()
}

pub(crate) fn add_optional(value: &JsonValue) -> JsonValue {
    update(
        value,
        &[("~optional", JsonValue::Bool(true))],
        &JsonObject::new(),
    )
}

pub(crate) fn add_readonly(value: &JsonValue) -> JsonValue {
    update(
        value,
        &[("~readonly", JsonValue::Bool(true))],
        &JsonObject::new(),
    )
}

fn remove_marker(value: &JsonValue, marker: &str) -> JsonValue {
    JsonValue::Object(js_ordered(discard(value, &[marker])))
}

// ------------------------------------------------------------------
// Constructors
// ------------------------------------------------------------------

/// `Type.Literal(value)`: `Invalid Literal value` for non-literal values.
pub(crate) fn literal(value: &JsonValue) -> Result<JsonValue, JsError> {
    let type_name = match value {
        JsonValue::Bool(_) => "boolean",
        JsonValue::Number(_) => "number",
        JsonValue::String(_) => "string",
        JsonValue::Null | JsonValue::Array(_) | JsonValue::Object(_) => {
            return Err(JsError::new(JsErrorKind::Error, "Invalid Literal value"));
        }
    };
    let mut enumerable = JsonObject::new();
    enumerable.insert("type".to_owned(), JsonValue::String(type_name.to_owned()));
    enumerable.insert("const".to_owned(), value.clone());
    Ok(create("Literal", enumerable, &JsonObject::new()))
}

pub(crate) fn union(types: Vec<JsonValue>) -> JsonValue {
    let mut enumerable = JsonObject::new();
    enumerable.insert("anyOf".to_owned(), JsonValue::Array(types));
    create("Union", enumerable, &JsonObject::new())
}

pub(crate) fn never() -> JsonValue {
    let mut enumerable = JsonObject::new();
    enumerable.insert("not".to_owned(), JsonValue::Object(JsonObject::new()));
    create("Never", enumerable, &JsonObject::new())
}

fn unknown() -> JsonValue {
    create("Unknown", JsonObject::new(), &JsonObject::new())
}

/// `Type.Object(properties, options)`: `required` lists the non-optional keys.
pub(crate) fn object(properties: JsonObject, options: &JsonObject) -> JsonValue {
    let properties = js_ordered(properties);
    let required: Vec<JsonValue> = properties
        .iter()
        .filter(|(_, property)| !is_optional(property))
        .map(|(key, _)| JsonValue::String(key.clone()))
        .collect();
    let mut enumerable = JsonObject::new();
    enumerable.insert("type".to_owned(), JsonValue::String("object".to_owned()));
    if !required.is_empty() {
        enumerable.insert("required".to_owned(), JsonValue::Array(required));
    }
    enumerable.insert("properties".to_owned(), JsonValue::Object(properties));
    create("Object", enumerable, options)
}

fn array(items: JsonValue, options: &JsonObject) -> JsonValue {
    let mut enumerable = JsonObject::new();
    enumerable.insert("type".to_owned(), JsonValue::String("array".to_owned()));
    enumerable.insert("items".to_owned(), items);
    create("Array", enumerable, options)
}

pub(crate) fn tuple(items: Vec<JsonValue>, options: &JsonObject) -> JsonValue {
    let mut enumerable = JsonObject::new();
    enumerable.insert("type".to_owned(), JsonValue::String("array".to_owned()));
    enumerable.insert("additionalItems".to_owned(), JsonValue::Bool(false));
    let length = items.len();
    enumerable.insert("items".to_owned(), JsonValue::Array(items));
    enumerable.insert("minItems".to_owned(), JsonValue::from(length));
    create("Tuple", enumerable, options)
}

fn intersect(types: Vec<JsonValue>, options: &JsonObject) -> JsonValue {
    let mut enumerable = JsonObject::new();
    enumerable.insert("allOf".to_owned(), JsonValue::Array(types));
    create("Intersect", enumerable, options)
}

fn union_with(types: Vec<JsonValue>, options: &JsonObject) -> JsonValue {
    let mut enumerable = JsonObject::new();
    enumerable.insert("anyOf".to_owned(), JsonValue::Array(types));
    create("Union", enumerable, options)
}

/// `CreateRecord(pattern, value)`.
pub(crate) fn record(pattern: &str, value: JsonValue) -> JsonValue {
    let mut pattern_properties = JsonObject::new();
    pattern_properties.insert(pattern.to_owned(), value);
    let mut enumerable = JsonObject::new();
    enumerable.insert("type".to_owned(), JsonValue::String("object".to_owned()));
    enumerable.insert(
        "patternProperties".to_owned(),
        JsonValue::Object(pattern_properties),
    );
    create("Record", enumerable, &JsonObject::new())
}

/// `RecordPattern(type)`: the first `patternProperties` key.
pub(crate) fn record_pattern(value: &JsonValue) -> Option<String> {
    entries(field(value, "patternProperties"))
        .into_iter()
        .next()
        .map(|(key, _)| key)
}

/// `RecordValue(type)`.
pub(crate) fn record_value(value: &JsonValue) -> Option<JsonValue> {
    entries(field(value, "patternProperties"))
        .into_iter()
        .next()
        .map(|(_, value)| value)
}

// ------------------------------------------------------------------
// Instantiate
// ------------------------------------------------------------------

/// `Instantiate({}, type)` for immediate (non-deferred, ref-free) types:
/// structural types are rebuilt from their parts and options, then the
/// optional/readonly modifiers are re-applied.
pub(crate) fn instantiate(value: &JsonValue) -> JsonValue {
    let instantiated = match kind(value) {
        Some("Array") => array(
            field(value, "items").map_or(JsonValue::Null, instantiate),
            &options_of(value, &["~kind", "type", "items"]),
        ),
        Some("Intersect") => intersect(
            array_field(value, "allOf")
                .iter()
                .map(instantiate)
                .collect(),
            &options_of(value, &["~kind", "allOf"]),
        ),
        Some("Object") => object(
            entries(field(value, "properties"))
                .into_iter()
                .map(|(key, property)| (key, instantiate(&property)))
                .collect(),
            &options_of(value, &["~kind", "type", "properties", "required"]),
        ),
        Some("Record") => match (record_pattern(value), record_value(value)) {
            (Some(pattern), Some(property)) => record(&pattern, instantiate(&property)),
            _ => value.clone(),
        },
        Some("Tuple") => tuple(
            array_field(value, "items")
                .iter()
                .map(instantiate)
                .collect(),
            &options_of(
                value,
                &["~kind", "type", "items", "minItems", "additionalItems"],
            ),
        ),
        Some("Union") => union_with(
            array_field(value, "anyOf")
                .iter()
                .map(instantiate)
                .collect(),
            &options_of(value, &["~kind", "anyOf"]),
        ),
        _ => value.clone(),
    };
    let with_optional = if is_optional(value) {
        add_optional(&instantiated)
    } else {
        instantiated
    };
    if is_readonly(value) {
        add_readonly(&with_optional)
    } else {
        with_optional
    }
}

// ------------------------------------------------------------------
// Evaluate
// ------------------------------------------------------------------

/// `Evaluate(type)`: `EvaluateType` then a `Memory.Update` clone.
pub(crate) fn evaluate(value: &JsonValue) -> Result<JsonValue, JsError> {
    Ok(update(&evaluate_type(value)?, &[], &JsonObject::new()))
}

/// `EvaluateType`.
pub(crate) fn evaluate_type(value: &JsonValue) -> Result<JsonValue, JsError> {
    match kind(value) {
        Some("Enum") => evaluate_enum(array_field(value, "enum")),
        Some("Intersect") => evaluate_intersect(array_field(value, "allOf")),
        Some("Union") => evaluate_union(array_field(value, "anyOf")),
        _ => Ok(value.clone()),
    }
}

/// `EvaluateEnum(values)`: a union of the distinct literals.
pub(crate) fn evaluate_enum(values: &[JsonValue]) -> Result<JsonValue, JsError> {
    let literals = values.iter().map(literal).collect::<Result<Vec<_>, _>>()?;
    evaluate_union(&literals)
}

/// `EvaluateUnion(types)`.
pub(crate) fn evaluate_union(types: &[JsonValue]) -> Result<JsonValue, JsError> {
    let mut broadened = broaden(types)?;
    Ok(match broadened.len() {
        0 => never(),
        1 => broadened.remove(0),
        _ => union(broadened),
    })
}

/// `EvaluateIntersect(types)`.
pub(crate) fn evaluate_intersect(types: &[JsonValue]) -> Result<JsonValue, JsError> {
    let distribution = distribute(types, Vec::new())?;
    let broadened = broaden(&distribution)?;
    evaluate_union(&broadened)
}

/// `Broaden(types)`: drops types contained in others, then flattens unions.
fn broaden(types: &[JsonValue]) -> Result<Vec<JsonValue>, JsError> {
    let mut result: Vec<JsonValue> = Vec::new();
    for value in types {
        let evaluated = evaluate_type(value)?;
        match kind(&evaluated) {
            // The broadest type: everything else is discarded.
            Some("Any" | "Unknown") => {
                result = vec![evaluated];
                break;
            }
            Some("Never") => {}
            Some("Object") => result.push(evaluated),
            _ => result = broaden_filter(evaluated, result)?,
        }
    }
    Ok(flatten(result))
}

fn broaden_filter(value: JsonValue, types: Vec<JsonValue>) -> Result<Vec<JsonValue>, JsError> {
    let mut kept = Vec::new();
    for left in &types {
        match compare(&value, left)? {
            Comparison::LeftInside | Comparison::Equal => return Ok(types),
            Comparison::Disjoint => kept.push(left.clone()),
            Comparison::RightInside => {}
        }
    }
    kept.push(value);
    Ok(kept)
}

fn flatten(types: Vec<JsonValue>) -> Vec<JsonValue> {
    let mut result = Vec::new();
    for value in types {
        if is_kind(&value, "Union") {
            result.extend(flatten(array_field(&value, "anyOf").to_vec()));
        } else {
            result.push(value);
        }
    }
    result
}

fn distribute(types: &[JsonValue], mut result: Vec<JsonValue>) -> Result<Vec<JsonValue>, JsError> {
    for value in types {
        result = if is_kind(value, "Union") {
            let mut distributed = Vec::new();
            for member in array_field(value, "anyOf") {
                distributed.extend(distribute(std::slice::from_ref(member), result.clone())?);
            }
            distributed
        } else if result.is_empty() {
            vec![value.clone()]
        } else {
            result
                .iter()
                .map(|left| distribute_operation(left, value))
                .collect::<Result<_, _>>()?
        };
    }
    Ok(result)
}

fn distribute_operation(left: &JsonValue, right: &JsonValue) -> Result<JsonValue, JsError> {
    let left = evaluate_type(left)?;
    let right = evaluate_type(right)?;
    if is_kind(&left, "Union") || is_kind(&right, "Union") {
        evaluate_intersect(&[left, right])
    } else {
        narrow(left, right)
    }
}

fn can_composite(value: &JsonValue) -> bool {
    is_kind(value, "Object") || is_kind(value, "Tuple")
}

#[allow(clippy::match_same_arms)] // `Narrow` tests the left operand before the right; the order matters.
fn narrow(left: JsonValue, right: JsonValue) -> Result<JsonValue, JsError> {
    Ok(match (kind(&left), kind(&right)) {
        (Some("Never" | "Any"), _) => left,
        (Some("Unknown"), _) => right,
        (_, Some("Never" | "Any")) => right,
        (_, Some("Unknown")) => left,
        _ => match (can_composite(&left), can_composite(&right)) {
            (true, true) => composite(&left, &right)?,
            (true, false) => left,
            (false, true) => right,
            (false, false) => match compare(&left, &right)? {
                Comparison::LeftInside => left,
                Comparison::RightInside | Comparison::Equal => right,
                Comparison::Disjoint => never(),
            },
        },
    })
}

fn composite_properties_of(value: &JsonValue) -> Vec<(String, JsonValue)> {
    if is_kind(value, "Object") {
        entries(field(value, "properties"))
    } else if is_kind(value, "Tuple") {
        array_field(value, "items")
            .iter()
            .enumerate()
            .map(|(index, item)| (index.to_string(), item.clone()))
            .collect()
    } else {
        Vec::new()
    }
}

/// `Composite(left, right)`: an object with the properties of both; shared
/// properties intersect.
fn composite(left: &JsonValue, right: &JsonValue) -> Result<JsonValue, JsError> {
    let left = composite_properties_of(left);
    let right = composite_properties_of(right);
    let mut keys: Vec<&str> = left.iter().map(|(key, _)| key.as_str()).collect();
    for (key, _) in &right {
        if !keys.contains(&key.as_str()) {
            keys.push(key);
        }
    }
    let find = |properties: &[(String, JsonValue)], key: &str| {
        properties
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| value.clone())
    };
    let mut properties = JsonObject::new();
    for key in keys {
        let property = match (find(&left, key), find(&right, key)) {
            (Some(left), Some(right)) => composite_property(&left, &right)?,
            (Some(only), None) | (None, Some(only)) => only,
            (None, None) => never(),
        };
        properties.insert(key.to_owned(), property);
    }
    Ok(object(properties, &JsonObject::new()))
}

fn composite_property(left: &JsonValue, right: &JsonValue) -> Result<JsonValue, JsError> {
    let readonly = is_readonly(left) && is_readonly(right);
    let optional = is_optional(left) && is_optional(right);
    let evaluated = evaluate_intersect(&[left.clone(), right.clone()])?;
    let property = remove_marker(&remove_marker(&evaluated, "~optional"), "~readonly");
    Ok(match (readonly, optional) {
        (true, true) => add_readonly(&add_optional(&property)),
        (true, false) => add_readonly(&property),
        (false, true) => add_optional(&property),
        (false, false) => property,
    })
}

// ------------------------------------------------------------------
// Compare / Extends
// ------------------------------------------------------------------

/// The set relation of two types (`Compare`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Comparison {
    Equal,
    Disjoint,
    LeftInside,
    RightInside,
}

fn compare(left: &JsonValue, right: &JsonValue) -> Result<Comparison, JsError> {
    Ok(match (extends(left, right)?, extends(right, left)?) {
        (true, true) => Comparison::Equal,
        (true, false) => Comparison::LeftInside,
        (false, true) => Comparison::RightInside,
        (false, false) => Comparison::Disjoint,
    })
}

/// `Extends({}, left, right)` is true-like (`ExtendsTrue` or `ExtendsUnion`).
fn extends(left: &JsonValue, right: &JsonValue) -> Result<bool, JsError> {
    let canonical = |value: &JsonValue| {
        if is_unsafe(value) {
            unknown()
        } else {
            value.clone()
        }
    };
    extends_left(&canonical(left), &canonical(right))
}

fn extends_left(left: &JsonValue, right: &JsonValue) -> Result<bool, JsError> {
    match kind(left) {
        // `ExtendsAny` yields `ExtendsUnion` (true-like) when not true.
        Some("Any" | "Never") => Ok(true),
        Some("Array") => {
            if is_kind(right, "Array") {
                if is_immutable(left) && !is_immutable(right) {
                    return Ok(false);
                }
                let (Some(left_items), Some(right_items)) =
                    (field(left, "items"), field(right, "items"))
                else {
                    return Ok(false);
                };
                return extends_left(left_items, right_items);
            }
            extends_right(left, right)
        }
        Some("Boolean") => primitive(left, right, &["Boolean"]),
        Some("Integer") => primitive(left, right, &["Integer", "Number"]),
        Some("Null") => primitive(left, right, &["Null"]),
        Some("Number") => primitive(left, right, &["Number"]),
        Some("String") => primitive(left, right, &["String"]),
        Some("Enum") => extends_left(&evaluate_enum(array_field(left, "enum"))?, right),
        Some("Intersect") => extends_left(&evaluate_intersect(array_field(left, "allOf"))?, right),
        Some("Literal") => extends_literal(left, right),
        Some("Object") => extends_object(left, right),
        Some("Record") => extends_record(left, right),
        Some("Tuple") => extends_tuple(left, right),
        Some("Union") => {
            let left_types = array_field(left, "anyOf");
            if is_kind(right, "Union") {
                let right_types = array_field(right, "anyOf");
                for member in left_types {
                    if !some_extends(member, right_types)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            } else {
                for member in left_types {
                    if !extends_left(member, right)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
        Some("Unknown") => Ok(matches!(kind(right), Some("Any" | "Unknown"))),
        _ => Ok(false),
    }
}

fn some_extends(left: &JsonValue, types: &[JsonValue]) -> Result<bool, JsError> {
    for member in types {
        if extends_left(left, member)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn primitive(left: &JsonValue, right: &JsonValue, accepted: &[&str]) -> Result<bool, JsError> {
    if kind(right).is_some_and(|name| accepted.contains(&name)) {
        return Ok(true);
    }
    extends_right(left, right)
}

/// `ExtendsRight(left, right)`: the right-hand structural cases.
fn extends_right(left: &JsonValue, right: &JsonValue) -> Result<bool, JsError> {
    match kind(right) {
        Some("Any" | "Unknown") => Ok(true),
        Some("Enum") => extends_left(left, &evaluate_enum(array_field(right, "enum"))?),
        Some("Intersect") => {
            for member in array_field(right, "allOf") {
                if !extends_left(left, member)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Some("Union") => some_extends(left, array_field(right, "anyOf")),
        _ => Ok(false),
    }
}

fn extends_literal(left: &JsonValue, right: &JsonValue) -> Result<bool, JsError> {
    let constant = field(left, "const").unwrap_or(&JsonValue::Null);
    let base = match constant {
        JsonValue::Bool(_) => "Boolean",
        JsonValue::Number(_) => "Number",
        JsonValue::String(_) => "String",
        JsonValue::Null | JsonValue::Array(_) | JsonValue::Object(_) => {
            return Err(JsError::new(JsErrorKind::Error, "Unreachable"))
        }
    };
    if is_kind(right, "Literal") {
        return Ok(field(right, "const").is_some_and(|other| literal_equals(constant, other)));
    }
    if is_kind(right, base) {
        return Ok(true);
    }
    extends_right(&literal(constant)?, right)
}

/// `===` between literal constants.
fn literal_equals(left: &JsonValue, right: &JsonValue) -> bool {
    match (left, right) {
        (JsonValue::Number(left), JsonValue::Number(right)) => left
            .as_f64()
            .zip(right.as_f64())
            .is_some_and(|(left, right)| {
                left.to_bits() == right.to_bits() || (left == 0.0 && right == 0.0)
            }),
        _ => left == right,
    }
}

fn extends_property(left: &JsonValue, right: &JsonValue) -> Result<bool, JsError> {
    Ok(extends_left(left, right)? && (!is_optional(left) || is_optional(right)))
}

fn extends_object(left: &JsonValue, right: &JsonValue) -> Result<bool, JsError> {
    let left_properties = entries(field(left, "properties"));
    if is_kind(right, "Record") {
        let Some(value) = record_value(right) else {
            return Ok(false);
        };
        for (_, property) in &left_properties {
            if !extends_left(property, &value)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if is_kind(right, "Object") {
        for (key, right_property) in entries(field(right, "properties")) {
            let satisfied = match left_properties.iter().find(|(name, _)| *name == key) {
                Some((_, left_property)) => extends_property(left_property, &right_property)?,
                None => is_optional(&right_property),
            };
            if !satisfied {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    extends_right(left, right)
}

fn extends_record(left: &JsonValue, right: &JsonValue) -> Result<bool, JsError> {
    match kind(right) {
        Some("Record") => match (record_value(left), record_value(right)) {
            (Some(left), Some(right)) => extends_left(&left, &right),
            _ => Ok(false),
        },
        Some("Object") => Ok(entries(field(right, "properties")).is_empty()),
        Some("Any" | "Unknown") => Ok(true),
        _ => Ok(false),
    }
}

fn extends_tuple(left: &JsonValue, right: &JsonValue) -> Result<bool, JsError> {
    let left_items = array_field(left, "items");
    if is_kind(right, "Tuple") {
        let right_items = array_field(right, "items");
        if left_items.len() != right_items.len() {
            return Ok(false);
        }
        for (left, right) in left_items.iter().zip(right_items) {
            if !extends_left(left, right)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if is_kind(right, "Array") {
        let Some(items) = field(right, "items") else {
            return Ok(false);
        };
        for item in left_items {
            if !extends_left(item, items)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    extends_right(left, right)
}

/// `String(value)` of a literal record key.
pub(crate) fn property_key(value: &JsonValue) -> Option<String> {
    match value {
        JsonValue::String(text) => Some(text.clone()),
        JsonValue::Number(number) => number.as_f64().map(number_to_js_string),
        JsonValue::Bool(flag) => Some(flag.to_string()),
        JsonValue::Null | JsonValue::Array(_) | JsonValue::Object(_) => None,
    }
}
