//! `TypeBox` `Value.Convert(type, value)` (`value/convert`): kind-directed
//! conversion of a value toward a `TypeBox`-built schema, in place.
//!
//! Dispatch reads each node's `~kind` marker from the schema's `TypeBox` view,
//! so plain JSON schemas (no markers) pass values through untouched, as in
//! the TS. `validate_tool_arguments` discards the returned value and keeps
//! the in-place mutations, so [`Converter::convert_type`] reports a replacement
//! value separately from mutating `value`.
//!
//! The kinds handled are those `crate::typebox::Type` builds. Kinds it
//! cannot build (`BigInt`, `Undefined`, `Void`, `Cyclic`, `TemplateLiteral`)
//! produce values JSON cannot hold and pass through; `Ref` passes through as
//! in the TS (the conversion context is empty).

use eukhe_types::pi_ai::JsonValue;

use super::context::CheckContext;
use super::engine::{Engine, Mode};
use super::js_value::{
    is_unsafe_property_key, strict_equals, string_to_number, JsError, JsErrorKind, JsObject,
    JsValue,
};
use super::regexp::{JsRegExp, RegExpCache};
use crate::typebox::algebra;
use crate::utils::js::number_to_js_string;

/// `Value.Convert` state: the regexps compiled by `Value.Check` calls.
#[derive(Default)]
pub(crate) struct Converter {
    regexps: RegExpCache,
}

type Converted = Result<Option<JsValue>, JsError>;

impl Converter {
    /// `Value.Convert(type, value)` with its result discarded.
    pub(crate) fn convert(&self, type_: &JsonValue, value: &mut JsValue) -> Result<(), JsError> {
        self.convert_type(type_, value).map(drop)
    }

    /// `FromType(context, type, value)`: mutates `value` in place and returns
    /// `Some` when the TS returns a different value.
    fn convert_type(&self, type_: &JsonValue, value: &mut JsValue) -> Converted {
        match algebra::kind(type_) {
            Some("Array") => self.convert_array(type_, value),
            Some("Boolean") => Ok(try_boolean(value).map(JsValue::Bool)),
            Some("Enum") => {
                let evaluated = algebra::evaluate(type_)?;
                self.convert_type(&evaluated, value)
            }
            Some("Integer") => Ok(try_number(value).map(|number| JsValue::Number(number.trunc()))),
            Some("Intersect") => {
                let evaluated = algebra::evaluate(&algebra::instantiate(type_))?;
                self.convert_type(&evaluated, value)
            }
            Some("Literal") => from_literal(type_, value),
            Some("Null") => Ok(try_null(value).then_some(JsValue::Null)),
            Some("Number") => Ok(try_number(value).map(JsValue::Number)),
            Some("Object") => self.convert_object(type_, value).map(|()| None),
            Some("Record") => self.convert_record(type_, value).map(|()| None),
            Some("String") => Ok(try_string(value).map(JsValue::String)),
            Some("Tuple") => self.convert_tuple(type_, value).map(|()| None),
            Some("Union") => self.convert_union(type_, value),
            _ => Ok(None),
        }
    }

    /// Converts `value[key]` in place (`value[key] = FromType(type, value[key])`).
    fn convert_property(
        &self,
        type_: &JsonValue,
        object: &mut JsObject,
        key: &str,
    ) -> Result<(), JsError> {
        if let Some(property) = object.get_own_mut(key) {
            if let Some(replacement) = self.convert_type(type_, property)? {
                *property = replacement;
            }
        }
        Ok(())
    }

    /// `FromArray`: `TryArray` wraps a non-array, then maps the items.
    fn convert_array(&self, type_: &JsonValue, value: &mut JsValue) -> Converted {
        let items_type = type_.get("items").unwrap_or(&JsonValue::Null);
        let convert_item = |item: &mut JsValue| -> Result<JsValue, JsError> {
            Ok(match self.convert_type(items_type, item)? {
                Some(replacement) => replacement,
                None => item.clone(),
            })
        };
        let mapped = match value {
            JsValue::Array(items) => items
                .iter_mut()
                .map(convert_item)
                .collect::<Result<Vec<_>, _>>()?,
            JsValue::Null
            | JsValue::Bool(_)
            | JsValue::Number(_)
            | JsValue::String(_)
            | JsValue::Object(_)
            | JsValue::Function(_) => {
                vec![convert_item(value)?]
            }
        };
        Ok(Some(JsValue::Array(mapped)))
    }

    /// `FromObject`: property keys act as anchored regexps (`^key$`, no flags).
    fn convert_object(&self, type_: &JsonValue, value: &mut JsValue) -> Result<(), JsError> {
        let JsValue::Object(object) = value else {
            return Ok(());
        };
        let entries = entries_regexp(type_.get("properties"))?;
        let keys: Vec<String> = object.keys().into_iter().map(str::to_owned).collect();
        for (regexp, property) in &entries {
            for key in &keys {
                // `IsOptionalUndefined`: own values are never `undefined`.
                if regexp.test(key) {
                    self.convert_property(property, object, key)?;
                }
            }
        }
        self.convert_additional_properties(type_, &entries, object)
    }

    /// `FromRecord`: `patternProperties` keys as anchored regexps.
    fn convert_record(&self, type_: &JsonValue, value: &mut JsValue) -> Result<(), JsError> {
        let JsValue::Object(object) = value else {
            return Ok(());
        };
        let entries = entries_regexp(type_.get("patternProperties"))?;
        let keys: Vec<String> = object.keys().into_iter().map(str::to_owned).collect();
        for (regexp, property) in &entries {
            for key in &keys {
                if regexp.test(key) {
                    self.convert_property(property, object, key)?;
                }
            }
        }
        self.convert_additional_properties(type_, &entries, object)
    }

    /// `FromAdditionalProperties`: once per entry, every key that entry does
    /// not match converts through `additionalProperties` (when it is an object).
    fn convert_additional_properties(
        &self,
        type_: &JsonValue,
        entries: &[(JsRegExp, JsonValue)],
        object: &mut JsObject,
    ) -> Result<(), JsError> {
        let Some(additional @ (JsonValue::Object(_) | JsonValue::Array(_))) =
            type_.get("additionalProperties")
        else {
            return Ok(());
        };
        let keys: Vec<String> = object.keys().into_iter().map(str::to_owned).collect();
        for (regexp, _) in entries {
            for key in &keys {
                if !regexp.test(key) {
                    self.convert_property(additional, object, key)?;
                }
            }
        }
        Ok(())
    }

    /// `FromTuple`: converts the leading items in place.
    fn convert_tuple(&self, type_: &JsonValue, value: &mut JsValue) -> Result<(), JsError> {
        let JsValue::Array(items) = value else {
            return Ok(());
        };
        let item_types = type_
            .get("items")
            .and_then(JsonValue::as_array)
            .map_or(&[][..], Vec::as_slice);
        for (item_type, item) in item_types.iter().zip(items.iter_mut()) {
            if let Some(replacement) = self.convert_type(item_type, item)? {
                *item = replacement;
            }
        }
        Ok(())
    }

    /// `FromUnion`: keep a value some member accepts; else the first member
    /// conversion (of a clone) the whole union accepts.
    fn convert_union(&self, type_: &JsonValue, value: &mut JsValue) -> Converted {
        let members = type_
            .get("anyOf")
            .and_then(JsonValue::as_array)
            .map_or(&[][..], Vec::as_slice);
        for member in members {
            if self.check(member, value)? {
                return Ok(None);
            }
        }
        let mut conversions = Vec::with_capacity(members.len());
        for member in members {
            let mut converted = typebox_clone(value);
            if let Some(replacement) = self.convert_type(member, &mut converted)? {
                converted = replacement;
            }
            conversions.push(converted);
        }
        for converted in conversions {
            if self.check(type_, &converted)? {
                return Ok(Some(converted));
            }
        }
        Ok(None)
    }

    /// `Value.Check(context, type, value)`: the interpreted checker rooted at `type`.
    fn check(&self, type_: &JsonValue, value: &JsValue) -> Result<bool, JsError> {
        let root = JsValue::from_json(type_);
        let mut engine = Engine::new(&root, &self.regexps, Mode::Interpreted);
        engine.check_schema(&mut CheckContext::new(), &root, value)
    }
}

/// `Guard.EntriesRegExp(map)`: `[new RegExp(`^${key}$`), map[key]]`.
fn entries_regexp(map: Option<&JsonValue>) -> Result<Vec<(JsRegExp, JsonValue)>, JsError> {
    let Some(JsonValue::Object(map)) = map else {
        return Ok(Vec::new());
    };
    algebra::js_ordered(map.clone())
        .into_iter()
        .map(|(key, value)| Ok((JsRegExp::new(&format!("^{key}$"), "")?, value)))
        .collect()
}

/// `Clone(value)` (`system/memory/clone.mjs`): plain objects drop the unsafe
/// keys (`__proto__`, `constructor`, `prototype`).
fn typebox_clone(value: &JsValue) -> JsValue {
    match value {
        JsValue::Array(items) => JsValue::Array(items.iter().map(typebox_clone).collect()),
        JsValue::Object(object) => JsValue::Object(
            object
                .entries()
                .into_iter()
                .filter(|(key, _)| !is_unsafe_property_key(key))
                .map(|(key, value)| (key.to_owned(), typebox_clone(value)))
                .collect(),
        ),
        JsValue::Null
        | JsValue::Bool(_)
        | JsValue::Number(_)
        | JsValue::String(_)
        | JsValue::Function(_) => value.clone(),
    }
}

/// `FromLiteral`: the matching `Try*` conversion when it yields the constant.
fn from_literal(type_: &JsonValue, value: &JsValue) -> Converted {
    let constant = type_.get("const").map(JsValue::from_json);
    let Some(constant) = constant else {
        return Err(JsError::new(JsErrorKind::Error, "Unreachable"));
    };
    if strict_equals(&constant, value) {
        return Ok(None);
    }
    let converted = match constant {
        JsValue::Bool(_) => try_boolean(value).map(JsValue::Bool),
        JsValue::Number(_) => try_number(value).map(JsValue::Number),
        JsValue::String(_) => try_string(value).map(JsValue::String),
        JsValue::Null | JsValue::Array(_) | JsValue::Object(_) | JsValue::Function(_) => {
            return Err(JsError::new(JsErrorKind::Error, "Unreachable"));
        }
    };
    Ok(converted.filter(|converted| strict_equals(&constant, converted)))
}

/// `TryBoolean`.
fn try_boolean(value: &JsValue) -> Option<bool> {
    match value {
        JsValue::Bool(flag) => Some(*flag),
        JsValue::Number(number) if *number == 0.0 => Some(false),
        JsValue::Number(number) if is_one(*number) => Some(true),
        JsValue::Null => Some(false),
        JsValue::String(text) => match text.to_lowercase().as_str() {
            "false" => Some(false),
            "true" => Some(true),
            _ => match text.as_str() {
                "0" => Some(false),
                "1" => Some(true),
                _ => None,
            },
        },
        JsValue::Number(_) | JsValue::Array(_) | JsValue::Object(_) | JsValue::Function(_) => None,
    }
}

#[allow(clippy::float_cmp)] // JS `value === 1`.
fn is_one(number: f64) -> bool {
    number == 1.0
}

/// `TryNumber`.
fn try_number(value: &JsValue) -> Option<f64> {
    match value {
        JsValue::Bool(flag) => Some(if *flag { 1.0 } else { 0.0 }),
        JsValue::Number(number) => number.is_finite().then_some(*number),
        JsValue::Null => Some(0.0),
        JsValue::String(text) => number_from_string(text),
        JsValue::Array(_) | JsValue::Object(_) | JsValue::Function(_) => None,
    }
}

/// `TryNumber` of a string: `+value`, then `true`/`false`, then a
/// safe-range `BigInt` literal (`123n`).
fn number_from_string(text: &str) -> Option<f64> {
    let coerced = string_to_number(text);
    if coerced.is_finite() {
        return Some(coerced);
    }
    match text.to_lowercase().as_str() {
        "false" => return Some(0.0),
        "true" => return Some(1.0),
        _ => {}
    }
    // `+value` already parsed every finite decimal or integer string, so only
    // the `<digits>n` form can land in the safe range.
    let digits = text.strip_suffix('n')?;
    let (negative, magnitude) = match digits.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, digits),
    };
    let canonical = magnitude == "0"
        || (magnitude.starts_with(|c: char| ('1'..='9').contains(&c))
            && magnitude.bytes().all(|byte| byte.is_ascii_digit()));
    if !canonical || magnitude.len() > 16 {
        return None;
    }
    let parsed: i64 = magnitude.parse().ok()?;
    if parsed > 9_007_199_254_740_991 {
        return None;
    }
    // Checked within ±(2^53 - 1): the conversion is exact.
    #[allow(clippy::cast_precision_loss)]
    let number = parsed as f64;
    Some(if negative { -number } else { number })
}

/// `TryNull`.
fn try_null(value: &JsValue) -> bool {
    match value {
        JsValue::Bool(flag) => !flag,
        JsValue::Number(number) => *number == 0.0,
        JsValue::Null => true,
        JsValue::String(text) => {
            let lowercase = text.to_lowercase();
            lowercase == "undefined" || lowercase == "null" || text.is_empty() || text == "0"
        }
        JsValue::Array(_) | JsValue::Object(_) | JsValue::Function(_) => false,
    }
}

/// `TryString`.
fn try_string(value: &JsValue) -> Option<String> {
    match value {
        JsValue::Bool(flag) => Some(flag.to_string()),
        JsValue::Number(number) => number.is_finite().then(|| number_to_js_string(*number)),
        JsValue::Null => Some("null".to_owned()),
        JsValue::String(text) => Some(text.clone()),
        JsValue::Array(_) | JsValue::Object(_) | JsValue::Function(_) => None,
    }
}
