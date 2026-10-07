//! Shared machinery of `TypeBox`'s schema engine (`schema/engine`): the
//! evaluation state, `$ref` target classification, and the value guards
//! (`Guard.IsDeepEqual`, grapheme lengths, `Hashing.Hash`, multipleOf).

use std::borrow::Cow;

use super::js_value::{
    compare_utf16, is_integer, js_min3, JsError, JsObject, JsValue, NativeFunction, FALSE_SCHEMA,
};
use super::keywords::{self, Members};
use super::regexp::RegExpCache;
use super::resolve::Resolved;
use super::stack::Stack;

/// Which `TypeBox` evaluator a check follows.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mode {
    /// The JIT-compiled `Validator.Check` (Node's default).
    Compiled,
    /// The interpreted `Schema.Check` / `Schema.Errors` engine.
    Interpreted,
}

/// Nesting limit standing in for V8's call stack: schema recursion that never
/// consumes the value (`{"$ref": "#"}`) throws `RangeError` like the TS.
const MAX_DEPTH: usize = 512;

/// The state of one `Check` or `Errors` run.
pub(crate) struct Engine<'v, 's> {
    pub(crate) regexps: &'v RegExpCache,
    pub(crate) stack: Stack<'s>,
    pub(crate) mode: Mode,
    depth: usize,
}

impl<'v, 's> Engine<'v, 's> {
    pub(crate) fn new(root: &'s JsValue, regexps: &'v RegExpCache, mode: Mode) -> Self {
        Self {
            regexps,
            stack: Stack::new(root),
            mode,
            depth: 0,
        }
    }

    pub(crate) fn enter(&mut self) -> Result<(), JsError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(JsError::stack_overflow());
        }
        Ok(())
    }

    pub(crate) fn leave(&mut self) {
        self.depth -= 1;
    }
}

/// A `$ref`-family target after `?? false`.
pub(crate) enum RefTarget<'s> {
    /// A schema object or boolean schema.
    Schema(&'s JsValue),
    /// An array or function: no keywords, so the compiled check passes while
    /// the interpreter rejects it (`Schema.IsSchema` fails).
    Keywordless,
    /// A primitive: compiling it throws `'type' in <value>`; the interpreter
    /// rejects it.
    Primitive(JsError),
}

pub(crate) fn ref_target(resolved: Option<Resolved<'_>>) -> RefTarget<'_> {
    match resolved {
        None => RefTarget::Schema(&FALSE_SCHEMA),
        Some(Resolved::Value(value @ (JsValue::Object(_) | JsValue::Bool(_)))) => {
            RefTarget::Schema(value)
        }
        Some(Resolved::Value(JsValue::Array(_) | JsValue::Function(_)) | Resolved::Function) => {
            RefTarget::Keywordless
        }
        Some(Resolved::Value(
            value @ (JsValue::Null | JsValue::Number(_) | JsValue::String(_)),
        )) => RefTarget::Primitive(in_operator_error(value)),
        Some(Resolved::Number(number)) => {
            RefTarget::Primitive(in_operator_error(&JsValue::Number(number)))
        }
    }
}

/// The `TypeError` of `'type' in value` on a primitive schema.
pub(crate) fn in_operator_error(value: &JsValue) -> JsError {
    JsError::type_error(format!(
        "Cannot use 'in' operator to search for 'type' in {}",
        value.primitive_to_string()
    ))
}

/// `value[key]` on a plain object whose key passed `HasPropertyKey`.
pub(crate) fn property<'a>(object: &'a JsObject, key: &str) -> Cow<'a, JsValue> {
    match object.get_own(key) {
        Some(value) => Cow::Borrowed(value),
        None => Cow::Owned(NativeFunction::inherited(key).map_or(JsValue::Null, JsValue::Function)),
    }
}

/// `Object.entries(value)` of an object or array instance.
pub(crate) fn instance_entries(value: &JsValue) -> Vec<(Cow<'_, str>, &JsValue)> {
    match value {
        JsValue::Object(object) => Members::Object(object).entries(),
        JsValue::Array(items) => Members::Array(items).entries(),
        JsValue::Null
        | JsValue::Bool(_)
        | JsValue::Number(_)
        | JsValue::String(_)
        | JsValue::Function(_) => Vec::new(),
    }
}

/// `GetPropertiesPattern(schema)`: the pattern matching every key covered by
/// `patternProperties` or `properties`.
pub(crate) fn properties_pattern(schema: &JsValue) -> String {
    let mut patterns: Vec<String> = Vec::new();
    if let Some(pattern_properties) = keywords::pattern_properties(schema) {
        patterns.extend(pattern_properties.keys().into_iter().map(Cow::into_owned));
    }
    if let Some(properties) = keywords::properties(schema) {
        patterns.extend(
            properties
                .keys()
                .iter()
                .map(|key| format!("^{}$", escape_pattern(key))),
        );
    }
    if patterns.is_empty() {
        "(?!)".to_owned()
    } else {
        format!("({})", patterns.join("|"))
    }
}

/// `key.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')`.
fn escape_pattern(key: &str) -> String {
    let mut escaped = String::with_capacity(key.len());
    for c in key.chars() {
        if matches!(
            c,
            '.' | '*' | '+' | '?' | '^' | '$' | '{' | '}' | '(' | ')' | '|' | '[' | ']' | '\\'
        ) {
            escaped.push('\\');
        }
        escaped.push(c);
    }
    escaped
}

/// `CanAdditionalPropertiesFast`: the compiled check counts own keys instead.
pub(crate) fn can_additional_properties_fast(schema: &JsValue) -> Option<usize> {
    let required = keywords::required(schema)?;
    let properties = keywords::properties(schema)?;
    let fast = keywords::pattern_properties(schema).is_none()
        && matches!(
            keywords::additional_properties(schema),
            Some(JsValue::Bool(false))
        )
        && properties.keys().len() == required.len();
    fast.then_some(required.len())
}

/// `Schema.IsType` value checks (`CheckTypeName`).
pub(crate) fn check_type_name(name: &str, value: &JsValue) -> bool {
    match name {
        "object" => matches!(value, JsValue::Object(_)),
        "array" => matches!(value, JsValue::Array(_)),
        "boolean" => matches!(value, JsValue::Bool(_)),
        "integer" => matches!(value, JsValue::Number(number) if is_integer(*number)),
        "number" => matches!(value, JsValue::Number(number) if number.is_finite()),
        "null" => matches!(value, JsValue::Null),
        "string" => matches!(value, JsValue::String(_)),
        // Native functions are constructors per `Guard.IsConstructor` (`[native code]`).
        "constructor" | "function" => matches!(value, JsValue::Function(_)),
        "bigint" | "symbol" | "undefined" | "void" => false,
        _ => true,
    }
}

pub(crate) fn check_type(type_: &JsValue, value: &JsValue) -> bool {
    match type_ {
        JsValue::String(name) => check_type_name(name, value),
        JsValue::Array(names) => keywords::strings(names).any(|name| check_type_name(name, value)),
        JsValue::Null
        | JsValue::Bool(_)
        | JsValue::Number(_)
        | JsValue::Object(_)
        | JsValue::Function(_) => true,
    }
}

/// `Guard.IsValueLike(value) ? value === constant : Guard.IsDeepEqual(value, constant)`.
pub(crate) fn const_matches(value: &JsValue, constant: &JsValue) -> bool {
    deep_equal(value, constant)
}

/// `Guard.IsDeepEqual(left, right)`.
fn deep_equal(left: &JsValue, right: &JsValue) -> bool {
    match left {
        JsValue::Array(left_items) => match right {
            JsValue::Array(right_items) => {
                left_items.len() == right_items.len()
                    && left_items
                        .iter()
                        .zip(right_items)
                        .all(|(left, right)| deep_equal(left, right))
            }
            _ => false,
        },
        JsValue::Object(left_object) => {
            let keys = left_object.keys();
            match right {
                JsValue::Object(right_object) => {
                    keys.len() == right_object.len()
                        && keys.iter().all(|key| {
                            match (left_object.get_own(key), right_object.get(key)) {
                                (Some(left), Some(right)) => deep_equal(left, &right),
                                _ => false,
                            }
                        })
                }
                // `Object.getOwnPropertyNames(array)` lists the indices and `length`.
                JsValue::Array(right_items) => {
                    keys.len() == right_items.len() + 1
                        && keys.iter().all(|key| {
                            let right = match *key {
                                "length" => Some(Cow::Owned(JsValue::Number(
                                    super::js_value::usize_to_f64(right_items.len()),
                                ))),
                                _ => crate::utils::js::array_index_key(key)
                                    .and_then(|index| usize::try_from(index).ok())
                                    .and_then(|index| right_items.get(index))
                                    .map(Cow::Borrowed),
                            };
                            match (left_object.get_own(key), right) {
                                (Some(left), Some(right)) => deep_equal(left, &right),
                                _ => false,
                            }
                        })
                }
                JsValue::Null
                | JsValue::Bool(_)
                | JsValue::Number(_)
                | JsValue::String(_)
                | JsValue::Function(_) => false,
            }
        }
        JsValue::Null
        | JsValue::Bool(_)
        | JsValue::Number(_)
        | JsValue::String(_)
        | JsValue::Function(_) => super::js_value::strict_equals(left, right),
    }
}

/// `Guard.IsMultipleOf(dividend, divisor)` for a finite dividend.
pub(crate) fn is_multiple_of(dividend: f64, divisor: f64) -> bool {
    if is_integer(dividend) && (1.0 / divisor) % 1.0 == 0.0 {
        return true;
    }
    let remainder = dividend % divisor;
    js_min3(
        remainder.abs(),
        (remainder - divisor).abs(),
        (remainder + divisor).abs(),
    ) < 1e-10
}

// ------------------------------------------------------------------
// Grapheme lengths (guard/string.mjs)
// ------------------------------------------------------------------

fn code_point_at(units: &[u16], index: usize) -> Option<u32> {
    let first = *units.get(index)?;
    if (0xD800..=0xDBFF).contains(&first) {
        if let Some(second) = units
            .get(index + 1)
            .filter(|second| (0xDC00..=0xDFFF).contains(*second))
        {
            return Some(
                0x10000 + ((u32::from(first) - 0xD800) << 10) + (u32::from(*second) - 0xDC00),
            );
        }
    }
    Some(u32::from(first))
}

fn code_point_length(point: u32) -> usize {
    if point > 0xFFFF {
        2
    } else {
        1
    }
}

fn is_combining_mark(point: u32) -> bool {
    matches!(point, 0x0300..=0x036F | 0x1AB0..=0x1AFF | 0x1DC0..=0x1DFF | 0xFE20..=0xFE2F)
}

fn is_variation_selector(point: u32) -> bool {
    (0xFE00..=0xFE0F).contains(&point)
}

fn is_regional_indicator(point: u32) -> bool {
    (0x1F1E6..=0x1F1FF).contains(&point)
}

fn consume_modifiers(units: &[u16], mut index: usize) -> usize {
    while let Some(point) = code_point_at(units, index) {
        if is_combining_mark(point) || is_variation_selector(point) {
            index += code_point_length(point);
        } else {
            break;
        }
    }
    index
}

fn next_grapheme_cluster_index(units: &[u16], start: usize) -> usize {
    let start_point = code_point_at(units, start).unwrap_or(0);
    let mut end = consume_modifiers(units, start + code_point_length(start_point));
    while end + 1 < units.len() && code_point_at(units, end) == Some(0x200D) {
        let next = code_point_at(units, end + 1).unwrap_or(0);
        end = consume_modifiers(units, end + 1 + code_point_length(next));
    }
    if is_regional_indicator(start_point) {
        if let Some(point) = code_point_at(units, end).filter(|point| is_regional_indicator(*point))
        {
            end += code_point_length(point);
        }
    }
    end
}

/// `IsGraphemeCodePoint(value.charCodeAt(index))` (a code unit).
fn is_grapheme_code_unit(units: &[u16], index: usize) -> bool {
    units.get(index).is_some_and(|unit| {
        let unit = u32::from(*unit);
        unit >= 0x0300
            && ((0xD800..=0xDBFF).contains(&unit)
                || is_combining_mark(unit)
                || is_variation_selector(unit)
                || unit == 0x200D)
    })
}

fn len_f64(units: &[u16]) -> f64 {
    super::js_value::usize_to_f64(units.len())
}

/// `Guard.IsMinLength(value, minLength)`: at least `minLength` graphemes.
pub(crate) fn is_min_length(value: &str, min_length: f64) -> bool {
    if min_length == 0.0 {
        return true;
    }
    let units: Vec<u16> = value.encode_utf16().collect();
    if len_f64(&units) < min_length {
        return false;
    }
    let mut index = 0;
    loop {
        if is_grapheme_code_unit(&units, index) {
            let mut count = 0.0;
            let mut position = 0;
            while position < units.len() {
                position = next_grapheme_cluster_index(&units, position);
                count += 1.0;
                if count >= min_length {
                    return true;
                }
            }
            return false;
        }
        index += 1;
        if super::js_value::usize_to_f64(index) >= min_length {
            return true;
        }
    }
}

/// `Guard.IsMaxLength(value, maxLength)`: at most `maxLength` graphemes.
pub(crate) fn is_max_length(value: &str, max_length: f64) -> bool {
    let units: Vec<u16> = value.encode_utf16().collect();
    if len_f64(&units) <= max_length {
        return true;
    }
    let mut index = 0;
    loop {
        if is_grapheme_code_unit(&units, index) {
            let mut count = 0.0;
            let mut position = 0;
            while position < units.len() {
                position = next_grapheme_cluster_index(&units, position);
                count += 1.0;
                if count > max_length {
                    return false;
                }
            }
            return true;
        }
        index += 1;
        if super::js_value::usize_to_f64(index) > max_length {
            return false;
        }
    }
}

// ------------------------------------------------------------------
// Hashing.Hash (FNV-1a 64) for uniqueItems
// ------------------------------------------------------------------

struct Fnv(u64);

impl Fnv {
    fn byte(&mut self, byte: u8) {
        self.0 ^= u64::from(byte);
        self.0 = self.0.wrapping_mul(1_099_511_628_211);
    }

    fn string(&mut self, text: &str) {
        self.byte(10);
        for byte in text.bytes() {
            self.byte(byte);
        }
    }

    fn value(&mut self, value: &JsValue) {
        match value {
            JsValue::Number(number) => {
                self.byte(7);
                for byte in number.to_le_bytes() {
                    self.byte(byte);
                }
            }
            JsValue::Array(items) => {
                self.byte(0);
                for item in items {
                    self.value(item);
                }
            }
            JsValue::Bool(flag) => {
                self.byte(2);
                self.byte(u8::from(*flag));
            }
            JsValue::Null => self.byte(6),
            JsValue::Object(object) => {
                self.byte(8);
                let mut entries: Vec<(&str, &JsValue)> = object
                    .entries()
                    .into_iter()
                    .filter(|(key, _)| *key != "constructor")
                    .collect();
                entries.sort_by(|(left, _), (right, _)| compare_utf16(left, right));
                for (key, value) in entries {
                    self.string(key);
                    self.value(value);
                }
            }
            JsValue::String(text) => self.string(text),
            JsValue::Function(function) => {
                self.byte(4);
                self.string(&function.source());
            }
        }
    }
}

/// `Hashing.Hash(value)`.
pub(crate) fn hash(value: &JsValue) -> u64 {
    let mut fnv = Fnv(14_695_981_039_346_656_037);
    fnv.value(value);
    fnv.0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grapheme_lengths_follow_typebox() {
        assert!(is_max_length("abc", 3.0));
        assert!(!is_max_length("abcd", 3.0));
        // "e" + combining acute counts as one grapheme.
        assert!(is_max_length("e\u{301}", 1.0));
        assert!(!is_min_length("e\u{301}", 2.0));
        // Astral characters count once.
        assert!(is_max_length("😀😀", 2.0));
        assert!(is_min_length("ab", -1.0));
    }

    #[test]
    fn multiple_of_tolerates_float_error() {
        assert!(is_multiple_of(0.3, 0.1));
        assert!(is_multiple_of(10.0, 0.5));
        assert!(!is_multiple_of(10.0, 3.0));
        assert!(is_multiple_of(7.0, 0.0001));
    }

    #[test]
    fn hash_ignores_constructor_keys_and_key_order() {
        let left = JsValue::from_json(&serde_json::json!({ "a": 1, "b": [true, null] }));
        let right =
            JsValue::from_json(&serde_json::json!({ "b": [true, null], "a": 1, "constructor": 5 }));
        assert_eq!(hash(&left), hash(&right));
        assert_ne!(
            hash(&JsValue::Number(1.0)),
            hash(&JsValue::String("1".to_owned()))
        );
    }
}
