//! The JS value model the validation port runs on.
//!
//! validation.ts and `TypeBox` operate on JS values, not JSON: numbers are
//! doubles, objects enumerate array-index keys first, and property reads see
//! `Object.prototype` members (`value.toString` is a function, `"valueOf" in {}`
//! is true). Tool arguments and schemas enter as JSON and are converted once;
//! results leave through [`JsValue::to_json`], which drops function-valued
//! properties exactly as `JSON.stringify` does.

use eukhe_types::pi_ai::{JsonObject, JsonValue};

use crate::utils::js::{array_index_key, js_number_value, js_trim, number_to_js_string};

/// A JS exception class the ported code can throw.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JsErrorKind {
    /// A plain `Error` (`TypeBox`'s `Invalid Literal value`, `Unreachable`).
    Error,
    /// `TypeError` (property access on `null`, `in` on a primitive, invalid URL, ...).
    TypeError,
    /// `SyntaxError` (an invalid `RegExp` pattern in a schema).
    SyntaxError,
    /// `RangeError` (`Maximum call stack size exceeded`).
    RangeError,
    /// `URIError` (`decodeURIComponent` on a malformed `$ref` fragment).
    UriError,
    /// `DOMException` named `DataCloneError` (`structuredClone` of a function).
    DataCloneError,
}

/// A thrown JS exception: its class and `message`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct JsError {
    pub(crate) kind: JsErrorKind,
    pub(crate) message: String,
}

impl JsError {
    pub(crate) fn new(kind: JsErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
        }
    }

    pub(crate) fn type_error(message: impl Into<String>) -> Self {
        Self::new(JsErrorKind::TypeError, message)
    }

    /// `new URL(...)` on an unparsable input.
    pub(crate) fn invalid_url() -> Self {
        Self::type_error("Invalid URL")
    }

    /// The `RangeError` V8 throws when recursion exhausts the call stack.
    pub(crate) fn stack_overflow() -> Self {
        Self::new(JsErrorKind::RangeError, "Maximum call stack size exceeded")
    }
}

/// A native method inherited from `Object.prototype`, as seen by a property
/// read such as `value.toString` on a plain object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeFunction {
    /// `Object` (`value.constructor`).
    Object,
    DefineGetter,
    DefineSetter,
    HasOwnProperty,
    LookupGetter,
    LookupSetter,
    IsPrototypeOf,
    PropertyIsEnumerable,
    ToString,
    ValueOf,
    ToLocaleString,
}

impl NativeFunction {
    /// The `Object.prototype` member named `key`. `__proto__` is an accessor
    /// returning `Object.prototype` itself, not a function, and is not modeled.
    pub(crate) fn inherited(key: &str) -> Option<Self> {
        Some(match key {
            "constructor" => Self::Object,
            "__defineGetter__" => Self::DefineGetter,
            "__defineSetter__" => Self::DefineSetter,
            "hasOwnProperty" => Self::HasOwnProperty,
            "__lookupGetter__" => Self::LookupGetter,
            "__lookupSetter__" => Self::LookupSetter,
            "isPrototypeOf" => Self::IsPrototypeOf,
            "propertyIsEnumerable" => Self::PropertyIsEnumerable,
            "toString" => Self::ToString,
            "valueOf" => Self::ValueOf,
            "toLocaleString" => Self::ToLocaleString,
            _ => return None,
        })
    }

    fn name(self) -> &'static str {
        match self {
            Self::Object => "Object",
            Self::DefineGetter => "__defineGetter__",
            Self::DefineSetter => "__defineSetter__",
            Self::HasOwnProperty => "hasOwnProperty",
            Self::LookupGetter => "__lookupGetter__",
            Self::LookupSetter => "__lookupSetter__",
            Self::IsPrototypeOf => "isPrototypeOf",
            Self::PropertyIsEnumerable => "propertyIsEnumerable",
            Self::ToString => "toString",
            Self::ValueOf => "valueOf",
            Self::ToLocaleString => "toLocaleString",
        }
    }

    /// `Function.prototype.toString` of the native function.
    pub(crate) fn source(self) -> String {
        format!("function {}() {{ [native code] }}", self.name())
    }
}

/// `Guard.IsUnsafePropertyKey`: keys `TypeBox` only looks up as own properties.
pub(crate) fn is_unsafe_property_key(key: &str) -> bool {
    matches!(key, "__proto__" | "constructor" | "prototype")
}

/// A JS value reachable from JSON input.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum JsValue {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<JsValue>),
    Object(JsObject),
    /// A native function copied into an own property (`value[key] = value[key]`
    /// on an inherited `Object.prototype` member).
    Function(NativeFunction),
}

/// `false` as a schema (`?? false` on an unresolved `$ref`).
pub(crate) static FALSE_SCHEMA: JsValue = JsValue::Bool(false);
/// `true` as a schema (an absent `then`/`else`).
pub(crate) static TRUE_SCHEMA: JsValue = JsValue::Bool(true);

/// A plain JS object: own data properties in creation order.
#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct JsObject {
    entries: Vec<(String, JsValue)>,
}

impl JsObject {
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn get_own(&self, key: &str) -> Option<&JsValue> {
        self.entries
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| value)
    }

    pub(crate) fn has_own(&self, key: &str) -> bool {
        self.entries.iter().any(|(name, _)| name == key)
    }

    pub(crate) fn get_own_mut(&mut self, key: &str) -> Option<&mut JsValue> {
        self.entries
            .iter_mut()
            .find(|(name, _)| name == key)
            .map(|(_, value)| value)
    }

    /// `object[key] = value`: replaces in place or appends a new own property.
    pub(crate) fn set(&mut self, key: &str, value: JsValue) {
        match self.entries.iter_mut().find(|(name, _)| name == key) {
            Some((_, slot)) => *slot = value,
            None => self.entries.push((key.to_owned(), value)),
        }
    }

    /// `delete object[key]`.
    pub(crate) fn remove(&mut self, key: &str) -> Option<JsValue> {
        let position = self.entries.iter().position(|(name, _)| name == key)?;
        Some(self.entries.remove(position).1)
    }

    /// Removes the own property `key`, returning its value (used to coerce a
    /// property in place without cloning it).
    pub(crate) fn take(&mut self, key: &str) -> Option<JsValue> {
        let slot = self.entries.iter_mut().find(|(name, _)| name == key)?;
        Some(std::mem::replace(&mut slot.1, JsValue::Null))
    }

    /// Own entries in JS enumeration order (`Object.entries`,
    /// `Object.getOwnPropertyNames`): array-index keys ascending, then the
    /// remaining keys in creation order.
    pub(crate) fn entries(&self) -> Vec<(&str, &JsValue)> {
        let mut indexed: Vec<(u32, &str, &JsValue)> = Vec::new();
        let mut named: Vec<(&str, &JsValue)> = Vec::new();
        for (key, value) in &self.entries {
            match array_index_key(key) {
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

    /// Own keys in JS enumeration order.
    pub(crate) fn keys(&self) -> Vec<&str> {
        self.entries().into_iter().map(|(key, _)| key).collect()
    }

    /// `object[key]`: the own value, else the inherited `Object.prototype`
    /// method, else `undefined`.
    pub(crate) fn get(&self, key: &str) -> Option<JsValue> {
        match self.get_own(key) {
            Some(value) => Some(value.clone()),
            None => NativeFunction::inherited(key).map(JsValue::Function),
        }
    }

    /// `key in object` for a plain object (own or inherited from
    /// `Object.prototype`; `__proto__` is inherited too).
    pub(crate) fn has_in(&self, key: &str) -> bool {
        self.has_own(key) || key == "__proto__" || NativeFunction::inherited(key).is_some()
    }

    /// `Guard.HasPropertyKey`: own-only for the unsafe keys, `in` otherwise.
    pub(crate) fn has_property_key(&self, key: &str) -> bool {
        if is_unsafe_property_key(key) {
            self.has_own(key)
        } else {
            self.has_in(key)
        }
    }
}

impl FromIterator<(String, JsValue)> for JsObject {
    fn from_iter<T: IntoIterator<Item = (String, JsValue)>>(iter: T) -> Self {
        let mut object = Self::default();
        for (key, value) in iter {
            object.set(&key, value);
        }
        object
    }
}

impl JsValue {
    /// `JSON.parse` of the serialized JSON value.
    pub(crate) fn from_json(value: &JsonValue) -> Self {
        match value {
            JsonValue::Null => Self::Null,
            JsonValue::Bool(flag) => Self::Bool(*flag),
            JsonValue::Number(number) => Self::Number(number.as_f64().unwrap_or(f64::NAN)),
            JsonValue::String(text) => Self::String(text.clone()),
            JsonValue::Array(items) => Self::Array(items.iter().map(Self::from_json).collect()),
            JsonValue::Object(map) => Self::Object(Self::object_from_json(map)),
        }
    }

    pub(crate) fn object_from_json(map: &JsonObject) -> JsObject {
        map.iter()
            .map(|(key, value)| (key.clone(), Self::from_json(value)))
            .collect()
    }

    /// `JSON.parse(JSON.stringify(value))`: functions vanish from objects and
    /// become `null` in arrays; keys follow JS enumeration order.
    pub(crate) fn to_json(&self) -> JsonValue {
        match self {
            Self::Null | Self::Function(_) => JsonValue::Null,
            Self::Bool(flag) => JsonValue::Bool(*flag),
            Self::Number(number) => js_number_value(*number),
            Self::String(text) => JsonValue::String(text.clone()),
            Self::Array(items) => JsonValue::Array(items.iter().map(Self::to_json).collect()),
            Self::Object(object) => JsonValue::Object(
                object
                    .entries()
                    .into_iter()
                    .filter(|(_, value)| !matches!(value, Self::Function(_)))
                    .map(|(key, value)| (key.to_owned(), value.to_json()))
                    .collect(),
            ),
        }
    }

    /// `structuredClone(value)`: fails on the first function encountered.
    pub(crate) fn structured_clone(&self) -> Result<Self, JsError> {
        match self {
            Self::Function(function) => Err(JsError::new(
                JsErrorKind::DataCloneError,
                format!("{} could not be cloned.", function.source()),
            )),
            Self::Array(items) => items
                .iter()
                .map(Self::structured_clone)
                .collect::<Result<_, _>>()
                .map(Self::Array),
            Self::Object(object) => {
                let mut clone = JsObject::default();
                for (key, value) in object.entries() {
                    clone.set(key, value.structured_clone()?);
                }
                Ok(Self::Object(clone))
            }
            Self::Null | Self::Bool(_) | Self::Number(_) | Self::String(_) => Ok(self.clone()),
        }
    }

    /// `typeof value === "object" && value !== null` (`Guard.IsObject`).
    pub(crate) fn is_object(&self) -> bool {
        matches!(self, Self::Array(_) | Self::Object(_))
    }

    /// `value.key` on a schema value read by validation.ts; `null` throws.
    /// Schema keywords never name `Object.prototype` members, so only own
    /// properties of plain objects are visible.
    pub(crate) fn get_keyword(&self, key: &str) -> Result<Option<&Self>, JsError> {
        match self {
            Self::Null => Err(JsError::type_error(format!(
                "Cannot read properties of null (reading '{key}')"
            ))),
            Self::Object(object) => Ok(object.get_own(key)),
            Self::Bool(_)
            | Self::Number(_)
            | Self::String(_)
            | Self::Array(_)
            | Self::Function(_) => Ok(None),
        }
    }

    /// JS truthiness.
    pub(crate) fn is_truthy(&self) -> bool {
        match self {
            Self::Null => false,
            Self::Bool(flag) => *flag,
            Self::Number(number) => *number != 0.0 && !number.is_nan(),
            Self::String(text) => !text.is_empty(),
            Self::Array(_) | Self::Object(_) | Self::Function(_) => true,
        }
    }

    /// `String(value)` for primitives (used in thrown messages).
    pub(crate) fn primitive_to_string(&self) -> String {
        match self {
            Self::Null => "null".to_owned(),
            Self::Bool(flag) => flag.to_string(),
            Self::Number(number) => number_to_js_string(*number),
            Self::String(text) => text.clone(),
            Self::Array(_) | Self::Object(_) => "[object Object]".to_owned(),
            Self::Function(function) => function.source(),
        }
    }
}

/// `left === right`. Objects and arrays never compare equal here: callers only
/// compare freshly produced primitives or values against schema constants.
#[allow(clippy::float_cmp)] // JS strict equality on numbers is exact (`-0 === 0`).
pub(crate) fn strict_equals(left: &JsValue, right: &JsValue) -> bool {
    match (left, right) {
        (JsValue::Null, JsValue::Null) => true,
        (JsValue::Bool(left), JsValue::Bool(right)) => left == right,
        (JsValue::Number(left), JsValue::Number(right)) => left == right,
        (JsValue::String(left), JsValue::String(right)) => left == right,
        (JsValue::Function(left), JsValue::Function(right)) => left == right,
        _ => false,
    }
}

/// `Number(text)`: ECMAScript `StringToNumber`.
pub(crate) fn string_to_number(text: &str) -> f64 {
    let trimmed = js_trim(text);
    if trimmed.is_empty() {
        return 0.0;
    }
    match trimmed {
        "Infinity" | "+Infinity" => return f64::INFINITY,
        "-Infinity" => return f64::NEG_INFINITY,
        _ => {}
    }
    let bytes = trimmed.as_bytes();
    if bytes.len() > 2 && bytes[0] == b'0' {
        let radix = match bytes[1] {
            b'x' | b'X' => Some(16),
            b'o' | b'O' => Some(8),
            b'b' | b'B' => Some(2),
            _ => None,
        };
        if let Some(radix) = radix {
            return parse_radix_integer(&trimmed[2..], radix);
        }
    }
    if !is_str_decimal_literal(trimmed) {
        return f64::NAN;
    }
    trimmed.parse::<f64>().unwrap_or(f64::NAN)
}

/// `StrUnsignedDecimalLiteral` with an optional sign (no `Infinity`, which
/// the caller handles): digits with an optional fraction and exponent.
fn is_str_decimal_literal(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut index = usize::from(matches!(bytes.first(), Some(b'+' | b'-')));
    let integer_start = index;
    while index < bytes.len() && bytes[index].is_ascii_digit() {
        index += 1;
    }
    let mut digits = index - integer_start;
    if index < bytes.len() && bytes[index] == b'.' {
        index += 1;
        let fraction_start = index;
        while index < bytes.len() && bytes[index].is_ascii_digit() {
            index += 1;
        }
        digits += index - fraction_start;
    }
    if digits == 0 {
        return false;
    }
    if index < bytes.len() && matches!(bytes[index], b'e' | b'E') {
        index += 1;
        if index < bytes.len() && matches!(bytes[index], b'+' | b'-') {
            index += 1;
        }
        let exponent_start = index;
        while index < bytes.len() && bytes[index].is_ascii_digit() {
            index += 1;
        }
        if index == exponent_start {
            return false;
        }
    }
    index == bytes.len()
}

/// `0x`/`0o`/`0b` literal digits (no sign, no separators), rounded once to
/// the nearest double like the spec's mathematical value.
fn parse_radix_integer(digits: &str, radix: u32) -> f64 {
    let mut exact: Option<u128> = Some(0);
    let mut approximate = 0.0_f64;
    for character in digits.chars() {
        let Some(digit) = character.to_digit(radix) else {
            return f64::NAN;
        };
        exact = exact
            .and_then(|value| value.checked_mul(u128::from(radix)))
            .and_then(|value| value.checked_add(u128::from(digit)));
        approximate = approximate * f64::from(radix) + f64::from(digit);
    }
    match exact {
        Some(value) => u128_to_f64(value),
        None => approximate,
    }
}

/// `value as f64`: rounds to the nearest double (ties to even).
#[allow(clippy::cast_precision_loss)] // Rounding is the intended JS number conversion.
fn u128_to_f64(value: u128) -> f64 {
    value as f64
}

/// A length or index as a JS number.
#[allow(clippy::cast_precision_loss)] // Lengths stay far below 2^53.
pub(crate) fn usize_to_f64(value: usize) -> f64 {
    value as f64
}

/// `Number.isInteger(value)`.
#[allow(clippy::float_cmp)] // An exact integrality test.
pub(crate) fn is_integer(value: f64) -> bool {
    value.is_finite() && value.trunc() == value
}

/// `Math.min` over three numbers: `NaN` if any operand is `NaN`.
pub(crate) fn js_min3(first: f64, second: f64, third: f64) -> f64 {
    if first.is_nan() || second.is_nan() || third.is_nan() {
        return f64::NAN;
    }
    first.min(second).min(third)
}

/// JS default `Array.prototype.sort` order for strings: UTF-16 code units.
pub(crate) fn compare_utf16(left: &str, right: &str) -> std::cmp::Ordering {
    left.encode_utf16().cmp(right.encode_utf16())
}

/// `decodeURIComponent(text)`.
pub(crate) fn decode_uri_component(text: &str) -> Result<String, JsError> {
    let malformed = || JsError::new(JsErrorKind::UriError, "URI malformed");
    let bytes = text.as_bytes();
    let mut decoded: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != b'%' {
            decoded.push(bytes[index]);
            index += 1;
            continue;
        }
        let byte = percent_byte(bytes, index).ok_or_else(malformed)?;
        index += 3;
        let continuation = match byte {
            0x00..=0x7F => 0,
            0xC2..=0xDF => 1,
            0xE0..=0xEF => 2,
            0xF0..=0xF4 => 3,
            _ => return Err(malformed()),
        };
        let mut sequence = vec![byte];
        for _ in 0..continuation {
            if bytes.get(index) != Some(&b'%') {
                return Err(malformed());
            }
            let next = percent_byte(bytes, index).ok_or_else(malformed)?;
            index += 3;
            sequence.push(next);
        }
        // Overlong forms, surrogates, and out-of-range scalars are rejected.
        let text = std::str::from_utf8(&sequence).map_err(|_| malformed())?;
        decoded.extend_from_slice(text.as_bytes());
    }
    String::from_utf8(decoded).map_err(|_| malformed())
}

fn percent_byte(bytes: &[u8], index: usize) -> Option<u8> {
    let high = char::from(*bytes.get(index + 1)?).to_digit(16)?;
    let low = char::from(*bytes.get(index + 2)?).to_digit(16)?;
    u8::try_from(high * 16 + low).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_to_number_matches_ecmascript() {
        let cases: [(&str, f64); 14] = [
            ("42", 42.0),
            (" 42 ", 42.0),
            ("4.5e1", 45.0),
            (".5", 0.5),
            ("5.", 5.0),
            ("+1", 1.0),
            ("-0", -0.0),
            ("0x10", 16.0),
            ("0b101", 5.0),
            ("0o17", 15.0),
            ("Infinity", f64::INFINITY),
            ("-Infinity", f64::NEG_INFINITY),
            ("", 0.0),
            ("\u{FEFF}7\n", 7.0),
        ];
        for (input, expected) in cases {
            assert_eq!(
                string_to_number(input).to_bits(),
                expected.to_bits(),
                "{input:?}"
            );
        }
        for input in [
            "abc", "1e", "-0x10", "1_000", "inf", "NaN", "0x", "1.2.3", "e5", ".",
        ] {
            assert!(string_to_number(input).is_nan(), "{input:?}");
        }
    }

    #[test]
    fn object_entries_list_array_index_keys_first() {
        let object: JsObject = [("b", 1.0), ("2", 2.0), ("a", 3.0), ("1", 4.0)]
            .into_iter()
            .map(|(key, value)| (key.to_owned(), JsValue::Number(value)))
            .collect();
        assert_eq!(object.keys(), vec!["1", "2", "b", "a"]);
    }

    #[test]
    fn has_property_key_sees_inherited_members_except_unsafe_keys() {
        let object = JsObject::default();
        assert!(object.has_property_key("toString"));
        assert!(!object.has_property_key("constructor"));
        assert!(!object.has_property_key("__proto__"));
        assert!(object.has_in("constructor"));
        assert!(!object.has_property_key("missing"));
    }

    #[test]
    fn decode_uri_component_rejects_malformed_sequences() {
        assert_eq!(decode_uri_component("%2Fa%20b").as_deref(), Ok("/a b"));
        assert_eq!(decode_uri_component("%C3%A9").as_deref(), Ok("é"));
        for input in ["%E0", "%zz", "%C3", "%ED%A0%80", "%"] {
            assert_eq!(
                decode_uri_component(input).map_err(|error| error.message),
                Err("URI malformed".to_owned()),
                "{input}"
            );
        }
    }

    #[test]
    fn structured_clone_rejects_functions() {
        let mut object = JsObject::default();
        object.set("toString", JsValue::Function(NativeFunction::ToString));
        let error = JsValue::Object(object)
            .structured_clone()
            .expect_err("functions are not cloneable");
        assert_eq!(
            error.message,
            "function toString() { [native code] } could not be cloned."
        );
    }
}
