//! serde integration: `Serialize`/`Deserialize` for [`JsonValue`] and the
//! typed-record conversions [`to_json`] / [`from_json`].

use std::fmt;
use std::sync::Arc;

use serde::de::{self, DeserializeOwned, MapAccess, SeqAccess, Visitor};
use serde::ser::{self, Impossible, Serialize, SerializeMap as _, SerializeSeq as _, Serializer};
use serde::{Deserialize, Deserializer};

use super::{JsonError, JsonNumber, JsonObject, JsonValue};

impl Serialize for JsonValue {
    /// Safe integers serialize as integers and other numbers as `f64`, so
    /// `serde_json` output matches `JSON.stringify` except for non-integral or
    /// unsafe-integer doubles outside `serde_json`'s decimal range; use
    /// `to_string()` (`Display`) for byte-exact `JSON.stringify` output.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Null => serializer.serialize_unit(),
            Self::Bool(flag) => serializer.serialize_bool(*flag),
            Self::Number(number) => match number.as_safe_integer() {
                Some(integer) => serializer.serialize_i64(integer),
                None => serializer.serialize_f64(number.get()),
            },
            Self::String(text) => serializer.serialize_str(text),
            Self::Array(items) => {
                let mut sequence = serializer.serialize_seq(Some(items.len()))?;
                for item in items.iter() {
                    sequence.serialize_element(item)?;
                }
                sequence.end()
            }
            Self::Object(object) => {
                let mut map = serializer.serialize_map(Some(object.len()))?;
                for (key, value) in object.iter() {
                    map.serialize_entry(key, value)?;
                }
                map.end()
            }
        }
    }
}

impl<'de> Deserialize<'de> for JsonValue {
    /// Accepts any JSON; rejects non-finite numbers. Duplicate object keys keep
    /// the first key's position and the last value, as `JSON.parse` does.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(ValueVisitor)
    }
}

struct ValueVisitor;

impl<'de> Visitor<'de> for ValueVisitor {
    type Value = JsonValue;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("strict JSON")
    }

    fn visit_bool<E: de::Error>(self, value: bool) -> Result<JsonValue, E> {
        Ok(JsonValue::Bool(value))
    }

    #[allow(clippy::cast_precision_loss)] // JSON.parse rounds integer literals to the nearest double
    fn visit_i64<E: de::Error>(self, value: i64) -> Result<JsonValue, E> {
        Ok(JsonValue::Number(
            JsonNumber::new(value as f64).unwrap_or_default(),
        ))
    }

    #[allow(clippy::cast_precision_loss)] // JSON.parse rounds integer literals to the nearest double
    fn visit_u64<E: de::Error>(self, value: u64) -> Result<JsonValue, E> {
        Ok(JsonValue::Number(
            JsonNumber::new(value as f64).unwrap_or_default(),
        ))
    }

    fn visit_f64<E: de::Error>(self, value: f64) -> Result<JsonValue, E> {
        JsonNumber::new(value)
            .map(JsonValue::Number)
            .ok_or_else(|| E::custom(JsonError::NonFinite))
    }

    fn visit_str<E: de::Error>(self, value: &str) -> Result<JsonValue, E> {
        Ok(JsonValue::String(Arc::from(value)))
    }

    fn visit_string<E: de::Error>(self, value: String) -> Result<JsonValue, E> {
        Ok(JsonValue::String(Arc::from(value)))
    }

    fn visit_unit<E: de::Error>(self) -> Result<JsonValue, E> {
        Ok(JsonValue::Null)
    }

    fn visit_none<E: de::Error>(self) -> Result<JsonValue, E> {
        Ok(JsonValue::Null)
    }

    fn visit_some<D: Deserializer<'de>>(self, deserializer: D) -> Result<JsonValue, D::Error> {
        JsonValue::deserialize(deserializer)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut access: A) -> Result<JsonValue, A::Error> {
        let mut items = Vec::with_capacity(access.size_hint().unwrap_or(0));
        while let Some(item) = access.next_element::<JsonValue>()? {
            items.push(item);
        }
        Ok(JsonValue::Array(Arc::new(items)))
    }

    fn visit_map<A: MapAccess<'de>>(self, mut access: A) -> Result<JsonValue, A::Error> {
        let mut object = JsonObject::with_capacity(access.size_hint().unwrap_or(0));
        while let Some((key, value)) = access.next_entry::<String, JsonValue>()? {
            object.insert(key, value);
        }
        Ok(JsonValue::Object(Arc::new(object)))
    }
}

/// Convert a typed record into a [`JsonValue`] (the Rust form of
/// `copyJson(record, { omitUndefinedProperties: true })`: `None` fields
/// skipped by `skip_serializing_if` are omitted). Struct fields keep
/// declaration order. Non-finite floats and integers beyond
/// `Number.MAX_SAFE_INTEGER` are rejected rather than coerced.
///
/// # Errors
///
/// [`JsonError`] when the value is not strict JSON or does not match the type.
pub fn to_json<T: Serialize + ?Sized>(value: &T) -> Result<JsonValue, JsonError> {
    value.serialize(ValueSerializer)
}

/// Convert a [`JsonValue`] into a typed record.
///
/// # Errors
///
/// [`JsonError`] when the value is not strict JSON or does not match the type.
pub fn from_json<T: DeserializeOwned>(value: &JsonValue) -> Result<T, JsonError> {
    serde_json::from_value(serde_json::Value::from(value)).map_err(JsonError::Deserialize)
}

impl ser::Error for JsonError {
    fn custom<T: fmt::Display>(message: T) -> Self {
        Self::Serialize(message.to_string())
    }
}

fn number(value: f64) -> Result<JsonValue, JsonError> {
    JsonNumber::new(value)
        .map(JsonValue::Number)
        .ok_or(JsonError::NonFinite)
}

#[allow(clippy::cast_precision_loss)] // bounded by MAX_SAFE_INTEGER: exact
fn safe_integer(value: i128) -> Result<JsonValue, JsonError> {
    if value.unsigned_abs() > 9_007_199_254_740_991 {
        return Err(JsonError::UnsafeInteger);
    }
    number(value as f64)
}

fn wrap_variant(variant: &str, value: JsonValue) -> JsonValue {
    let mut object = JsonObject::new();
    object.insert(variant, value);
    JsonValue::Object(Arc::new(object))
}

struct ValueSerializer;

impl Serializer for ValueSerializer {
    type Ok = JsonValue;
    type Error = JsonError;
    type SerializeSeq = SeqBuilder;
    type SerializeTuple = SeqBuilder;
    type SerializeTupleStruct = SeqBuilder;
    type SerializeTupleVariant = SeqBuilder;
    type SerializeMap = MapBuilder;
    type SerializeStruct = MapBuilder;
    type SerializeStructVariant = MapBuilder;

    fn serialize_bool(self, value: bool) -> Result<JsonValue, JsonError> {
        Ok(JsonValue::Bool(value))
    }
    fn serialize_i8(self, value: i8) -> Result<JsonValue, JsonError> {
        safe_integer(value.into())
    }
    fn serialize_i16(self, value: i16) -> Result<JsonValue, JsonError> {
        safe_integer(value.into())
    }
    fn serialize_i32(self, value: i32) -> Result<JsonValue, JsonError> {
        safe_integer(value.into())
    }
    fn serialize_i64(self, value: i64) -> Result<JsonValue, JsonError> {
        safe_integer(value.into())
    }
    fn serialize_i128(self, value: i128) -> Result<JsonValue, JsonError> {
        safe_integer(value)
    }
    fn serialize_u8(self, value: u8) -> Result<JsonValue, JsonError> {
        safe_integer(value.into())
    }
    fn serialize_u16(self, value: u16) -> Result<JsonValue, JsonError> {
        safe_integer(value.into())
    }
    fn serialize_u32(self, value: u32) -> Result<JsonValue, JsonError> {
        safe_integer(value.into())
    }
    fn serialize_u64(self, value: u64) -> Result<JsonValue, JsonError> {
        safe_integer(value.into())
    }
    fn serialize_u128(self, value: u128) -> Result<JsonValue, JsonError> {
        safe_integer(i128::try_from(value).map_err(|_| JsonError::UnsafeInteger)?)
    }
    fn serialize_f32(self, value: f32) -> Result<JsonValue, JsonError> {
        number(value.into())
    }
    fn serialize_f64(self, value: f64) -> Result<JsonValue, JsonError> {
        number(value)
    }
    fn serialize_char(self, value: char) -> Result<JsonValue, JsonError> {
        Ok(JsonValue::from(value.to_string()))
    }
    fn serialize_str(self, value: &str) -> Result<JsonValue, JsonError> {
        Ok(JsonValue::from(value))
    }
    fn serialize_bytes(self, value: &[u8]) -> Result<JsonValue, JsonError> {
        Ok(JsonValue::Array(Arc::new(
            value.iter().map(|byte| JsonValue::from(*byte)).collect(),
        )))
    }
    fn serialize_none(self) -> Result<JsonValue, JsonError> {
        Ok(JsonValue::Null)
    }
    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<JsonValue, JsonError> {
        value.serialize(self)
    }
    fn serialize_unit(self) -> Result<JsonValue, JsonError> {
        Ok(JsonValue::Null)
    }
    fn serialize_unit_struct(self, _name: &'static str) -> Result<JsonValue, JsonError> {
        Ok(JsonValue::Null)
    }
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
    ) -> Result<JsonValue, JsonError> {
        Ok(JsonValue::from(variant))
    }
    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<JsonValue, JsonError> {
        value.serialize(self)
    }
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<JsonValue, JsonError> {
        Ok(wrap_variant(variant, value.serialize(self)?))
    }
    fn serialize_seq(self, length: Option<usize>) -> Result<SeqBuilder, JsonError> {
        Ok(SeqBuilder {
            items: Vec::with_capacity(length.unwrap_or(0)),
            variant: None,
        })
    }
    fn serialize_tuple(self, length: usize) -> Result<SeqBuilder, JsonError> {
        self.serialize_seq(Some(length))
    }
    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        length: usize,
    ) -> Result<SeqBuilder, JsonError> {
        self.serialize_seq(Some(length))
    }
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        length: usize,
    ) -> Result<SeqBuilder, JsonError> {
        Ok(SeqBuilder {
            items: Vec::with_capacity(length),
            variant: Some(variant),
        })
    }
    fn serialize_map(self, length: Option<usize>) -> Result<MapBuilder, JsonError> {
        Ok(MapBuilder {
            object: JsonObject::with_capacity(length.unwrap_or(0)),
            key: None,
            variant: None,
        })
    }
    fn serialize_struct(self, _name: &'static str, length: usize) -> Result<MapBuilder, JsonError> {
        self.serialize_map(Some(length))
    }
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        length: usize,
    ) -> Result<MapBuilder, JsonError> {
        Ok(MapBuilder {
            object: JsonObject::with_capacity(length),
            key: None,
            variant: Some(variant),
        })
    }
}

struct SeqBuilder {
    items: Vec<JsonValue>,
    variant: Option<&'static str>,
}

impl SeqBuilder {
    fn push<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), JsonError> {
        self.items.push(value.serialize(ValueSerializer)?);
        Ok(())
    }

    fn finish(self) -> JsonValue {
        let array = JsonValue::Array(Arc::new(self.items));
        match self.variant {
            Some(variant) => wrap_variant(variant, array),
            None => array,
        }
    }
}

impl ser::SerializeSeq for SeqBuilder {
    type Ok = JsonValue;
    type Error = JsonError;
    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), JsonError> {
        self.push(value)
    }
    fn end(self) -> Result<JsonValue, JsonError> {
        Ok(self.finish())
    }
}

impl ser::SerializeTuple for SeqBuilder {
    type Ok = JsonValue;
    type Error = JsonError;
    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), JsonError> {
        self.push(value)
    }
    fn end(self) -> Result<JsonValue, JsonError> {
        Ok(self.finish())
    }
}

impl ser::SerializeTupleStruct for SeqBuilder {
    type Ok = JsonValue;
    type Error = JsonError;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), JsonError> {
        self.push(value)
    }
    fn end(self) -> Result<JsonValue, JsonError> {
        Ok(self.finish())
    }
}

impl ser::SerializeTupleVariant for SeqBuilder {
    type Ok = JsonValue;
    type Error = JsonError;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), JsonError> {
        self.push(value)
    }
    fn end(self) -> Result<JsonValue, JsonError> {
        Ok(self.finish())
    }
}

struct MapBuilder {
    object: JsonObject,
    key: Option<String>,
    variant: Option<&'static str>,
}

impl MapBuilder {
    fn finish(self) -> JsonValue {
        let object = JsonValue::Object(Arc::new(self.object));
        match self.variant {
            Some(variant) => wrap_variant(variant, object),
            None => object,
        }
    }
}

impl ser::SerializeMap for MapBuilder {
    type Ok = JsonValue;
    type Error = JsonError;
    fn serialize_key<T: Serialize + ?Sized>(&mut self, key: &T) -> Result<(), JsonError> {
        self.key = Some(key.serialize(KeySerializer)?);
        Ok(())
    }
    fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), JsonError> {
        let key = self.key.take().ok_or_else(|| {
            JsonError::Serialize("map value serialized before its key".to_owned())
        })?;
        self.object.insert(key, value.serialize(ValueSerializer)?);
        Ok(())
    }
    fn end(self) -> Result<JsonValue, JsonError> {
        Ok(self.finish())
    }
}

impl ser::SerializeStruct for MapBuilder {
    type Ok = JsonValue;
    type Error = JsonError;
    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), JsonError> {
        self.object.insert(key, value.serialize(ValueSerializer)?);
        Ok(())
    }
    fn end(self) -> Result<JsonValue, JsonError> {
        Ok(self.finish())
    }
}

impl ser::SerializeStructVariant for MapBuilder {
    type Ok = JsonValue;
    type Error = JsonError;
    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), JsonError> {
        self.object.insert(key, value.serialize(ValueSerializer)?);
        Ok(())
    }
    fn end(self) -> Result<JsonValue, JsonError> {
        Ok(self.finish())
    }
}

/// Map keys: strings, and integers/booleans/chars rendered as their text (as
/// `serde_json` does).
struct KeySerializer;

fn key_error() -> JsonError {
    JsonError::Serialize("map keys must be strings".to_owned())
}

impl Serializer for KeySerializer {
    type Ok = String;
    type Error = JsonError;
    type SerializeSeq = Impossible<String, JsonError>;
    type SerializeTuple = Impossible<String, JsonError>;
    type SerializeTupleStruct = Impossible<String, JsonError>;
    type SerializeTupleVariant = Impossible<String, JsonError>;
    type SerializeMap = Impossible<String, JsonError>;
    type SerializeStruct = Impossible<String, JsonError>;
    type SerializeStructVariant = Impossible<String, JsonError>;

    fn serialize_bool(self, value: bool) -> Result<String, JsonError> {
        Ok(value.to_string())
    }
    fn serialize_i8(self, value: i8) -> Result<String, JsonError> {
        Ok(value.to_string())
    }
    fn serialize_i16(self, value: i16) -> Result<String, JsonError> {
        Ok(value.to_string())
    }
    fn serialize_i32(self, value: i32) -> Result<String, JsonError> {
        Ok(value.to_string())
    }
    fn serialize_i64(self, value: i64) -> Result<String, JsonError> {
        Ok(value.to_string())
    }
    fn serialize_u8(self, value: u8) -> Result<String, JsonError> {
        Ok(value.to_string())
    }
    fn serialize_u16(self, value: u16) -> Result<String, JsonError> {
        Ok(value.to_string())
    }
    fn serialize_u32(self, value: u32) -> Result<String, JsonError> {
        Ok(value.to_string())
    }
    fn serialize_u64(self, value: u64) -> Result<String, JsonError> {
        Ok(value.to_string())
    }
    fn serialize_f32(self, _value: f32) -> Result<String, JsonError> {
        Err(key_error())
    }
    fn serialize_f64(self, _value: f64) -> Result<String, JsonError> {
        Err(key_error())
    }
    fn serialize_char(self, value: char) -> Result<String, JsonError> {
        Ok(value.to_string())
    }
    fn serialize_str(self, value: &str) -> Result<String, JsonError> {
        Ok(value.to_owned())
    }
    fn serialize_bytes(self, _value: &[u8]) -> Result<String, JsonError> {
        Err(key_error())
    }
    fn serialize_none(self) -> Result<String, JsonError> {
        Err(key_error())
    }
    fn serialize_some<T: Serialize + ?Sized>(self, _value: &T) -> Result<String, JsonError> {
        Err(key_error())
    }
    fn serialize_unit(self) -> Result<String, JsonError> {
        Err(key_error())
    }
    fn serialize_unit_struct(self, _name: &'static str) -> Result<String, JsonError> {
        Err(key_error())
    }
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
    ) -> Result<String, JsonError> {
        Ok(variant.to_owned())
    }
    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<String, JsonError> {
        value.serialize(self)
    }
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> Result<String, JsonError> {
        Err(key_error())
    }
    fn serialize_seq(self, _length: Option<usize>) -> Result<Self::SerializeSeq, JsonError> {
        Err(key_error())
    }
    fn serialize_tuple(self, _length: usize) -> Result<Self::SerializeTuple, JsonError> {
        Err(key_error())
    }
    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _length: usize,
    ) -> Result<Self::SerializeTupleStruct, JsonError> {
        Err(key_error())
    }
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _index: u32,
        _variant: &'static str,
        _length: usize,
    ) -> Result<Self::SerializeTupleVariant, JsonError> {
        Err(key_error())
    }
    fn serialize_map(self, _length: Option<usize>) -> Result<Self::SerializeMap, JsonError> {
        Err(key_error())
    }
    fn serialize_struct(
        self,
        _name: &'static str,
        _length: usize,
    ) -> Result<Self::SerializeStruct, JsonError> {
        Err(key_error())
    }
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _index: u32,
        _variant: &'static str,
        _length: usize,
    ) -> Result<Self::SerializeStructVariant, JsonError> {
        Err(key_error())
    }
}

/// `serde_json::Value` → [`JsonValue`]. Every `serde_json` number is a finite
/// double, `i64`, or `u64` (no `arbitrary_precision` in this workspace);
/// integers beyond 2^53 round to the nearest double as `JSON.parse` does.
impl From<serde_json::Value> for JsonValue {
    fn from(value: serde_json::Value) -> Self {
        Self::from(&value)
    }
}

impl From<&serde_json::Value> for JsonValue {
    fn from(value: &serde_json::Value) -> Self {
        match value {
            serde_json::Value::Null => Self::Null,
            serde_json::Value::Bool(flag) => Self::Bool(*flag),
            serde_json::Value::Number(number) => Self::Number(
                number
                    .as_f64()
                    .and_then(JsonNumber::new)
                    .unwrap_or_default(),
            ),
            serde_json::Value::String(text) => Self::String(Arc::from(text.as_str())),
            serde_json::Value::Array(items) => {
                Self::Array(Arc::new(items.iter().map(Self::from).collect()))
            }
            serde_json::Value::Object(map) => Self::Object(Arc::new(
                map.iter()
                    .map(|(key, value)| (key.as_str(), Self::from(value)))
                    .collect(),
            )),
        }
    }
}

/// [`JsonValue`] → `serde_json::Value`: safe integers become integer numbers,
/// other numbers `f64`; object keys keep JS order.
impl From<&JsonValue> for serde_json::Value {
    fn from(value: &JsonValue) -> Self {
        match value {
            JsonValue::Null => Self::Null,
            JsonValue::Bool(flag) => Self::Bool(*flag),
            JsonValue::Number(number) => match number.as_safe_integer() {
                Some(integer) => Self::Number(integer.into()),
                None => serde_json::Number::from_f64(number.get()).map_or(Self::Null, Self::Number),
            },
            JsonValue::String(text) => Self::String(text.to_string()),
            JsonValue::Array(items) => Self::Array(items.iter().map(Self::from).collect()),
            JsonValue::Object(object) => Self::Object(
                object
                    .iter()
                    .map(|(key, value)| (key.to_owned(), Self::from(value)))
                    .collect(),
            ),
        }
    }
}

impl From<JsonValue> for serde_json::Value {
    fn from(value: JsonValue) -> Self {
        Self::from(&value)
    }
}
