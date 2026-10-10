//! `TypeBox` 1.3.27 schema builder (TS `import { Type } from "typebox"`, which
//! pi-ai re-exports).
//!
//! Every builder returns a [`TSchema`]: the JSON Schema `TypeBox` serializes
//! (`JSON.stringify(Type.X(..))`, key order included) together with the
//! non-enumerable markers `TypeBox` attaches to each node (`~kind`,
//! `~optional`, `~readonly`, `~unsafe`). Tool parameters built here
//! (`TSchema` → [`ToolSchema`]) validate exactly like the TS ones:
//! `validate_tool_arguments` runs `Value.Convert` on them (`Type::integer()`
//! turns `"42"` into `42`), and not on plain JSON schemas.
//!
//! Options are the TS option objects (`{ description, minLength, ... }`) as a
//! [`JsonObject`]; they are merged after the builder's own keys, like
//! `{ ...schema, ...options }`.
//!
//! ```
//! use eukhe_pi_ai::typebox::Type;
//! use serde_json::json;
//!
//! let schema = Type::object([
//!     ("path", Type::string()),
//!     ("offset", Type::optional(Type::integer())),
//! ]);
//! assert_eq!(
//!     schema.json(),
//!     &json!({
//!         "type": "object",
//!         "required": ["path"],
//!         "properties": { "path": { "type": "string" }, "offset": { "type": "integer" } }
//!     })
//! );
//! ```

pub(crate) mod algebra;
#[cfg(test)]
mod tests;

use eukhe_types::pi_ai::{JsonObject, JsonValue, ToolSchema};

use crate::utils::js::js_number_value;

/// `TypeBox` schema options (`{ description, default, minLength, ... }`):
/// JSON values, or schemas for the options that hold one
/// (`additionalProperties: Type.Integer()`), in insertion order.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Options {
    entries: Vec<(String, OptionValue)>,
}

#[derive(Debug, Clone, PartialEq)]
enum OptionValue {
    Json(JsonValue),
    Schema(TSchema),
}

impl Options {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets a JSON option (`{ ...options, [key]: value }`).
    #[must_use]
    pub fn set(self, key: impl Into<String>, value: impl Into<JsonValue>) -> Self {
        self.with(key.into(), OptionValue::Json(value.into()))
    }

    /// Sets a schema-valued option, keeping its `TypeBox` markers.
    #[must_use]
    pub fn schema(self, key: impl Into<String>, schema: TSchema) -> Self {
        self.with(key.into(), OptionValue::Schema(schema))
    }

    fn with(mut self, key: String, value: OptionValue) -> Self {
        match self.entries.iter_mut().find(|(name, _)| *name == key) {
            Some((_, slot)) => *slot = value,
            None => self.entries.push((key, value)),
        }
        self
    }

    /// The options as serialized and with schema markers, in JS key order.
    fn into_parts(self) -> (JsonObject, JsonObject) {
        (self.json(), self.view())
    }

    /// The options as serialized, in JS object key order.
    fn json(&self) -> JsonObject {
        algebra::js_ordered(
            self.entries
                .iter()
                .map(|(key, value)| {
                    let value = match value {
                        OptionValue::Json(value) => js_ordered_deep(value),
                        OptionValue::Schema(schema) => schema.json.clone(),
                    };
                    (key.clone(), value)
                })
                .collect(),
        )
    }

    /// The options with schema values' markers.
    fn view(&self) -> JsonObject {
        algebra::js_ordered(
            self.entries
                .iter()
                .map(|(key, value)| {
                    let value = match value {
                        OptionValue::Json(value) => js_ordered_deep(value),
                        OptionValue::Schema(schema) => schema.view.clone(),
                    };
                    (key.clone(), value)
                })
                .collect(),
        )
    }
}

/// Options from a JSON object (no schema-valued options; use [`Options::schema`]).
impl From<JsonObject> for Options {
    fn from(options: JsonObject) -> Self {
        Self {
            entries: options
                .into_iter()
                .map(|(key, value)| (key, OptionValue::Json(value)))
                .collect(),
        }
    }
}

/// A `TypeBox` schema: wire JSON plus `TypeBox`'s hidden markers.
#[derive(Debug, Clone, PartialEq)]
pub struct TSchema {
    json: JsonValue,
    view: JsonValue,
}

impl TSchema {
    /// The serialized schema (`JSON.parse(JSON.stringify(schema))`).
    #[must_use]
    pub fn json(&self) -> &JsonValue {
        &self.json
    }

    /// The schema with its non-enumerable markers as keys.
    #[must_use]
    pub fn typebox(&self) -> &JsonValue {
        &self.view
    }
}

impl From<TSchema> for ToolSchema {
    fn from(schema: TSchema) -> Self {
        ToolSchema::from_typebox(schema.json, schema.view)
    }
}

/// A `Type.Literal` value.
#[derive(Debug, Clone, PartialEq)]
pub enum LiteralValue {
    String(String),
    Number(f64),
    Boolean(bool),
}

impl LiteralValue {
    fn to_json(&self) -> JsonValue {
        match self {
            Self::String(text) => JsonValue::String(text.clone()),
            Self::Number(number) => js_number_value(*number),
            Self::Boolean(flag) => JsonValue::Bool(*flag),
        }
    }
}

impl From<&str> for LiteralValue {
    fn from(value: &str) -> Self {
        Self::String(value.to_owned())
    }
}

impl From<String> for LiteralValue {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<f64> for LiteralValue {
    fn from(value: f64) -> Self {
        Self::Number(value)
    }
}

impl From<i32> for LiteralValue {
    fn from(value: i32) -> Self {
        Self::Number(f64::from(value))
    }
}

impl From<bool> for LiteralValue {
    fn from(value: bool) -> Self {
        Self::Boolean(value)
    }
}

/// A `Type.Enum` value (`string | number`).
#[derive(Debug, Clone, PartialEq)]
pub enum EnumValue {
    String(String),
    Number(f64),
}

impl EnumValue {
    fn to_json(&self) -> JsonValue {
        match self {
            Self::String(text) => JsonValue::String(text.clone()),
            Self::Number(number) => js_number_value(*number),
        }
    }
}

impl From<&str> for EnumValue {
    fn from(value: &str) -> Self {
        Self::String(value.to_owned())
    }
}

impl From<String> for EnumValue {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<f64> for EnumValue {
    fn from(value: f64) -> Self {
        Self::Number(value)
    }
}

impl From<i32> for EnumValue {
    fn from(value: i32) -> Self {
        Self::Number(f64::from(value))
    }
}

/// JS object literal key order at every level of a JSON value.
fn js_ordered_deep(value: &JsonValue) -> JsonValue {
    match value {
        JsonValue::Object(map) => JsonValue::Object(algebra::js_ordered(
            map.iter()
                .map(|(key, value)| (key.clone(), js_ordered_deep(value)))
                .collect(),
        )),
        JsonValue::Array(items) => JsonValue::Array(items.iter().map(js_ordered_deep).collect()),
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::String(_) => {
            value.clone()
        }
    }
}

/// One enumerable field of a node under construction.
enum Part {
    Json(JsonValue),
    Schema(TSchema),
    Schemas(Vec<TSchema>),
    Properties(Vec<(String, TSchema)>),
}

impl Part {
    fn json(&self) -> JsonValue {
        match self {
            Self::Json(value) => value.clone(),
            Self::Schema(schema) => schema.json.clone(),
            Self::Schemas(schemas) => {
                JsonValue::Array(schemas.iter().map(|schema| schema.json.clone()).collect())
            }
            Self::Properties(properties) => JsonValue::Object(algebra::js_ordered(
                properties
                    .iter()
                    .map(|(key, schema)| (key.clone(), schema.json.clone()))
                    .collect(),
            )),
        }
    }

    fn view(&self) -> JsonValue {
        match self {
            Self::Json(value) => value.clone(),
            Self::Schema(schema) => schema.view.clone(),
            Self::Schemas(schemas) => {
                JsonValue::Array(schemas.iter().map(|schema| schema.view.clone()).collect())
            }
            Self::Properties(properties) => JsonValue::Object(algebra::js_ordered(
                properties
                    .iter()
                    .map(|(key, schema)| (key.clone(), schema.view.clone()))
                    .collect(),
            )),
        }
    }
}

/// `Memory.Create({ '~kind': kind }, parts, options)`.
fn create(kind: &str, parts: &[(&str, Part)], options: Options) -> TSchema {
    let (options_json, options_view) = options.into_parts();
    let json_fields: JsonObject = parts
        .iter()
        .map(|(key, part)| ((*key).to_owned(), part.json()))
        .collect();
    let view_fields: JsonObject = parts
        .iter()
        .map(|(key, part)| ((*key).to_owned(), part.view()))
        .collect();
    TSchema {
        json: JsonValue::Object(algebra::merge_options(json_fields, &options_json)),
        view: algebra::create(kind, view_fields, &options_view),
    }
}

/// `Memory.Update(schema, hidden, options)`.
fn update(schema: TSchema, hidden: &[(&str, JsonValue)], options: Options) -> TSchema {
    let (options_json, options_view) = options.into_parts();
    let TSchema { json, view } = schema;
    TSchema {
        json: algebra::update(&json, &[], &options_json),
        view: algebra::update(&view, hidden, &options_view),
    }
}

fn type_name(name: &str) -> Part {
    Part::Json(JsonValue::String(name.to_owned()))
}

const STRING_KEY: &str = "^.*$";
const NUMBER_KEY: &str = "^-?(?:0|[1-9][0-9]*)(?:\\.[0-9]+)?$";
const INTEGER_KEY: &str = "^-?(?:0|[1-9][0-9]*)$";

/// `CreateRecord(pattern, value)`.
fn create_record(pattern: &str, value: TSchema) -> TSchema {
    let pattern_properties = Part::Properties(vec![(pattern.to_owned(), value)]);
    create(
        "Record",
        &[
            ("type", type_name("object")),
            ("patternProperties", pattern_properties),
        ],
        Options::new(),
    )
}

/// `FromKey(key, value)`: the record shape for a key type.
fn record_from_key(key: &JsonValue, value: TSchema) -> TSchema {
    let object_of = |keys: Vec<String>, value: TSchema| {
        Type::object(keys.into_iter().map(|key| (key, value.clone())))
    };
    match algebra::kind(key) {
        Some("Any") => create_record(STRING_KEY, value),
        Some("Boolean") => object_of(vec!["true".to_owned(), "false".to_owned()], value),
        Some("Enum" | "Intersect") => {
            let evaluated = algebra::evaluate_type(key)
                .expect("builder enums hold only string and number values");
            record_from_key(&evaluated, value)
        }
        Some("Integer") => create_record(INTEGER_KEY, value),
        Some("Literal") => match key.get("const") {
            Some(constant @ (JsonValue::String(_) | JsonValue::Number(_) | JsonValue::Bool(_))) => {
                object_of(algebra::property_key(constant).into_iter().collect(), value)
            }
            _ => object_of(Vec::new(), value),
        },
        Some("Number") => create_record(NUMBER_KEY, value),
        Some("Union") => {
            let members = flatten(
                key.get("anyOf")
                    .and_then(JsonValue::as_array)
                    .map_or(&[][..], Vec::as_slice),
            );
            if members.iter().any(|member| {
                matches!(algebra::kind(member), Some("String" | "Number" | "Integer"))
            }) {
                return create_record(STRING_KEY, value);
            }
            let mut keys: Vec<String> = Vec::new();
            for member in &members {
                if algebra::is_kind(member, "Literal") {
                    if let Some(constant @ (JsonValue::String(_) | JsonValue::Number(_))) =
                        member.get("const")
                    {
                        if let Some(name) =
                            algebra::property_key(constant).filter(|name| !keys.contains(name))
                        {
                            keys.push(name);
                        }
                    }
                }
            }
            object_of(keys, value)
        }
        Some("String") => match key.get("pattern") {
            Some(JsonValue::String(pattern)) => create_record(pattern, value),
            _ => create_record(STRING_KEY, value),
        },
        _ => object_of(Vec::new(), value),
    }
}

fn flatten(types: &[JsonValue]) -> Vec<JsonValue> {
    let mut result = Vec::new();
    for member in types {
        if algebra::is_kind(member, "Union") {
            result.extend(flatten(
                member
                    .get("anyOf")
                    .and_then(JsonValue::as_array)
                    .map_or(&[][..], Vec::as_slice),
            ));
        } else {
            result.push(member.clone());
        }
    }
    result
}

/// The `TypeBox` `Type` namespace. `*_with` variants take the TS options.
pub struct Type;

impl Type {
    /// `Type.Object(properties)`.
    pub fn object<K: Into<String>>(properties: impl IntoIterator<Item = (K, TSchema)>) -> TSchema {
        Self::object_with(properties, Options::new())
    }

    /// `Type.Object(properties, options)`: `required` lists the properties
    /// not wrapped in [`Type::optional`].
    pub fn object_with<K: Into<String>>(
        properties: impl IntoIterator<Item = (K, TSchema)>,
        options: Options,
    ) -> TSchema {
        let properties: Vec<(String, TSchema)> = properties
            .into_iter()
            .map(|(key, schema)| (key.into(), schema))
            .collect();
        let ordered = algebra::js_ordered(
            properties
                .iter()
                .map(|(key, schema)| (key.clone(), schema.view.clone()))
                .collect(),
        );
        let required: Vec<JsonValue> = ordered
            .iter()
            .filter(|(_, view)| !algebra::is_optional(view))
            .map(|(key, _)| JsonValue::String(key.clone()))
            .collect();
        let mut parts = vec![("type", type_name("object"))];
        if !required.is_empty() {
            parts.push(("required", Part::Json(JsonValue::Array(required))));
        }
        parts.push(("properties", Part::Properties(properties)));
        create("Object", &parts, options)
    }

    #[must_use]
    pub fn string() -> TSchema {
        Self::string_with(Options::new())
    }

    #[must_use]
    pub fn string_with(options: Options) -> TSchema {
        create("String", &[("type", type_name("string"))], options)
    }

    #[must_use]
    pub fn number() -> TSchema {
        Self::number_with(Options::new())
    }

    #[must_use]
    pub fn number_with(options: Options) -> TSchema {
        create("Number", &[("type", type_name("number"))], options)
    }

    #[must_use]
    pub fn integer() -> TSchema {
        Self::integer_with(Options::new())
    }

    #[must_use]
    pub fn integer_with(options: Options) -> TSchema {
        create("Integer", &[("type", type_name("integer"))], options)
    }

    #[must_use]
    pub fn boolean() -> TSchema {
        Self::boolean_with(Options::new())
    }

    #[must_use]
    pub fn boolean_with(options: Options) -> TSchema {
        create("Boolean", &[("type", type_name("boolean"))], options)
    }

    #[must_use]
    pub fn null() -> TSchema {
        Self::null_with(Options::new())
    }

    #[must_use]
    pub fn null_with(options: Options) -> TSchema {
        create("Null", &[("type", type_name("null"))], options)
    }

    /// `Type.Literal(value)`.
    pub fn literal(value: impl Into<LiteralValue>) -> TSchema {
        Self::literal_with(value, Options::new())
    }

    pub fn literal_with(value: impl Into<LiteralValue>, options: Options) -> TSchema {
        let value = value.into();
        let name = match value {
            LiteralValue::String(_) => "string",
            LiteralValue::Number(_) => "number",
            LiteralValue::Boolean(_) => "boolean",
        };
        create(
            "Literal",
            &[
                ("type", type_name(name)),
                ("const", Part::Json(value.to_json())),
            ],
            options,
        )
    }

    /// `Type.Union(types)`.
    pub fn union(types: impl IntoIterator<Item = TSchema>) -> TSchema {
        Self::union_with(types, Options::new())
    }

    pub fn union_with(types: impl IntoIterator<Item = TSchema>, options: Options) -> TSchema {
        create(
            "Union",
            &[("anyOf", Part::Schemas(types.into_iter().collect()))],
            options,
        )
    }

    /// `Type.Intersect(types)`.
    pub fn intersect(types: impl IntoIterator<Item = TSchema>) -> TSchema {
        Self::intersect_with(types, Options::new())
    }

    pub fn intersect_with(types: impl IntoIterator<Item = TSchema>, options: Options) -> TSchema {
        create(
            "Intersect",
            &[("allOf", Part::Schemas(types.into_iter().collect()))],
            options,
        )
    }

    /// `Type.Array(items)`.
    #[must_use]
    pub fn array(items: TSchema) -> TSchema {
        Self::array_with(items, Options::new())
    }

    #[must_use]
    pub fn array_with(items: TSchema, options: Options) -> TSchema {
        create(
            "Array",
            &[("type", type_name("array")), ("items", Part::Schema(items))],
            options,
        )
    }

    /// `Type.Tuple(types)`: `items` with `additionalItems: false` and `minItems`.
    pub fn tuple(types: impl IntoIterator<Item = TSchema>) -> TSchema {
        Self::tuple_with(types, Options::new())
    }

    pub fn tuple_with(types: impl IntoIterator<Item = TSchema>, options: Options) -> TSchema {
        let types: Vec<TSchema> = types.into_iter().collect();
        let length = types.len();
        create(
            "Tuple",
            &[
                ("type", type_name("array")),
                ("additionalItems", Part::Json(JsonValue::Bool(false))),
                ("items", Part::Schemas(types)),
                ("minItems", Part::Json(JsonValue::from(length))),
            ],
            options,
        )
    }

    /// `Type.Record(key, value)`: `patternProperties` for `String`/`Number`/
    /// `Integer`/`Any` keys (a `String` key's `pattern` becomes the pattern),
    /// an object with required properties for literal keys and unions of
    /// literals, as `TypeBox` derives it.
    #[must_use]
    pub fn record(key: TSchema, value: TSchema) -> TSchema {
        Self::record_with(key, value, Options::new())
    }

    /// # Panics
    ///
    /// Never for builder-made keys: `Enum`/`Intersect` keys are evaluated, and
    /// builder enums only hold string and number values.
    #[must_use]
    pub fn record_with(key: TSchema, value: TSchema, options: Options) -> TSchema {
        let TSchema { view, .. } = key;
        update(record_from_key(&view, value), &[], options)
    }

    /// `Type.Enum(values)`.
    pub fn enum_(values: impl IntoIterator<Item = impl Into<EnumValue>>) -> TSchema {
        Self::enum_with(values, Options::new())
    }

    pub fn enum_with(
        values: impl IntoIterator<Item = impl Into<EnumValue>>,
        options: Options,
    ) -> TSchema {
        let values: Vec<JsonValue> = values
            .into_iter()
            .map(|value| value.into().to_json())
            .collect();
        create(
            "Enum",
            &[("enum", Part::Json(JsonValue::Array(values)))],
            options,
        )
    }

    /// `Type.Unsafe(schema)`: the schema as given (`Value.Convert` leaves it alone).
    #[must_use]
    pub fn unsafe_(schema: JsonObject) -> TSchema {
        let schema = JsonValue::Object(schema);
        let plain = TSchema {
            json: schema.clone(),
            view: schema,
        };
        update(plain, &[("~unsafe", JsonValue::Null)], Options::new())
    }

    #[must_use]
    pub fn any() -> TSchema {
        Self::any_with(Options::new())
    }

    #[must_use]
    pub fn any_with(options: Options) -> TSchema {
        create("Any", &[], options)
    }

    #[must_use]
    pub fn unknown() -> TSchema {
        Self::unknown_with(Options::new())
    }

    #[must_use]
    pub fn unknown_with(options: Options) -> TSchema {
        create("Unknown", &[], options)
    }

    #[must_use]
    pub fn never() -> TSchema {
        Self::never_with(Options::new())
    }

    #[must_use]
    pub fn never_with(options: Options) -> TSchema {
        create(
            "Never",
            &[("not", Part::Json(JsonValue::Object(JsonObject::new())))],
            options,
        )
    }

    /// `Type.Optional(type)`: an optional object property.
    #[must_use]
    pub fn optional(schema: TSchema) -> TSchema {
        update(
            schema,
            &[("~optional", JsonValue::Bool(true))],
            Options::new(),
        )
    }

    /// `Type.Readonly(type)`: a readonly object property.
    #[must_use]
    pub fn readonly(schema: TSchema) -> TSchema {
        update(
            schema,
            &[("~readonly", JsonValue::Bool(true))],
            Options::new(),
        )
    }

    /// `Type.Partial(type)`.
    #[must_use]
    pub fn partial(schema: TSchema) -> TSchema {
        Self::partial_with(schema, Options::new())
    }

    /// `Type.Partial(type, options)`: an `Object` with every property made
    /// optional (so no `required`), keeping its other keys and merging
    /// `options`. Non-object types only take the options.
    #[must_use]
    pub fn partial_with(schema: TSchema, options: Options) -> TSchema {
        if !algebra::is_kind(&schema.view, "Object") {
            return update(schema, &[], options);
        }
        let empty = JsonObject::new();
        let json_properties = schema
            .json
            .get("properties")
            .and_then(JsonValue::as_object)
            .unwrap_or(&empty);
        let view_properties = schema
            .view
            .get("properties")
            .and_then(JsonValue::as_object)
            .unwrap_or(&empty);
        let properties: Vec<(String, TSchema)> = view_properties
            .iter()
            .map(|(key, view)| {
                let property = TSchema {
                    json: json_properties
                        .get(key)
                        .cloned()
                        .unwrap_or_else(|| view.clone()),
                    view: view.clone(),
                };
                (key.clone(), Self::optional(property))
            })
            .collect();
        let mut merged = Options::new();
        if let Some(fields) = schema.json.as_object() {
            for (key, value) in fields {
                if !matches!(key.as_str(), "type" | "required" | "properties") {
                    merged = merged.set(key.clone(), value.clone());
                }
            }
        }
        for (key, value) in options.entries {
            merged = merged.with(key, value);
        }
        Self::object_with(properties, merged)
    }
}
