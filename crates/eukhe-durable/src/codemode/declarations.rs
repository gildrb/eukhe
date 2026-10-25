//! Port of the parts of pi-codemode `declarations.ts` durable code mode
//! uses: TypeScript types of JSON Schemas, and a tool's signature and
//! sample. `renderDeclarations`, `renderGlobal`, and `docComment` are not
//! ported: nothing here renders a whole `declare` block.

use std::collections::HashSet;
use std::fmt::Write as _;

use eukhe_chord::json::to_json;
use indexmap::IndexSet;
use serde_json::{Map, Value};

use super::identifier::{is_codemode_identifier, to_codemode_identifier};

const INDENT: &str = "  ";
/// Largest rendered input type, in characters (UTF-16 units), before it
/// becomes `unknown`.
pub const DEFAULT_INPUT_SCHEMA_MAX_CHARS: usize = 16_000;
/// Local `$ref` expansions per rendered schema, so shared definitions cannot
/// blow up the output.
const MAX_REF_EXPANSIONS: usize = 32;
/// JSON Schema keywords with a number or string value shown as
/// `@keyword value` property tags.
const TAG_KEYWORDS: [&str; 11] = [
    "minimum",
    "exclusiveMinimum",
    "maximum",
    "exclusiveMaximum",
    "multipleOf",
    "minLength",
    "maxLength",
    "pattern",
    "format",
    "minItems",
    "maxItems",
];
/// Tag keywords whose values all hold at once, so only the largest matters.
const LOWER_BOUNDS: [&str; 4] = ["minimum", "exclusiveMinimum", "minLength", "minItems"];
/// Tag keywords whose values all hold at once, so only the smallest matters.
const UPPER_BOUNDS: [&str; 4] = ["maximum", "exclusiveMaximum", "maxLength", "maxItems"];
/// Longest property tag; longer ones (large defaults, long patterns) are
/// left out.
const MAX_TAG_CHARS: usize = 80;

/// A tool as its declaration renders it (pi-codemode
/// `CodemodeToolDeclaration`).
#[derive(Debug, Clone, PartialEq)]
pub struct CodemodeToolDeclaration {
    /// The tool's name; scripts use [`to_codemode_identifier`] of it.
    pub name: String,
    /// The tool's description.
    pub description: Option<String>,
    /// JSON Schema of the arguments; `None` renders `unknown`.
    pub input_schema: Option<Value>,
    /// JSON Schema of the result; `None` renders `unknown`.
    pub output_schema: Option<Value>,
}

fn utf16_len(text: &str) -> usize {
    text.encode_utf16().count()
}

/// JS `JSON.stringify(value)`. Values parsed from JSON always stringify; a
/// failure renders `unknown`, as the TS does for `undefined`.
fn stringify(value: &Value) -> String {
    to_json(value).map_or_else(|_| "unknown".to_owned(), |json| json.to_string())
}

/// JS `String(n)` of a number.
fn number_text(number: f64) -> String {
    to_json(&number).map_or_else(|_| number.to_string(), |json| json.to_string())
}

/// Whether a line terminator ends a `//` comment here.
fn is_line_terminator(c: char) -> bool {
    matches!(c, '\r' | '\n' | '\u{2028}' | '\u{2029}')
}

/// One tool as a member of the `tools` object: `name(args: T): Promise<R>;`
/// with the name as the identifier scripts use. Input types longer than
/// `input_max_chars` render as `unknown`.
#[must_use]
pub fn render_tool_signature(tool: &CodemodeToolDeclaration, input_max_chars: usize) -> String {
    let input = tool.input_schema.as_ref().map_or_else(
        || "unknown".to_owned(),
        |schema| schema_to_type_within(schema, input_max_chars),
    );
    format!(
        "{}(args: {input}): Promise<{}>;",
        to_codemode_identifier(&tool.name),
        render_tool_output_type(tool.output_schema.as_ref())
    )
}

/// A tool's sample: the description followed by the tool's declaration.
/// Used for tool listings and `ALL_TOOLS` entries.
#[must_use]
pub fn render_tool_sample(tool: &CodemodeToolDeclaration) -> String {
    let declaration = format!(
        "declare const tools: {{ {} }};",
        render_tool_signature(tool, DEFAULT_INPUT_SCHEMA_MAX_CHARS)
    );
    let description = tool.description.as_deref().map_or("", str::trim);
    format!("{description}\n\ncodemode tool declaration:\n```ts\n{declaration}\n```")
}

/// The type a tool call resolves to: the output schema's type, and
/// `unknown` without a schema.
#[must_use]
pub fn render_tool_output_type(schema: Option<&Value>) -> String {
    schema.map_or_else(|| "unknown".to_owned(), schema_to_type)
}

fn property_key(name: &str) -> String {
    if is_codemode_identifier(name) {
        name.to_owned()
    } else {
        stringify(&Value::String(name.to_owned()))
    }
}

fn union(types: Vec<String>) -> String {
    let unique: IndexSet<String> = types.into_iter().collect();
    if unique.contains("unknown") {
        return "unknown".to_owned();
    }
    if unique.is_empty() {
        return "never".to_owned();
    }
    unique.into_iter().collect::<Vec<_>>().join(" | ")
}

/// Whether tags render.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tags {
    Shown,
    Omitted,
}

struct Context<'a> {
    root: &'a Value,
    resolving: HashSet<String>,
    expansions: usize,
    tags: Tags,
}

fn render(schema: &Value, tags: Tags) -> String {
    to_type(
        schema,
        &mut Context {
            root: schema,
            resolving: HashSet::new(),
            expansions: 0,
            tags,
        },
    )
}

/// Convert a JSON Schema to a TypeScript type expression: objects on one
/// line (`{ a: string; b?: number; }`) with properties sorted by name, or
/// one property per line with `//` comments when a property has a
/// description or constraints the type cannot express
/// (`// @integer @minimum 1 @default 20`); `Array<T>` for arrays. Local
/// references (`#/$defs/...`, `#/definitions/...`) resolve against
/// `schema`; recursive and remote references render as `unknown`.
#[must_use]
pub fn schema_to_type(schema: &Value) -> String {
    render(schema, Tags::Shown)
}

/// [`schema_to_type`] bounded by `max_chars` (UTF-16 units): a longer
/// result is rendered again without the constraint tags, and renders as
/// `unknown` if it is still too long.
#[must_use]
pub fn schema_to_type_within(schema: &Value, max_chars: usize) -> String {
    let tagged = render(schema, Tags::Shown);
    if utf16_len(&tagged) <= max_chars {
        return tagged;
    }
    let untagged = render(schema, Tags::Omitted);
    if utf16_len(&untagged) <= max_chars {
        untagged
    } else {
        "unknown".to_owned()
    }
}

/// JS `decodeURIComponent`; `None` where it throws (malformed escapes or
/// UTF-8).
fn decode_uri_component(segment: &str) -> Option<String> {
    let bytes = segment.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'%' {
            let hex = segment
                .get(index + 1..index + 3)
                .filter(|hex| hex.bytes().all(|byte| byte.is_ascii_hexdigit()))?;
            decoded.push(u8::from_str_radix(hex, 16).ok()?);
            index += 3;
        } else {
            decoded.push(bytes[index]);
            index += 1;
        }
    }
    String::from_utf8(decoded).ok()
}

fn resolve_ref<'a>(reference: &str, root: &'a Value) -> Option<&'a Value> {
    if reference != "#" && !reference.starts_with("#/") {
        return None;
    }
    let mut current = root;
    for segment in reference
        .get(2..)
        .unwrap_or_default()
        .split('/')
        .filter(|segment| !segment.is_empty())
    {
        let key = decode_uri_component(segment)?
            .replace("~1", "/")
            .replace("~0", "~");
        let Value::Object(object) = current else {
            return None;
        };
        current = object.get(&key)?;
    }
    match current {
        Value::Bool(_) | Value::Object(_) => Some(current),
        Value::Null | Value::Number(_) | Value::String(_) | Value::Array(_) => None,
    }
}

fn to_type(schema: &Value, context: &mut Context<'_>) -> String {
    let object = match schema {
        Value::Bool(true) => return "unknown".to_owned(),
        Value::Bool(false) => return "never".to_owned(),
        Value::Null | Value::Number(_) | Value::String(_) | Value::Array(_) => {
            return "unknown".to_owned();
        }
        Value::Object(object) => object,
    };
    if let Some(Value::String(reference)) = object.get("$ref") {
        if context.resolving.contains(reference) || context.expansions >= MAX_REF_EXPANSIONS {
            return "unknown".to_owned();
        }
        let Some(target) = resolve_ref(reference, context.root) else {
            return "unknown".to_owned();
        };
        context.expansions += 1;
        context.resolving.insert(reference.clone());
        let rendered = to_type(target, context);
        context.resolving.remove(reference);
        return rendered;
    }
    if let Some(value) = object.get("const") {
        return stringify(value);
    }
    if let Some(Value::Array(values)) = object.get("enum") {
        return union(values.iter().map(stringify).collect());
    }
    let variants = match (object.get("anyOf"), object.get("oneOf")) {
        (Some(Value::Array(variants)), _) | (_, Some(Value::Array(variants))) => Some(variants),
        _ => None,
    };
    if let Some(variants) = variants {
        return union(
            variants
                .iter()
                .map(|variant| to_type(variant, context))
                .collect(),
        );
    }
    if let Some(Value::Array(parts)) = object.get("allOf") {
        let parts: Vec<String> = parts
            .iter()
            .map(|part| to_type(part, context))
            .filter(|part| part != "unknown")
            .collect();
        if parts.is_empty() {
            return "unknown".to_owned();
        }
        return parts
            .iter()
            .map(|part| {
                if part.contains(" | ") {
                    format!("({part})")
                } else {
                    part.clone()
                }
            })
            .collect::<Vec<_>>()
            .join(" & ");
    }
    match object.get("type") {
        Some(Value::Array(types)) => union(
            types
                .iter()
                .map(|entry| {
                    let mut variant = object.clone();
                    variant.insert("type".to_owned(), entry.clone());
                    to_type(&Value::Object(variant), context)
                })
                .collect(),
        ),
        Some(Value::String(name)) => match name.as_str() {
            "string" => "string".to_owned(),
            "number" | "integer" => "number".to_owned(),
            "boolean" => "boolean".to_owned(),
            "null" => "null".to_owned(),
            "array" => array_type(object, context),
            "object" => object_type(object, context),
            _ => "unknown".to_owned(),
        },
        Some(Value::Null | Value::Bool(_) | Value::Number(_) | Value::Object(_)) => {
            "unknown".to_owned()
        }
        None => {
            if ["properties", "additionalProperties", "required"]
                .iter()
                .any(|key| object.contains_key(*key))
            {
                object_type(object, context)
            } else if object.contains_key("items") || object.contains_key("prefixItems") {
                array_type(object, context)
            } else {
                "unknown".to_owned()
            }
        }
    }
}

fn array_type(schema: &Map<String, Value>, context: &mut Context<'_>) -> String {
    let items = schema.get("items");
    if let Some(items) = items.filter(|items| !items.is_array()) {
        return format!("Array<{}>", to_type(items, context));
    }
    let tuple = match (schema.get("prefixItems"), items) {
        (Some(Value::Array(tuple)), _) | (_, Some(Value::Array(tuple))) => tuple.as_slice(),
        _ => &[],
    };
    if tuple.is_empty() {
        return "unknown[]".to_owned();
    }
    let types: Vec<String> = tuple.iter().map(|item| to_type(item, context)).collect();
    format!("[{}]", types.join(", "))
}

fn description_of(property: &Value) -> &str {
    match property.get("description") {
        Some(Value::String(description)) => description.trim(),
        _ => "",
    }
}

/// A tag value deduplicated like a JS `Set` of numbers and strings.
#[derive(Debug, Clone, PartialEq)]
enum TagValue<'a> {
    Number(f64),
    Text(&'a str),
}

/// Constraints of a property that its TypeScript type cannot express, as
/// JSDoc-style tags: `@integer @minimum 1 @maximum 100 @default 20`. Empty
/// when there are none.
#[expect(
    clippy::too_many_lines,
    reason = "one ported upstream routine mapping each JSON Schema keyword to its tag"
)]
fn constraint_tags(schema: &Value) -> String {
    let Value::Object(property) = schema else {
        return String::new();
    };
    // Optional fields such as Pydantic's `int | None` keep their constraints
    // in the non-null branch. The branch's constraints apply together with
    // the property's, so both are read.
    let variants = match property.get("anyOf") {
        Some(Value::Array(variants)) => Some(variants),
        _ => match property.get("oneOf") {
            Some(Value::Array(variants)) => Some(variants),
            _ => None,
        },
    };
    let non_null: Vec<&Value> = variants
        .map(|variants| {
            variants
                .iter()
                .filter(|variant| variant.get("type") != Some(&Value::String("null".to_owned())))
                .collect()
        })
        .unwrap_or_default();
    let mut branches = vec![property];
    if let [Value::Object(branch)] = non_null.as_slice() {
        branches.push(branch);
    }
    // Draft-04 and OpenAPI 3.0 make `minimum`/`maximum` exclusive with a
    // boolean `exclusiveMinimum`/`exclusiveMaximum`.
    let schemas: Vec<Map<String, Value>> = branches
        .into_iter()
        .map(|branch| {
            let mut schema = branch.clone();
            for (inclusive, exclusive) in [
                ("minimum", "exclusiveMinimum"),
                ("maximum", "exclusiveMaximum"),
            ] {
                if schema.get(exclusive) == Some(&Value::Bool(true)) {
                    match schema.remove(inclusive) {
                        Some(bound) => schema.insert(exclusive.to_owned(), bound),
                        None => schema.remove(exclusive),
                    };
                }
            }
            schema
        })
        .collect();
    let mut tags: Vec<String> = Vec::new();
    let is_integer = |schema: &Map<String, Value>| match schema.get("type") {
        Some(Value::String(name)) => name == "integer",
        Some(Value::Array(types)) => types.iter().any(|entry| entry == "integer"),
        _ => false,
    };
    if schemas.iter().any(is_integer) {
        tags.push("@integer".to_owned());
    }
    for keyword in TAG_KEYWORDS {
        let values = schemas.iter().filter_map(|schema| schema.get(keyword));
        let lower = LOWER_BOUNDS.contains(&keyword);
        if lower || UPPER_BOUNDS.contains(&keyword) {
            let numbers: Vec<f64> = values.filter_map(Value::as_f64).collect();
            let bound = if lower {
                numbers.into_iter().reduce(f64::max)
            } else {
                numbers.into_iter().reduce(f64::min)
            };
            if let Some(bound) = bound {
                tags.push(format!("@{keyword} {}", number_text(bound)));
            }
            continue;
        }
        let mut seen: Vec<TagValue<'_>> = Vec::new();
        for value in values {
            let tag_value = match value {
                Value::Number(number) => number.as_f64().map(TagValue::Number),
                Value::String(text) => Some(TagValue::Text(text)),
                Value::Null | Value::Bool(_) | Value::Array(_) | Value::Object(_) => None,
            };
            let Some(tag_value) = tag_value else {
                continue;
            };
            if seen.contains(&tag_value) {
                continue;
            }
            let text = match &tag_value {
                TagValue::Number(number) => number_text(*number),
                TagValue::Text(text) => (*text).to_owned(),
            };
            tags.push(format!("@{keyword} {text}"));
            seen.push(tag_value);
        }
    }
    if schemas
        .iter()
        .any(|schema| schema.get("uniqueItems") == Some(&Value::Bool(true)))
    {
        tags.push("@uniqueItems".to_owned());
    }
    // Annotations, unlike constraints, come from the property itself.
    if let Some(default) = property.get("default").filter(|default| !default.is_null()) {
        tags.push(format!("@default {}", stringify(default)));
    }
    if property.get("deprecated") == Some(&Value::Bool(true)) {
        tags.push("@deprecated".to_owned());
    }
    tags.into_iter()
        .filter(|tag| utf16_len(tag) <= MAX_TAG_CHARS)
        .map(|tag| escape_line_terminators(&tag))
        .collect::<Vec<_>>()
        .join(" ")
}

/// Line terminators as `\uXXXX`, so a tag stays on its comment line.
fn escape_line_terminators(tag: &str) -> String {
    let mut escaped = String::with_capacity(tag.len());
    for c in tag.chars() {
        if is_line_terminator(c) {
            let _ = write!(escaped, "\\u{:04x}", u32::from(c));
        } else {
            escaped.push(c);
        }
    }
    escaped
}

fn object_type(schema: &Map<String, Value>, context: &mut Context<'_>) -> String {
    let empty = Map::new();
    let properties = match schema.get("properties") {
        Some(Value::Object(properties)) => properties,
        _ => &empty,
    };
    let required: &[Value] = match schema.get("required") {
        Some(Value::Array(required)) => required,
        _ => &[],
    };
    let mut names: Vec<&String> = properties.keys().collect();
    // JS `sort()` compares UTF-16 code units.
    names.sort_by(|left, right| left.encode_utf16().cmp(right.encode_utf16()));
    let mut members: Vec<String> = names
        .iter()
        .map(|name| {
            let optional = if required.iter().any(|entry| entry == name.as_str()) {
                ""
            } else {
                "?"
            };
            format!(
                "{}{optional}: {};",
                property_key(name),
                to_type(&properties[name.as_str()], context)
            )
        })
        .collect();
    match schema.get("additionalProperties") {
        Some(Value::Bool(false)) => {}
        Some(Value::Bool(true)) => members.push("[key: string]: unknown;".to_owned()),
        Some(additional) => {
            members.push(format!("[key: string]: {};", to_type(additional, context)));
        }
        None if names.is_empty() => members.push("[key: string]: unknown;".to_owned()),
        None => {}
    }
    if members.is_empty() {
        return "{}".to_owned();
    }
    let comments: Vec<Vec<String>> = names
        .iter()
        .map(|name| {
            let property = &properties[name.as_str()];
            let mut lines: Vec<String> = description_of(property)
                .split(is_line_terminator)
                .map(str::trim)
                .filter(|line| !line.is_empty())
                .map(str::to_owned)
                .collect();
            let tags = match context.tags {
                Tags::Shown => constraint_tags(property),
                Tags::Omitted => String::new(),
            };
            if !tags.is_empty() {
                lines.push(tags);
            }
            lines
        })
        .collect();
    if comments.iter().all(Vec::is_empty) {
        return format!("{{ {} }}", members.join(" "));
    }
    let mut lines = vec!["{".to_owned()];
    for (comment, member) in comments.iter().zip(&members) {
        for line in comment {
            lines.push(format!("{INDENT}// {line}"));
        }
        lines.push(format!(
            "{INDENT}{}",
            member.replace('\n', &format!("\n{INDENT}"))
        ));
    }
    for member in &members[names.len()..] {
        lines.push(format!("{INDENT}{member}"));
    }
    lines.push("}".to_owned());
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn primitive_and_boolean_schemas() {
        assert_eq!(schema_to_type(&json!(true)), "unknown");
        assert_eq!(schema_to_type(&json!(false)), "never");
        assert_eq!(schema_to_type(&json!(3)), "unknown");
        assert_eq!(schema_to_type(&json!({"type": "integer"})), "number");
        assert_eq!(
            schema_to_type(&json!({"type": ["string", "null"]})),
            "string | null"
        );
        assert_eq!(schema_to_type(&json!({"type": "date"})), "unknown");
        assert_eq!(schema_to_type(&json!({})), "unknown");
    }

    #[test]
    fn const_enum_and_unions() {
        assert_eq!(schema_to_type(&json!({"const": "a\"b"})), "\"a\\\"b\"");
        assert_eq!(
            schema_to_type(&json!({"enum": ["a", 1, "a", null]})),
            "\"a\" | 1 | null"
        );
        assert_eq!(schema_to_type(&json!({"enum": []})), "never");
        assert_eq!(
            schema_to_type(
                &json!({"anyOf": [{"type": "string"}, {"type": "number"}, {"type": "string"}]})
            ),
            "string | number"
        );
        assert_eq!(
            schema_to_type(&json!({"oneOf": [{"type": "string"}, {}]})),
            "unknown"
        );
        assert_eq!(
            schema_to_type(&json!({"allOf": [{"enum": ["a", "b"]}, {}, {"type": "string"}]})),
            "(\"a\" | \"b\") & string"
        );
        assert_eq!(schema_to_type(&json!({"allOf": [{}]})), "unknown");
    }

    #[test]
    fn arrays_and_tuples() {
        assert_eq!(
            schema_to_type(&json!({"type": "array", "items": {"type": "string"}})),
            "Array<string>"
        );
        assert_eq!(
            schema_to_type(&json!({"prefixItems": [{"type": "string"}, {"type": "number"}]})),
            "[string, number]"
        );
        assert_eq!(
            schema_to_type(&json!({"type": "array", "items": [{"type": "null"}]})),
            "[null]"
        );
        assert_eq!(schema_to_type(&json!({"type": "array"})), "unknown[]");
    }

    #[test]
    fn objects_on_one_line() {
        assert_eq!(
            schema_to_type(&json!({
                "type": "object",
                "properties": {"b": {"type": "number"}, "a": {"type": "string"}, "my-key": {}},
                "required": ["a"],
                "additionalProperties": false
            })),
            "{ a: string; b?: number; \"my-key\"?: unknown; }"
        );
        assert_eq!(
            schema_to_type(&json!({"type": "object"})),
            "{ [key: string]: unknown; }"
        );
        assert_eq!(
            schema_to_type(&json!({"type": "object", "additionalProperties": false})),
            "{}"
        );
        assert_eq!(
            schema_to_type(&json!({"additionalProperties": {"type": "number"}})),
            "{ [key: string]: number; }"
        );
    }

    #[test]
    fn objects_with_comments() {
        let schema = json!({
            "type": "object",
            "properties": {
                "limit": {
                    "type": "integer",
                    "description": "  How many.\nAt most 100. ",
                    "minimum": 1,
                    "maximum": 100,
                    "default": 20
                },
                "nested": {
                    "type": "object",
                    "properties": {"x": {"type": "string", "description": "X"}}
                },
                "query": {"type": "string"}
            },
            "required": ["query"],
            "additionalProperties": true
        });
        assert_eq!(
            schema_to_type(&schema),
            "{\n  // How many.\n  // At most 100.\n  // @integer @minimum 1 @maximum 100 @default 20\n  limit?: number;\n  nested?: {\n    // X\n    x?: string;\n  };\n  query: string;\n  [key: string]: unknown;\n}"
        );
        assert_eq!(
            schema_to_type_within(&schema, 150),
            "{\n  // How many.\n  // At most 100.\n  limit?: number;\n  nested?: {\n    // X\n    x?: string;\n  };\n  query: string;\n  [key: string]: unknown;\n}"
        );
        assert_eq!(schema_to_type_within(&schema, 10), "unknown");
    }

    #[test]
    fn constraint_tags_merge_branches_and_bounds() {
        let schema = json!({
            "properties": {
                "n": {
                    "anyOf": [{"type": "integer", "minimum": 5, "exclusiveMaximum": true, "maximum": 9}, {"type": "null"}],
                    "minimum": 2,
                    "maximum": 50,
                    "format": "int",
                    "default": null,
                    "deprecated": true
                },
                "s": {"type": "string", "pattern": "a\nb", "minLength": 1.5, "uniqueItems": true}
            }
        });
        assert_eq!(
            schema_to_type(&schema),
            "{\n  // @integer @minimum 5 @maximum 50 @exclusiveMaximum 9 @format int @deprecated\n  n?: number | null;\n  // @minLength 1.5 @pattern a\\u000ab @uniqueItems\n  s?: string;\n}"
        );
    }

    #[test]
    fn long_tags_are_left_out() {
        let long = "x".repeat(80);
        let schema =
            json!({"properties": {"a": {"type": "string", "pattern": long, "default": "d"}}});
        assert_eq!(
            schema_to_type(&schema),
            "{\n  // @default \"d\"\n  a?: string;\n}"
        );
    }

    #[test]
    fn local_references() {
        let schema = json!({
            "$defs": {"Name": {"type": "string"}, "a/b": {"type": "number"}, "Node": {"properties": {"next": {"$ref": "#/$defs/Node"}}}},
            "properties": {
                "name": {"$ref": "#/$defs/Name"},
                "escaped": {"$ref": "#/$defs/a~1b"},
                "encoded": {"$ref": "#/%24defs/Name"},
                "malformed": {"$ref": "#/$defs/%E0"},
                "remote": {"$ref": "https://example.com/schema"},
                "node": {"$ref": "#/$defs/Node"},
                "flag": {"$ref": "#/$defs/missing"}
            }
        });
        assert_eq!(
            schema_to_type(&schema),
            "{ encoded?: string; escaped?: number; flag?: unknown; malformed?: unknown; name?: string; node?: { next?: unknown; }; remote?: unknown; }"
        );
        assert_eq!(schema_to_type(&json!({"$ref": "#"})), "unknown");
    }

    #[test]
    fn ref_expansions_are_bounded() {
        let mut properties = Map::new();
        for index in 0..33 {
            properties.insert(format!("p{index:02}"), json!({"$ref": "#/$defs/T"}));
        }
        let schema = json!({"$defs": {"T": {"type": "string"}}, "properties": properties});
        let rendered = schema_to_type(&schema);
        assert!(
            rendered.ends_with("p31?: string; p32?: unknown; }"),
            "{rendered}"
        );
    }

    #[test]
    fn tool_signature_and_sample() {
        let tool = CodemodeToolDeclaration {
            name: "my-tool".to_owned(),
            description: Some("  Reads a file.\n".to_owned()),
            input_schema: Some(
                json!({"properties": {"path": {"type": "string"}}, "required": ["path"]}),
            ),
            output_schema: Some(json!({"type": "string"})),
        };
        assert_eq!(
            render_tool_signature(&tool, 16_000),
            "my_tool(args: { path: string; }): Promise<string>;"
        );
        assert_eq!(
            render_tool_signature(&tool, 5),
            "my_tool(args: unknown): Promise<string>;"
        );
        assert_eq!(
            render_tool_sample(&tool),
            "Reads a file.\n\ncodemode tool declaration:\n```ts\ndeclare const tools: { my_tool(args: { path: string; }): Promise<string>; };\n```"
        );
        let bare = CodemodeToolDeclaration {
            name: "x".to_owned(),
            description: None,
            input_schema: None,
            output_schema: None,
        };
        assert_eq!(
            render_tool_sample(&bare),
            "\n\ncodemode tool declaration:\n```ts\ndeclare const tools: { x(args: unknown): Promise<unknown>; };\n```"
        );
        assert_eq!(render_tool_output_type(None), "unknown");
    }
}
