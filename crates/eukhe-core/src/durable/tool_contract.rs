//! What every eukhe wire tool's contract shares (omp ADR 0026, docs/tools.md
//! S7): the intent `i`, the first property of a closed parameter object; the
//! schema version, the annotation `title: "v<n>"` with `n >= 1`, which every
//! wire API keeps; and the durable identity `name@rev` each result's details
//! carry as `version`.
//!
//! `i` is declared but not required: a call without an intent still runs
//! (strict on meaning, charitable on dialect, ADR 0020). [`build`] gives
//! every tool of the session both, as the harness sends it.

use eukhe_ai::typebox::{Options, TSchema, Type};
use eukhe_types::pi_ai::{JsonObject, JsonValue, ToolSchema};

const INTENT_DESCRIPTION: &str = "Short present-participle intent for this call.";

/// The intent parameter's name.
const INTENT: &str = "i";

/// The intent parameter: an optional string.
fn intent() -> TSchema {
    Type::optional(Type::string_with(
        Options::new().set("description", INTENT_DESCRIPTION),
    ))
}

/// A closed object of `i` followed by the tool's own `properties`, at schema
/// version `version`.
pub(crate) fn parameters<'a>(
    version: u32,
    properties: impl IntoIterator<Item = (&'a str, TSchema)>,
) -> TSchema {
    Type::object_with(
        std::iter::once((INTENT, intent())).chain(properties),
        Options::new()
            .set("additionalProperties", false)
            .set("title", format!("v{version}")),
    )
}

/// The schema the harness sends for a tool that declares `schema`
/// (`build` of bend/tools.bend): `i` first unless the schema has it, every
/// declared parameter kept in its place, and the declared version (`n` of
/// `title: "v<n>"`, else 0), at least 1. Every other key keeps its place, so
/// building a built schema changes nothing.
pub(crate) fn build(schema: &ToolSchema) -> ToolSchema {
    let declared = schema
        .json()
        .get("title")
        .and_then(JsonValue::as_str)
        .and_then(|title| title.strip_prefix('v'))
        .and_then(|number| number.parse::<u32>().ok())
        .unwrap_or(0);
    let title = JsonValue::from(format!("v{}", declared.max(1)));
    let intent = intent();
    let node = |schema: &JsonValue, intent: &JsonValue| {
        let mut built = schema.as_object().cloned().unwrap_or_default();
        let declared = built
            .get("properties")
            .and_then(JsonValue::as_object)
            .cloned()
            .unwrap_or_default();
        if !declared.contains_key(INTENT) {
            let mut properties = JsonObject::new();
            properties.insert(INTENT.to_owned(), intent.clone());
            properties.extend(declared);
            built.insert("properties".to_owned(), JsonValue::Object(properties));
        }
        built.insert("title".to_owned(), title.clone());
        JsonValue::Object(built)
    };
    let json = node(schema.json(), intent.json());
    match schema.typebox() {
        Some(view) => ToolSchema::from_typebox(json, node(view, intent.typebox())),
        None => ToolSchema::from(json),
    }
}
