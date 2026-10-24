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
use eukhe_bend::rules::tool_surface::{self, Schema, INTENT as INTENT_ID};
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
/// (`build` of bend/tools.bend, run as the compiled core): the core
/// decides the parameters in order (`i` first unless the schema has it,
/// every declared parameter kept in its place) and the version (the
/// declared `n` of `title: "v<n>"`, else 0, at least 1). Every other key
/// keeps its place, so building a built schema changes nothing.
pub(crate) fn build(schema: &ToolSchema) -> ToolSchema {
    let declared = schema
        .json()
        .get("title")
        .and_then(JsonValue::as_str)
        .and_then(|title| title.strip_prefix('v'))
        .and_then(|number| number.parse::<u32>().ok())
        .unwrap_or(0);
    let properties = schema
        .json()
        .get("properties")
        .and_then(JsonValue::as_object)
        .cloned()
        .unwrap_or_default();
    // The parameters as numbers: `i` is the intent's, the others 1, 2, ...
    // in declared order.
    let names: Vec<&String> = properties.keys().collect();
    let numbers = (1..).zip(&names).map(|(number, name)| {
        if name.as_str() == INTENT {
            INTENT_ID
        } else {
            number
        }
    });
    let built = tool_surface::build(&Schema {
        params: numbers.collect(),
        version: u64::from(declared),
    });
    let title = JsonValue::from(format!("v{}", built.version));
    let intent = intent();
    let node = |schema: &JsonValue, intent: &JsonValue| {
        let mut node = schema.as_object().cloned().unwrap_or_default();
        let declared = node
            .get("properties")
            .and_then(JsonValue::as_object)
            .cloned()
            .unwrap_or_default();
        let mut sent = JsonObject::new();
        for &param in &built.params {
            // 0 is the intent; n > 0 the n-th declared parameter.
            let name = param
                .checked_sub(1)
                .and_then(|index| usize::try_from(index).ok())
                .and_then(|index| names.get(index))
                .map_or(INTENT, |name| name.as_str());
            let value = declared
                .get(name)
                .cloned()
                .unwrap_or_else(|| intent.clone());
            sent.insert(name.to_owned(), value);
        }
        node.insert("properties".to_owned(), JsonValue::Object(sent));
        node.insert("title".to_owned(), title.clone());
        JsonValue::Object(node)
    };
    let json = node(schema.json(), intent.json());
    match schema.typebox() {
        Some(view) => ToolSchema::from_typebox(json, node(view, intent.typebox())),
        None => ToolSchema::from(json),
    }
}
