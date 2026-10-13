//! What every eukhe wire tool's contract shares (omp ADR 0026): the intent
//! `i`, the first property of a closed parameter object, and the durable
//! identity `name@rev` each result's details carry as `version`.
//!
//! `i` is declared but not required: a call without an intent still runs
//! (strict on meaning, charitable on dialect, ADR 0020).

use eukhe_ai::typebox::{Options, TSchema, Type};

const INTENT_DESCRIPTION: &str = "Short present-participle intent for this call.";

/// A closed object of `i` followed by the tool's own `properties`.
pub(crate) fn parameters<'a>(properties: impl IntoIterator<Item = (&'a str, TSchema)>) -> TSchema {
    let intent = (
        "i",
        Type::optional(Type::string_with(
            Options::new().set("description", INTENT_DESCRIPTION),
        )),
    );
    Type::object_with(
        std::iter::once(intent).chain(properties),
        Options::new().set("additionalProperties", false),
    )
}
