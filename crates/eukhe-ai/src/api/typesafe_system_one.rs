//! `TypeSafe`'s native System One protocol (port of
//! `src/api/typesafe-system-one.ts`). `OpenRouter` serves the same protocol,
//! so both providers use this API with different base URLs.

use std::sync::Arc;

use eukhe_types::pi_ai::{ClassifierModel, JsonObject, JsonValue};

use super::classifier_shared::{error, join_url, trim_trailing_slashes};
use super::system_one_shared::{classify_system_one, SystemOneTransport};
use super::ProviderClassifier;
use crate::utils::diagnostics::Thrown;

fn url(model: &ClassifierModel) -> Result<url::Url, Thrown> {
    join_url(
        &format!("{}/", trim_trailing_slashes(&model.base_url)),
        "systemone",
    )
}

/// `{ model: model.id, ...request }`.
fn payload(model: &ClassifierModel, request: JsonObject) -> JsonValue {
    let mut body = JsonObject::new();
    body.insert("model".to_owned(), JsonValue::from(model.id.clone()));
    body.extend(request);
    JsonValue::Object(body)
}

fn output(body: JsonValue) -> Result<JsonObject, Thrown> {
    match body {
        JsonValue::Object(object) => Ok(object),
        _ => Err(error("System One API returned an unexpected response")),
    }
}

static TRANSPORT: SystemOneTransport = SystemOneTransport {
    api: "typesafe-system-one",
    label: "System One API",
    url,
    payload,
    output,
};

/// `TypeSafe` System One classification with public `bool` values mapped to
/// wire-level `noul`.
#[must_use]
pub fn classifier() -> ProviderClassifier {
    ProviderClassifier {
        classify: Arc::new(|model, context, options| {
            Box::pin(classify_system_one(
                &TRANSPORT,
                model.clone(),
                context.clone(),
                options,
            ))
        }),
    }
}

#[cfg(test)]
#[path = "typesafe_system_one_tests.rs"]
mod tests;
