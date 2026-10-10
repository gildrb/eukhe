//! System One models on the Workers AI REST endpoint (port of
//! `src/api/cloudflare-workers-ai-system-one.ts`):
//! `POST /accounts/{account}/ai/run` with `{ model, input }`. The REST API
//! wraps the model output in Cloudflare's API envelope. Third-party models
//! such as `typesafe/jev` add a run record:
//! `{ success, result: { state: "Completed", result: { answers, usage } } }`.
//! Cloudflare-hosted models such as `@cf/cloudflare/clef` return the output
//! directly: `{ success, result: { model, answers, usage } }`.

use std::sync::Arc;

use eukhe_types::pi_ai::{ClassifierModel, JsonObject, JsonValue};

use super::classifier_shared::{error, join_url, trim_trailing_slashes};
use super::system_one_shared::{classify_system_one, SystemOneTransport};
use super::ProviderClassifier;
use crate::utils::diagnostics::Thrown;
use crate::utils::js::js_to_string;

const LABEL: &str = "Cloudflare Workers AI";

fn cloudflare_error_message(errors: Option<&JsonValue>) -> String {
    if let Some(JsonValue::Array(errors)) = errors {
        let messages: Vec<&str> = errors
            .iter()
            .filter_map(|error| error.as_object()?.get("message")?.as_str())
            .collect();
        if !messages.is_empty() {
            return format!("{LABEL} error: {}", messages.join("; "));
        }
    }
    format!("{LABEL} request failed")
}

fn unexpected() -> Thrown {
    error(format!("{LABEL} returned an unexpected response"))
}

fn url(model: &ClassifierModel) -> Result<url::Url, Thrown> {
    join_url(
        &format!("{}/", trim_trailing_slashes(&model.base_url)),
        "run",
    )
}

/// `{ model: model.id, input: request }`.
fn payload(model: &ClassifierModel, request: JsonObject) -> JsonValue {
    let mut body = JsonObject::new();
    body.insert("model".to_owned(), JsonValue::from(model.id.clone()));
    body.insert("input".to_owned(), JsonValue::Object(request));
    JsonValue::Object(body)
}

fn output(body: JsonValue) -> Result<JsonObject, Thrown> {
    let JsonValue::Object(mut body) = body else {
        return Err(unexpected());
    };
    if body.get("success") == Some(&JsonValue::Bool(false)) {
        return Err(error(cloudflare_error_message(body.get("errors"))));
    }
    let Some(JsonValue::Object(mut result)) = body.shift_remove("result") else {
        return Err(unexpected());
    };
    if result.contains_key("answers") {
        return Ok(result);
    }
    if result.get("state").and_then(JsonValue::as_str) != Some("Completed") {
        let state = result
            .get("state")
            .map_or_else(|| "undefined".to_owned(), js_to_string);
        return Err(error(format!(
            "{LABEL} run did not complete (state: {state})"
        )));
    }
    match result.shift_remove("result") {
        Some(JsonValue::Object(inner)) => Ok(inner),
        _ => Err(unexpected()),
    }
}

static TRANSPORT: SystemOneTransport = SystemOneTransport {
    api: "cloudflare-workers-ai-system-one",
    label: LABEL,
    url,
    payload,
    output,
};

/// Cloudflare Workers AI System One classification with public `bool`
/// values mapped to wire-level `noul`.
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
#[path = "cloudflare_workers_ai_system_one_tests.rs"]
mod tests;
