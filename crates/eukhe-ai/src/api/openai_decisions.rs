//! `OpenAI`'s Decisions API (port of `src/api/openai-decisions.ts`):
//! `POST /v1/decisions` with `{ model, input, questions }`.
//! <https://developers.openai.com/api/docs/guides/decisions>
//!
//! The state is sent as JSON text. With images, the input becomes one user
//! message with the state as `input_text` followed by `input_image` data
//! URLs. Questions map to Decisions types: `choice` to `choice`, `score` to
//! `score`, and `bool` to `predicate`. Predicates have no criteria field, so
//! the meanings of true and false are appended to the instructions.
//!
//! Only `OpenAI` API keys work: Sign in with `ChatGPT` tokens are rejected on
//! this route.

use std::collections::HashMap;
use std::sync::Arc;

use eukhe_types::pi_ai::{
    ClassifierAnswer, ClassifierContext, ClassifierModel, ClassifierQuestion, ClassifierResult,
    ClassifierStopReason, IndexMap, JsonObject, JsonValue,
};
use serde_json::json;

use super::classifier_shared::{
    aborted, as_record, empty_result, error, http_error_status, join_url, js_entries,
    parse_classifier_usage, post_classifier_request, required_number, trim_trailing_slashes,
};
use super::ProviderClassifier;
use crate::types::ClassifierOptions;
use crate::utils::diagnostics::Thrown;
use crate::utils::error_body::{format_provider_error, normalize_provider_error};
use crate::utils::js::json_stringify;

const LABEL: &str = "OpenAI Decisions";

/// The endpoint accepts at most this many image parts per request.
const MAX_IMAGES: usize = 128;

fn predicate_instructions(instructions: &str, when_true: &str, when_false: &str) -> String {
    let meanings: Vec<String> = [
        (!when_true.is_empty()).then(|| format!("True means: {when_true}")),
        (!when_false.is_empty()).then(|| format!("False means: {when_false}")),
    ]
    .into_iter()
    .flatten()
    .collect();
    if meanings.is_empty() {
        instructions.to_owned()
    } else {
        format!("{instructions}\n\n{}", meanings.join("\n"))
    }
}

fn wire_question(name: &str, question: &ClassifierQuestion) -> JsonValue {
    match question {
        ClassifierQuestion::Choice {
            instructions,
            criteria,
        } => {
            let choices: Vec<JsonValue> = js_entries(criteria)
                .into_iter()
                .map(|(value, description)| {
                    if description.is_empty() {
                        json!({ "value": value })
                    } else {
                        json!({ "value": value, "description": description })
                    }
                })
                .collect();
            json!({
                "type": "choice",
                "name": name,
                "instructions": instructions,
                "choices": choices,
            })
        }
        ClassifierQuestion::Score {
            instructions,
            criteria,
        } => {
            let levels: Vec<JsonValue> = criteria
                .iter()
                .map(|label| json!({ "label": label }))
                .collect();
            json!({
                "type": "score",
                "name": name,
                "instructions": instructions,
                "levels": levels,
            })
        }
        ClassifierQuestion::Bool {
            instructions,
            criteria,
        } => json!({
            "type": "predicate",
            "name": name,
            "instructions": predicate_instructions(
                instructions,
                &criteria.when_true,
                &criteria.when_false,
            ),
        }),
    }
}

fn wire_input(context: &ClassifierContext) -> Result<JsonValue, Thrown> {
    let state = json_stringify(&JsonValue::Object(context.state.clone()));
    let images = context.images.as_deref().unwrap_or_default();
    if images.is_empty() {
        return Ok(JsonValue::String(state));
    }
    if images.len() > MAX_IMAGES {
        return Err(error(format!(
            "{LABEL} accepts at most {MAX_IMAGES} images, got {}",
            images.len()
        )));
    }
    let mut parts = vec![json!({ "type": "input_text", "text": state })];
    parts.extend(images.iter().map(|image| {
        json!({
            "type": "input_image",
            "image_url": format!("data:{};base64,{}", image.mime_type, image.data),
        })
    }));
    Ok(json!([{ "role": "user", "content": parts }]))
}

fn choice_probabilities(
    value: Option<&JsonValue>,
    id: &str,
) -> Result<IndexMap<String, f64>, Thrown> {
    let invalid = || error(format!("{LABEL} returned invalid probabilities for {id}"));
    let Some(JsonValue::Array(entries)) = value else {
        return Err(invalid());
    };
    let mut probabilities = IndexMap::new();
    for entry in entries {
        let Some(choice) = entry
            .as_object()
            .and_then(|entry| entry.get("value"))
            .and_then(JsonValue::as_str)
        else {
            return Err(invalid());
        };
        let probability = required_number(
            LABEL,
            entry.get("probability"),
            &format!("probability for {id}.{choice}"),
        )?;
        // `Object.fromEntries`: a later duplicate value overwrites in place.
        probabilities.insert(choice.to_owned(), probability);
    }
    Ok(probabilities)
}

fn parse_answer(
    id: &str,
    question: &ClassifierQuestion,
    answer: &JsonObject,
) -> Result<ClassifierAnswer, Thrown> {
    let answer_type = answer.get("type").and_then(JsonValue::as_str);
    if answer_type == Some("refusal") {
        return Err(error(format!("{LABEL} refused to answer {id}")));
    }
    let confidence = || {
        required_number(
            LABEL,
            answer.get("confidence"),
            &format!("confidence for {id}"),
        )
    };
    match question {
        ClassifierQuestion::Choice { .. } => {
            let choice = answer.get("choice").and_then(JsonValue::as_str);
            let (Some("choice"), Some(choice)) = (answer_type, choice) else {
                return Err(error(format!(
                    "{LABEL} did not return a choice answer for {id}"
                )));
            };
            Ok(ClassifierAnswer::Choice {
                choice: choice.to_owned(),
                probabilities: choice_probabilities(answer.get("probabilities"), id)?,
                confidence: confidence()?,
            })
        }
        ClassifierQuestion::Score { .. } => {
            if answer_type != Some("score") {
                return Err(error(format!(
                    "{LABEL} did not return a score answer for {id}"
                )));
            }
            Ok(ClassifierAnswer::Score {
                score: required_number(LABEL, answer.get("score"), &format!("score for {id}"))?,
                confidence: confidence()?,
            })
        }
        ClassifierQuestion::Bool { .. } => {
            if answer_type != Some("predicate") {
                return Err(error(format!(
                    "{LABEL} did not return a predicate answer for {id}"
                )));
            }
            Ok(ClassifierAnswer::Bool {
                probability: required_number(
                    LABEL,
                    answer.get("probability"),
                    &format!("probability for {id}"),
                )?,
            })
        }
    }
}

fn parse_answers(
    value: Option<&JsonValue>,
    context: &ClassifierContext,
) -> Result<IndexMap<String, ClassifierAnswer>, Thrown> {
    let Some(JsonValue::Array(answers)) = value else {
        return Err(error(format!("{LABEL} returned an unexpected response")));
    };
    let mut by_name: HashMap<&str, &JsonObject> = HashMap::new();
    for answer in answers {
        if let Some(answer) = as_record(answer) {
            if let Some(name) = answer.get("name").and_then(JsonValue::as_str) {
                by_name.insert(name, answer);
            }
        }
    }
    let mut parsed = IndexMap::new();
    for (id, question) in js_entries(&context.questions) {
        let Some(answer) = by_name.get(id.as_str()) else {
            return Err(error(format!("{LABEL} did not return an answer for {id}")));
        };
        parsed.insert(id.clone(), parse_answer(id, question, answer)?);
    }
    Ok(parsed)
}

/// Cloudflare in front of api.openai.com answers 504 with an HTML page when
/// a request runs longer than about five seconds. Large inputs, currently
/// above roughly 600K tokens, hit this limit, and retrying the same input
/// runs into it again, so 504 is not retried.
const NO_RETRY_STATUSES: [u16; 1] = [504];

fn error_message(error: &Thrown) -> String {
    if http_error_status(error).is_some_and(|status| status.total_cmp(&504.0).is_eq()) {
        return format!(
            "{LABEL} error (504): the request timed out at the gateway. Very large inputs (above roughly 600K tokens) currently exceed its time limit."
        );
    }
    format_provider_error(
        &normalize_provider_error(error),
        Some(&format!("{LABEL} error")),
    )
}

/// Classification through `OpenAI`'s Decisions API.
pub async fn classify(
    model: ClassifierModel,
    context: ClassifierContext,
    options: ClassifierOptions,
) -> ClassifierResult {
    let mut output = empty_result(&model);
    if let Err(error) = run(&model, &context, &options, &mut output).await {
        output.answers = IndexMap::new();
        output.stop_reason = if aborted(&options) {
            ClassifierStopReason::Aborted
        } else {
            ClassifierStopReason::Error
        };
        output.error_message = Some(error_message(&error));
    }
    output
}

async fn run(
    model: &ClassifierModel,
    context: &ClassifierContext,
    options: &ClassifierOptions,
    output: &mut ClassifierResult,
) -> Result<(), Thrown> {
    if model.api != "openai-decisions" {
        return Err(error(format!("Unsupported classifier API: {}", model.api)));
    }
    let url = join_url(
        &format!("{}/", trim_trailing_slashes(&model.base_url)),
        "decisions",
    )?;
    let questions: Vec<JsonValue> = js_entries(&context.questions)
        .into_iter()
        .map(|(id, question)| wire_question(id, question))
        .collect();
    let body = json!({
        "model": model.id,
        "input": wire_input(context)?,
        "questions": questions,
    });
    let body =
        post_classifier_request(LABEL, &url, model, body, options, &NO_RETRY_STATUSES).await?;
    let Some(body) = as_record(&body) else {
        return Err(error(format!("{LABEL} returned an unexpected response")));
    };
    // Set before parsing answers: a request with malformed or refused answers was still billed.
    if let Some(usage) = parse_classifier_usage(body.get("usage"), model) {
        output.usage = Some(usage);
    }
    output.answers = parse_answers(body.get("answers"), context)?;
    Ok(())
}

/// The Decisions API as a provider classifier.
#[must_use]
pub fn classifier() -> ProviderClassifier {
    ProviderClassifier {
        classify: Arc::new(|model, context, options| {
            Box::pin(classify(model.clone(), context.clone(), options))
        }),
    }
}

#[cfg(test)]
#[path = "openai_decisions_tests.rs"]
mod tests;
