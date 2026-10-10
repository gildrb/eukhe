//! System One classification shared by the services that serve `TypeSafe`'s
//! System One models (port of `src/api/system-one-shared.ts`).

use eukhe_types::pi_ai::{
    ClassifierAnswer, ClassifierContext, ClassifierModel, ClassifierQuestion, ClassifierResult,
    IndexMap, JsonObject, JsonValue,
};

use super::classifier_shared::{
    as_record, empty_result, error, fail, js_entries, parse_classifier_usage,
    post_classifier_request, required_number,
};
use crate::types::ClassifierOptions;
use crate::utils::diagnostics::Thrown;
use crate::utils::js::js_object_entries;

/// Differences between services that serve System One models.
pub(crate) struct SystemOneTransport {
    /// Classifier API implemented by this transport.
    pub(crate) api: &'static str,
    /// Service name used in error messages.
    pub(crate) label: &'static str,
    /// Absolute request URL.
    pub(crate) url: fn(&ClassifierModel) -> Result<url::Url, Thrown>,
    /// Wraps the System One request (`{ state, questions }`) in the service's
    /// request envelope.
    pub(crate) payload: fn(&ClassifierModel, JsonObject) -> JsonValue,
    /// Extracts the System One output (`{ answers, usage }`) from the
    /// service's response envelope.
    pub(crate) output: fn(JsonValue) -> Result<JsonObject, Thrown>,
}

fn probabilities(
    label: &str,
    value: Option<&JsonValue>,
    id: &str,
) -> Result<IndexMap<String, f64>, Thrown> {
    let Some(record) = value.and_then(as_record) else {
        return Err(error(format!(
            "{label} returned invalid probabilities for {id}"
        )));
    };
    js_object_entries(record)
        .into_iter()
        .map(|(key, probability)| {
            let number = required_number(
                label,
                Some(probability),
                &format!("probability for {id}.{key}"),
            )?;
            Ok((key.clone(), number))
        })
        .collect()
}

fn parse_answers(
    label: &str,
    value: Option<&JsonValue>,
    context: &ClassifierContext,
) -> Result<IndexMap<String, ClassifierAnswer>, Thrown> {
    let Some(value) = value.and_then(as_record) else {
        return Err(error(format!("{label} returned an unexpected response")));
    };
    let mut answers = IndexMap::new();
    for (id, question) in js_entries(&context.questions) {
        let Some(answer) = value.get(id).and_then(as_record) else {
            return Err(error(format!("{label} did not return an answer for {id}")));
        };
        let answer_type = answer.get("type").and_then(JsonValue::as_str);
        let parsed = match question {
            ClassifierQuestion::Choice { .. } => {
                let choice = answer.get("choice").and_then(JsonValue::as_str);
                let (Some("choice"), Some(choice)) = (answer_type, choice) else {
                    return Err(error(format!(
                        "{label} did not return a choice answer for {id}"
                    )));
                };
                ClassifierAnswer::Choice {
                    choice: choice.to_owned(),
                    probabilities: probabilities(label, answer.get("probabilities"), id)?,
                    confidence: required_number(
                        label,
                        answer.get("confidence"),
                        &format!("confidence for {id}"),
                    )?,
                }
            }
            ClassifierQuestion::Score { .. } => {
                if answer_type != Some("score") {
                    return Err(error(format!(
                        "{label} did not return a score answer for {id}"
                    )));
                }
                ClassifierAnswer::Score {
                    score: required_number(label, answer.get("score"), &format!("score for {id}"))?,
                    confidence: required_number(
                        label,
                        answer.get("confidence"),
                        &format!("confidence for {id}"),
                    )?,
                }
            }
            ClassifierQuestion::Bool { .. } => {
                if answer_type != Some("noul") {
                    return Err(error(format!(
                        "{label} did not return a bool answer for {id}"
                    )));
                }
                ClassifierAnswer::Bool {
                    probability: required_number(
                        label,
                        answer.get("noul"),
                        &format!("probability for {id}"),
                    )?,
                }
            }
        };
        answers.insert(id.clone(), parsed);
    }
    Ok(answers)
}

/// Maps public `bool` questions to `TypeSafe`'s wire-level `noul` type:
/// `{ state, questions }`.
fn wire_request(context: &ClassifierContext) -> JsonObject {
    let mut questions = JsonObject::new();
    for (id, question) in js_entries(&context.questions) {
        let mut value = serde_json::to_value(question).unwrap_or(JsonValue::Null);
        if matches!(question, ClassifierQuestion::Bool { .. }) {
            if let Some(object) = value.as_object_mut() {
                object.insert("type".to_owned(), JsonValue::from("noul"));
            }
        }
        questions.insert(id.clone(), value);
    }
    let mut request = JsonObject::new();
    request.insert("state".to_owned(), JsonValue::Object(context.state.clone()));
    request.insert("questions".to_owned(), JsonValue::Object(questions));
    request
}

/// Runs one System One classification over the given transport.
pub(crate) async fn classify_system_one(
    transport: &SystemOneTransport,
    model: ClassifierModel,
    context: ClassifierContext,
    options: ClassifierOptions,
) -> ClassifierResult {
    let mut output = empty_result(&model);
    if let Err(error) = run(transport, &model, &context, &options, &mut output).await {
        fail(
            &mut output,
            &options,
            &error,
            &format!("{} error", transport.label),
        );
    }
    output
}

async fn run(
    transport: &SystemOneTransport,
    model: &ClassifierModel,
    context: &ClassifierContext,
    options: &ClassifierOptions,
    output: &mut ClassifierResult,
) -> Result<(), Thrown> {
    if model.api != transport.api {
        return Err(error(format!("Unsupported classifier API: {}", model.api)));
    }
    if context
        .images
        .as_ref()
        .is_some_and(|images| !images.is_empty())
    {
        return Err(error(format!(
            "{} does not support image input",
            transport.label
        )));
    }
    let url = (transport.url)(model)?;
    let body = post_classifier_request(
        transport.label,
        &url,
        model,
        (transport.payload)(model, wire_request(context)),
        options,
        &[],
    )
    .await?;
    let result = (transport.output)(body)?;
    // Set before parsing answers: a request with malformed answers was still billed.
    if let Some(usage) = parse_classifier_usage(result.get("usage"), model) {
        output.usage = Some(usage);
    }
    output.answers = parse_answers(transport.label, result.get("answers"), context)?;
    Ok(())
}

#[cfg(test)]
#[path = "system_one_test_fetch.rs"]
pub(crate) mod test_fetch;
