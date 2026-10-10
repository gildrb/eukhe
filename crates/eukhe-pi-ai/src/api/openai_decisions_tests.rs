//! Port of `test/openai-decisions.test.ts` and the custom-fetch half of
//! "routes `OpenAI` GPT-6 Luna through the Decisions API with images" from
//! `test/classifier-models.test.ts`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use eukhe_types::pi_ai::{
    AnyModel, ClassifierAnswer, ClassifierContext, ClassifierModel, ClassifierResult,
    ClassifierStopReason, JsonValue, ModelType,
};
use serde_json::json;

use super::classifier;
use crate::api::system_one_shared::test_fetch::{json_response, mock_fetch, recorded, response};
use crate::models::CreateModelsOptions;
use crate::providers::all::builtin_models;
use crate::types::{ClassifierOptions, FetchFunction, ProviderRequestOptions};
use crate::utils::js::json_stringify;

fn model() -> ClassifierModel {
    serde_json::from_value(json!({
        "type": "classifier",
        "id": "gpt-6-luna",
        "name": "GPT-6 Luna",
        "api": "openai-decisions",
        "provider": "openai",
        "baseUrl": "https://api.openai.com/v1",
        "input": ["text", "image"],
        "cost": {
            "input": 0.1,
            "output": 0,
            "cacheRead": 0,
            "cacheWrite": 0,
            "tiers": [{ "inputTokensAbove": 272_000, "input": 0.2, "output": 0, "cacheRead": 0, "cacheWrite": 0 }],
        },
        "contextWindow": 922_000,
    }))
    .expect("model")
}

fn context_json() -> JsonValue {
    json!({
        "state": { "text": "The deployment succeeded, thank you." },
        "questions": {
            "category": {
                "type": "choice",
                "instructions": "Classify the message",
                "criteria": { "success": "Successful", "failure": "" },
            },
            "satisfaction": {
                "type": "score",
                "instructions": "Score satisfaction",
                "criteria": ["low", "neutral", "high"],
            },
            "approved": {
                "type": "bool",
                "instructions": "Does the user approve?",
                "criteria": { "true": "Approval", "false": "No approval" },
            },
        },
    })
}

fn context() -> ClassifierContext {
    serde_json::from_value(context_json()).expect("context")
}

fn context_with_images(images: JsonValue) -> ClassifierContext {
    let mut value = context_json();
    value["images"] = images;
    serde_json::from_value(value).expect("context")
}

fn state_text() -> String {
    json_stringify(&context_json()["state"])
}

/// Response shape from the API reference and live `gpt-6-luna` requests.
fn wire_answers() -> Vec<JsonValue> {
    vec![
        json!({
            "type": "choice",
            "name": "category",
            "choice": "success",
            "probabilities": [
                { "value": "success", "probability": 0.9 },
                { "value": "failure", "probability": 0.1 },
            ],
            "confidence": 0.8,
        }),
        json!({
            "type": "score",
            "name": "satisfaction",
            "score": 1.8,
            "probabilities": [
                { "value": 0, "label": "low", "probability": 0.05 },
                { "value": 1, "label": "neutral", "probability": 0.1 },
                { "value": 2, "label": "high", "probability": 0.85 },
            ],
            "confidence": 0.7,
        }),
        json!({ "type": "predicate", "name": "approved", "probability": 0.95 }),
    ]
}

fn wire_usage() -> JsonValue {
    json!({
        "input_tokens": 164,
        "input_tokens_details": { "cached_tokens": 0, "cache_write_tokens": 0 },
        "output_tokens": 0,
        "output_tokens_details": { "reasoning_tokens": 0 },
        "total_tokens": 164,
    })
}

fn image() -> JsonValue {
    json!({ "type": "image", "data": "aW1hZ2U=", "mimeType": "image/png" })
}

fn options(fetch: FetchFunction) -> ClassifierOptions {
    ClassifierOptions {
        request: ProviderRequestOptions {
            api_key: Some("secret".to_owned()),
            fetch: Some(fetch),
            ..ProviderRequestOptions::default()
        },
        temperature: None,
    }
}

fn answers_fetch() -> (
    FetchFunction,
    crate::api::system_one_shared::test_fetch::Requests,
) {
    mock_fetch(|_| json_response(200, &json!({ "answers": wire_answers() })))
}

async fn classify(
    model: &ClassifierModel,
    context: &ClassifierContext,
    options: ClassifierOptions,
) -> ClassifierResult {
    (classifier().classify)(model, context, options).await
}

fn message(result: &ClassifierResult) -> &str {
    result.error_message.as_deref().expect("error message")
}

#[tokio::test]
async fn maps_questions_to_decisions_types_and_answers_back_by_name() {
    let (fetch, requests) = mock_fetch(|_| {
        // Answers out of question order: they are matched by name.
        let mut answers = wire_answers();
        answers.reverse();
        json_response(
            200,
            &json!({ "model": "gpt-6-luna", "answers": answers, "usage": wire_usage() }),
        )
    });
    let mut first = options(fetch);
    first.temperature = Some(1.5);
    let result = classify(&model(), &context(), first).await;

    let requests = recorded(&requests);
    assert_eq!(requests.len(), 1);
    assert_eq!(requests[0].url, "https://api.openai.com/v1/decisions");
    assert_eq!(requests[0].header("authorization"), Some("Bearer secret"));
    assert_eq!(
        requests[0].json(),
        json!({
            "model": "gpt-6-luna",
            "input": state_text(),
            "questions": [
                {
                    "type": "choice",
                    "name": "category",
                    "instructions": "Classify the message",
                    // Empty descriptions are omitted.
                    "choices": [{ "value": "success", "description": "Successful" }, { "value": "failure" }],
                },
                {
                    "type": "score",
                    "name": "satisfaction",
                    "instructions": "Score satisfaction",
                    "levels": [{ "label": "low" }, { "label": "neutral" }, { "label": "high" }],
                },
                {
                    "type": "predicate",
                    "name": "approved",
                    "instructions": "Does the user approve?\n\nTrue means: Approval\nFalse means: No approval",
                },
            ],
        })
    );
    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(result.answers.len(), 3);
    match &result.answers["category"] {
        ClassifierAnswer::Choice {
            choice,
            probabilities,
            confidence,
        } => {
            assert_eq!(choice, "success");
            assert_eq!(
                probabilities
                    .iter()
                    .map(|(k, v)| (k.as_str(), *v))
                    .collect::<Vec<_>>(),
                [("success", 0.9), ("failure", 0.1)]
            );
            assert!((confidence - 0.8).abs() < f64::EPSILON);
        }
        other => panic!("unexpected category answer {other:?}"),
    }
    assert_eq!(
        result.answers["satisfaction"],
        ClassifierAnswer::Score {
            score: 1.8,
            confidence: 0.7
        }
    );
    assert_eq!(
        result.answers["approved"],
        ClassifierAnswer::Bool { probability: 0.95 }
    );
    let usage = result.usage.expect("usage");
    assert_eq!(
        (
            usage.input,
            usage.output,
            usage.cache_read,
            usage.total_tokens
        ),
        (164, 0, 0, 164)
    );
    assert!((usage.cost.total - 0.000_016_4).abs() < 5e-13);
}

#[tokio::test]
async fn prices_long_context_requests_at_the_long_context_input_rate() {
    let (fetch, _) = mock_fetch(|_| {
        json_response(
            200,
            &json!({ "answers": wire_answers(), "usage": { "input_tokens": 300_000, "output_tokens": 0 } }),
        )
    });
    let result = classify(&model(), &context(), options(fetch)).await;

    assert!((result.usage.expect("usage").cost.total - 0.06).abs() < 5e-13);
}

#[tokio::test]
async fn sends_images_after_the_state_in_one_user_message() {
    let (fetch, requests) = answers_fetch();
    let mut jpeg = image();
    jpeg["mimeType"] = json!("image/jpeg");
    let result = classify(
        &model(),
        &context_with_images(json!([image(), jpeg])),
        options(fetch),
    )
    .await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(
        recorded(&requests)[0].json()["input"],
        json!([
            {
                "role": "user",
                "content": [
                    { "type": "input_text", "text": state_text() },
                    { "type": "input_image", "image_url": "data:image/png;base64,aW1hZ2U=" },
                    { "type": "input_image", "image_url": "data:image/jpeg;base64,aW1hZ2U=" },
                ],
            },
        ])
    );
}

#[tokio::test]
async fn rejects_more_than_128_images_before_sending() {
    let (fetch, requests) = answers_fetch();
    let images: Vec<JsonValue> = (0..129).map(|_| image()).collect();
    let result = classify(
        &model(),
        &context_with_images(JsonValue::Array(images)),
        options(fetch),
    )
    .await;

    assert!(recorded(&requests).is_empty());
    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert!(message(&result).contains("at most 128 images, got 129"));
}

#[tokio::test]
async fn fails_the_result_when_a_question_is_refused_and_keeps_the_billed_usage() {
    let (fetch, _) = mock_fetch(|_| {
        let answers = wire_answers();
        json_response(
            200,
            &json!({
                "answers": [answers[0], answers[1], { "type": "refusal", "name": "approved" }],
                "usage": wire_usage(),
            }),
        )
    });
    let result = classify(&model(), &context(), options(fetch)).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert!(result.answers.is_empty());
    assert_eq!(
        message(&result),
        "OpenAI Decisions refused to answer approved"
    );
    assert_eq!(result.usage.expect("usage").input, 164);
}

#[tokio::test]
async fn returns_missing_and_mistyped_answers_as_classifier_errors() {
    let (fetch, _) = mock_fetch(|_| json_response(200, &json!({ "answers": wire_answers()[..2] })));
    let missing = classify(&model(), &context(), options(fetch)).await;
    let (fetch, _) = mock_fetch(|_| {
        let answers = wire_answers();
        json_response(
            200,
            &json!({ "answers": [answers[0], answers[1], { "type": "score", "name": "approved" }] }),
        )
    });
    let mistyped = classify(&model(), &context(), options(fetch)).await;

    assert_eq!(missing.stop_reason, ClassifierStopReason::Error);
    assert!(message(&missing).contains("did not return an answer for approved"));
    assert_eq!(mistyped.stop_reason, ClassifierStopReason::Error);
    assert!(message(&mistyped).contains("did not return a predicate answer for approved"));
}

#[tokio::test]
async fn preserves_prototype_sensitive_question_ids_in_answers() {
    let prototype_context: ClassifierContext = serde_json::from_value(json!({
        "state": {},
        "questions": {
            "__proto__": {
                "type": "bool",
                "instructions": "Is this true?",
                "criteria": { "true": "Yes", "false": "No" },
            },
        },
    }))
    .expect("context");
    let (fetch, _) = mock_fetch(|_| {
        json_response(
            200,
            &json!({ "answers": [{ "type": "predicate", "name": "__proto__", "probability": 0.75 }] }),
        )
    });
    let result = classify(&model(), &prototype_context, options(fetch)).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(
        result.answers.get("__proto__"),
        Some(&ClassifierAnswer::Bool { probability: 0.75 })
    );
}

#[tokio::test]
async fn does_not_retry_gateway_timeouts_and_explains_them_instead_of_returning_the_html_page() {
    let (fetch, requests) = mock_fetch(|_| {
        response(
            504,
            &[("retry-after-ms", "0")],
            "<!DOCTYPE html><html>Gateway time-out</html>".to_owned(),
        )
    });
    // Default retries: the same input would time out again.
    let result = classify(&model(), &context(), options(fetch)).await;

    assert_eq!(recorded(&requests).len(), 1);
    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert!(message(&result)
        .contains("OpenAI Decisions error (504): the request timed out at the gateway"));
    assert!(!message(&result).contains("<html>"));
}

#[tokio::test]
async fn still_retries_other_server_errors() {
    let attempts = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&attempts);
    let (fetch, _) = mock_fetch(move |_| {
        if counter.fetch_add(1, Ordering::SeqCst) == 0 {
            response(503, &[("retry-after-ms", "0")], "busy".to_owned())
        } else {
            json_response(200, &json!({ "answers": wire_answers() }))
        }
    });
    let result = classify(&model(), &context(), options(fetch)).await;

    assert_eq!(attempts.load(Ordering::SeqCst), 2);
    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
}

#[tokio::test]
async fn includes_the_api_error_body_for_other_http_failures() {
    let (fetch, _) = mock_fetch(|_| {
        json_response(
            400,
            &json!({ "error": { "message": "Decision input exceeds the token limit.", "type": "invalid_request_error" } }),
        )
    });
    let mut no_retries = options(fetch);
    no_retries.request.max_retries = Some(0);
    let result = classify(&model(), &context(), no_retries).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert!(message(&result).contains("OpenAI Decisions error (400)"));
    assert!(message(&result).contains("Decision input exceeds the token limit."));
}

#[tokio::test]
async fn rejects_models_for_other_classifier_apis_and_missing_api_keys() {
    let (fetch, requests) = answers_fetch();
    let mut other = model();
    other.api = "typesafe-system-one".to_owned();
    let other_api = classify(&other, &context(), options(Arc::clone(&fetch))).await;
    let mut no_key = options(fetch);
    no_key.request.api_key = None;
    let no_key = classify(&model(), &context(), no_key).await;

    assert!(recorded(&requests).is_empty());
    assert!(message(&other_api).contains("Unsupported classifier API: typesafe-system-one"));
    assert!(message(&no_key).contains("No API key for provider: openai"));
}

/// Custom-fetch half of the `classifier-models` case "routes `OpenAI` GPT-6
/// Luna through the Decisions API with images".
#[tokio::test]
async fn routes_openai_gpt_6_luna_through_the_decisions_api_with_images() {
    let models = builtin_models(CreateModelsOptions::default());
    let Some(AnyModel::Classifier(luna)) =
        models.get_model_of_type(ModelType::Classifier, "openai", "gpt-6-luna")
    else {
        panic!("missing OpenAI Decisions model");
    };
    let context: ClassifierContext = serde_json::from_value(json!({
        "state": { "text": "yes" },
        "questions": {
            "approved": {
                "type": "bool",
                "instructions": "Does this express approval?",
                "criteria": { "true": "Approval", "false": "No approval" },
            },
        },
        "images": [image()],
    }))
    .expect("context");
    let (fetch, requests) = mock_fetch(|_| {
        json_response(
            200,
            &json!({ "answers": [{ "type": "predicate", "name": "approved", "probability": 0.8 }] }),
        )
    });
    let result = models
        .classify(&luna, &context, options(fetch).into())
        .await;

    let urls: Vec<String> = recorded(&requests)
        .into_iter()
        .map(|request| request.url)
        .collect();
    assert_eq!(urls, ["https://api.openai.com/v1/decisions"]);
    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(
        result.answers["approved"],
        ClassifierAnswer::Bool { probability: 0.8 }
    );
}
