//! Port of `test/typesafe-system-one.test.ts` and the custom-fetch Jev
//! routing cases of `test/classifier-models.test.ts`.

use std::future::pending;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use eukhe_types::pi_ai::{
    ClassifierAnswer, ClassifierContext, ClassifierModel, ClassifierStopReason, JsonValue,
    ModelType,
};
use serde_json::json;

use super::classifier;
use crate::api::system_one_shared::test_fetch::{json_response, mock_fetch, recorded, response};
use crate::models::CreateModelsOptions;
use crate::providers::all::builtin_models;
use crate::types::{ClassifierOptions, FetchFunction, ProviderRequestOptions};

fn model() -> ClassifierModel {
    serde_json::from_value(json!({
        "type": "classifier",
        "id": "jev-latest",
        "name": "Jev",
        "api": "typesafe-system-one",
        "provider": "typesafe",
        "baseUrl": "https://api.typesafe.ai/v1/",
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 64000,
    }))
    .expect("model")
}

fn context() -> ClassifierContext {
    serde_json::from_value(json!({
        "state": { "text": "The deployment succeeded, thank you." },
        "questions": {
            "category": {
                "type": "choice",
                "instructions": "Classify the message",
                "criteria": { "success": "Successful", "failure": "Failed" },
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
    }))
    .expect("context")
}

fn wire_answers() -> JsonValue {
    json!({
        "category": {
            "type": "choice",
            "choice": "success",
            "probabilities": { "success": 0.9, "failure": 0.1 },
            "confidence": 0.8,
        },
        "satisfaction": { "type": "score", "score": 2, "confidence": 0.7 },
        "approved": { "type": "noul", "noul": 0.95 },
    })
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

async fn classify(
    model: &ClassifierModel,
    context: &ClassifierContext,
    options: ClassifierOptions,
) -> eukhe_types::pi_ai::ClassifierResult {
    (classifier().classify)(model, context, options).await
}

#[tokio::test]
async fn maps_public_bool_questions_and_answers_to_typesafe_noul_values() {
    let (fetch, requests) =
        mock_fetch(|_| json_response(200, &json!({ "answers": wire_answers() })));
    let mut first = options(fetch);
    first.temperature = Some(1.5);
    let result = classify(&model(), &context(), first).await;

    let mut priced_model = model();
    priced_model.cost.input = 0.042;
    let (priced_fetch, _) = mock_fetch(|_| {
        json_response(
            200,
            &json!({ "answers": wire_answers(), "usage": { "input_tokens": 308, "output_tokens": 23 } }),
        )
    });
    let priced = classify(&priced_model, &context(), options(priced_fetch)).await;

    let requests = recorded(&requests);
    assert_eq!(requests.len(), 1);
    let payload = requests[0].json();
    assert_eq!(payload["model"], "jev-latest");
    assert_eq!(payload["questions"]["category"]["type"], "choice");
    assert_eq!(payload["questions"]["satisfaction"]["type"], "score");
    assert_eq!(payload["questions"]["approved"]["type"], "noul");
    // System One has no temperature field; the option is ignored.
    assert!(payload.get("temperature").is_none());
    assert_eq!(requests[0].header("authorization"), Some("Bearer secret"));
    assert_eq!(requests[0].url, "https://api.typesafe.ai/v1/systemone");

    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(
        result.answers["approved"],
        ClassifierAnswer::Bool { probability: 0.95 }
    );
    assert!(matches!(
        &result.answers["category"],
        ClassifierAnswer::Choice { choice, .. } if choice == "success"
    ));
    assert_eq!(
        result.answers["satisfaction"],
        ClassifierAnswer::Score {
            score: 2.0,
            confidence: 0.7
        }
    );
    assert_eq!(result.usage, None);
    let usage = priced.usage.expect("usage");
    assert_eq!(
        (usage.input, usage.output, usage.total_tokens),
        (308, 23, 331)
    );
    assert!((usage.cost.total - 0.000_012_936).abs() < 5e-13);
}

#[tokio::test]
async fn posts_openrouter_system_one_requests_to_its_typesafe_compatible_endpoint() {
    let (fetch, requests) = mock_fetch(|_| {
        // Response shape observed from the live OpenRouter endpoint.
        json_response(
            200,
            &json!({
                "id": "gen-dec-1",
                "provider": "TypeSafe",
                "answers": wire_answers(),
                "usage": { "input_tokens": 308, "output_tokens": 23, "cost": 0.000_012_936 },
            }),
        )
    });
    let mut open_router_model = model();
    open_router_model.id = "typesafe/jev-1.13".to_owned();
    open_router_model.provider = "openrouter".to_owned();
    open_router_model.base_url = "https://openrouter.ai/api/v1".to_owned();
    open_router_model.cost.input = 0.042;

    let result = classify(&open_router_model, &context(), options(fetch)).await;

    let requests = recorded(&requests);
    let payload = requests[0].json();
    assert_eq!(payload["model"], "typesafe/jev-1.13");
    assert_eq!(payload["state"], json!(context().state));
    assert_eq!(requests[0].url, "https://openrouter.ai/api/v1/systemone");
    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(
        result.answers["approved"],
        ClassifierAnswer::Bool { probability: 0.95 }
    );
    // Priced from the catalog like chat usage; matches OpenRouter's reported cost.
    assert!((result.usage.expect("usage").cost.total - 0.000_012_936).abs() < 5e-13);
}

#[tokio::test]
async fn rejects_models_for_other_classifier_apis() {
    let (fetch, requests) =
        mock_fetch(|_| json_response(200, &json!({ "answers": wire_answers() })));
    let mut other = model();
    other.api = "cloudflare-workers-ai-system-one".to_owned();
    let result = classify(&other, &context(), options(fetch)).await;

    assert!(recorded(&requests).is_empty());
    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert!(result
        .error_message
        .expect("message")
        .contains("Unsupported classifier API: cloudflare-workers-ai-system-one"));
}

#[tokio::test]
async fn merges_headers_case_insensitively_and_supports_null_suppression() {
    let (fetch, requests) =
        mock_fetch(|_| json_response(200, &json!({ "answers": wire_answers() })));
    let mut with_headers = model();
    with_headers.headers = Some(
        [
            ("authorization".to_owned(), "Bearer model".to_owned()),
            ("X-Source".to_owned(), "model".to_owned()),
        ]
        .into_iter()
        .collect(),
    );

    let mut first = options(Arc::clone(&fetch));
    first.request.headers = Some(
        [
            (
                "Authorization".to_owned(),
                Some("Bearer request".to_owned()),
            ),
            ("x-source".to_owned(), Some("request".to_owned())),
        ]
        .into_iter()
        .collect(),
    );
    classify(&with_headers, &context(), first).await;
    let mut second = options(fetch);
    second.request.headers = Some([("Authorization".to_owned(), None)].into_iter().collect());
    classify(&with_headers, &context(), second).await;

    let requests = recorded(&requests);
    assert_eq!(requests[0].header("authorization"), Some("Bearer request"));
    assert_eq!(requests[0].header("x-source"), Some("request"));
    assert_eq!(
        requests[0].headers.get_all("authorization").iter().count(),
        1
    );
    assert_eq!(requests[1].header("authorization"), None);
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
            &json!({ "answers": { "__proto__": { "type": "noul", "noul": 0.75 } } }),
        )
    });
    let result = classify(&model(), &prototype_context, options(fetch)).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(result.answers.keys().collect::<Vec<_>>(), ["__proto__"]);
    assert_eq!(
        result.answers["__proto__"],
        ClassifierAnswer::Bool { probability: 0.75 }
    );
    assert_eq!(
        serde_json::to_value(&result.answers).expect("serialize")["__proto__"],
        json!({ "type": "bool", "probability": 0.75 })
    );
}

#[tokio::test]
async fn reports_request_timeouts_separately_from_caller_cancellation() {
    let fetch: FetchFunction = Arc::new(|_| Box::pin(pending()));
    let mut timed = options(fetch);
    timed.request.timeout_ms = Some(5.0);
    timed.request.max_retries = Some(0);
    let result = classify(&model(), &context(), timed).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert_eq!(
        result.error_message.as_deref(),
        Some("Request timed out after 5ms")
    );
}

/// Rust `fetch` has no per-request signal object; the observable equivalent
/// is that the second attempt runs (and succeeds) under its own timeout.
#[tokio::test]
async fn creates_a_fresh_timeout_for_every_retry_attempt() {
    let attempts = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&attempts);
    let (fetch, requests) = mock_fetch(move |_| {
        if counter.fetch_add(1, Ordering::SeqCst) == 0 {
            response(500, &[("retry-after-ms", "0")], "retry".to_owned())
        } else {
            json_response(200, &json!({ "answers": wire_answers() }))
        }
    });
    let mut retried = options(fetch);
    retried.request.timeout_ms = Some(1000.0);
    retried.request.max_retries = Some(1);
    let result = classify(&model(), &context(), retried).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(recorded(&requests).len(), 2);
}

#[tokio::test]
async fn returns_malformed_responses_as_classifier_errors() {
    let (fetch, _) = mock_fetch(|_| {
        json_response(
            200,
            &json!({ "answers": {}, "usage": { "input_tokens": 10, "output_tokens": 2 } }),
        )
    });
    let result = classify(&model(), &context(), options(fetch)).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert!(result.answers.is_empty());
    assert!(result
        .error_message
        .expect("message")
        .contains("did not return an answer for category"));
    // The request was billed, so its usage is kept.
    let usage = result.usage.expect("usage");
    assert_eq!((usage.input, usage.output), (10, 2));
}

#[tokio::test]
async fn ignores_malformed_usage() {
    let (fetch, _) = mock_fetch(|_| {
        json_response(
            200,
            &json!({ "answers": wire_answers(), "usage": { "input_tokens": "many", "output_tokens": 3 } }),
        )
    });
    let result = classify(&model(), &context(), options(fetch)).await;
    let (fetch, _) = mock_fetch(|_| {
        json_response(
            200,
            &json!({ "answers": wire_answers(), "usage": { "cost": 0.1 } }),
        )
    });
    let without_tokens = classify(&model(), &context(), options(fetch)).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    let usage = result.usage.expect("usage");
    assert_eq!((usage.input, usage.output, usage.total_tokens), (0, 3, 3));
    assert_eq!(without_tokens.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(without_tokens.usage, None);
}

async fn routes_jev_to_its_typesafe_compatible_endpoint(provider: &str, id: &str, url: &str) {
    let models = builtin_models(CreateModelsOptions::default());
    let Some(eukhe_types::pi_ai::AnyModel::Classifier(jev)) =
        models.get_model_of_type(ModelType::Classifier, provider, id)
    else {
        panic!("missing {provider} Jev model");
    };
    assert_eq!(jev.api, "typesafe-system-one");
    assert_eq!(jev.context_window, 32000);
    assert!(models.get_model(provider, id).is_none());

    let context: ClassifierContext = serde_json::from_value(json!({
        "state": { "text": "yes" },
        "questions": {
            "approved": {
                "type": "bool",
                "instructions": "Does this express approval?",
                "criteria": { "true": "Approval", "false": "No approval" },
            },
        },
    }))
    .expect("context");
    let reply_id = id.to_owned();
    let (fetch, requests) = mock_fetch(move |_| {
        json_response(
            200,
            &json!({ "model": reply_id, "answers": { "approved": { "type": "noul", "noul": 0.8 } } }),
        )
    });
    let result = models.classify(&jev, &context, options(fetch).into()).await;

    let requests = recorded(&requests);
    assert_eq!(requests.len(), 1);
    assert_eq!(requests[0].url, url);
    let body = requests[0].json();
    assert_eq!(body["model"], id);
    assert_eq!(body["state"], json!(context.state));
    assert_eq!(requests[0].header("authorization"), Some("Bearer secret"));
    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(
        result.answers["approved"],
        ClassifierAnswer::Bool { probability: 0.8 }
    );
}

#[tokio::test]
async fn routes_vercel_ai_gateway_jev_to_its_typesafe_compatible_endpoint() {
    routes_jev_to_its_typesafe_compatible_endpoint(
        "vercel-ai-gateway",
        "typesafe-ai/jev",
        "https://ai-gateway.vercel.sh/typesafe/v1/systemone",
    )
    .await;
}

#[tokio::test]
async fn routes_opencode_jev_to_its_typesafe_compatible_endpoint() {
    routes_jev_to_its_typesafe_compatible_endpoint(
        "opencode",
        "jev-1.13",
        "https://opencode.ai/zen/v1/systemone",
    )
    .await;
}

#[tokio::test]
async fn routes_opencode_free_jev_to_its_typesafe_compatible_endpoint() {
    routes_jev_to_its_typesafe_compatible_endpoint(
        "opencode",
        "jev-1.13-free",
        "https://opencode.ai/zen/v1/systemone",
    )
    .await;
}
