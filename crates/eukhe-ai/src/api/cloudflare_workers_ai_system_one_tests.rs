//! Port of `test/cloudflare-workers-ai-system-one.test.ts`.

use eukhe_types::pi_ai::{
    AnyModel, ClassifierAnswer, ClassifierContext, ClassifierModel, ClassifierStopReason,
    JsonValue, ModelType,
};
use serde_json::json;

use crate::api::system_one_shared::test_fetch::{json_response, mock_fetch, recorded};
use crate::models::{create_models, CreateModelsOptions, Models};
use crate::providers::all::get_builtin_classifier_model;
use crate::providers::cloudflare_workers_ai::cloudflare_workers_ai_provider;
use crate::types::{ClassifierOptions, FetchFunction, ProviderRequestOptions};

fn context() -> ClassifierContext {
    serde_json::from_value(json!({
        "state": { "message": "Help! My payouts have been failing for 3 days." },
        "questions": {
            "is_urgent": {
                "type": "bool",
                "instructions": "Does this convey urgency?",
                "criteria": { "true": "Explicitly time-sensitive", "false": "No urgency expressed" },
            },
            "department": {
                "type": "choice",
                "instructions": "Which team should handle this?",
                "criteria": { "billing": "Payments", "technical": "Bugs" },
            },
        },
    }))
    .expect("context")
}

/// Model output from <https://developers.cloudflare.com/ai/models/typesafe/jev/>.
fn jev_output() -> JsonValue {
    json!({
        "model": "jev-1.13.0",
        "answers": {
            "is_urgent": { "type": "noul", "noul": 0.95 },
            "department": {
                "type": "choice",
                "choice": "billing",
                "confidence": 0.8,
                "probabilities": { "billing": 0.87, "technical": 0.13 },
            },
        },
        "usage": { "input_tokens": 426, "output_tokens": 73 },
    })
}

/// REST envelope observed from the live /ai/run endpoint.
fn rest_response(state: &str, result: &JsonValue) -> JsonValue {
    json!({
        "result": { "state": state, "result": result, "gatewayMetadata": { "keySource": "Unified" } },
        "success": true,
        "errors": [],
        "messages": [],
    })
}

/// Cloudflare-hosted output observed from a live /ai/run call; the envelope
/// carries the output directly, without a run record.
fn clef_output() -> JsonValue {
    json!({
        "model": "clef",
        "answers": {
            "is_urgent": { "type": "noul", "noul": 0.9912 },
            "department": {
                "type": "choice",
                "choice": "technical",
                "probabilities": { "billing": 0.1632, "technical": 0.8368 },
                "confidence": 0.4538,
            },
        },
        "usage": { "input_tokens": 222, "output_tokens": 0 },
    })
}

fn classifier_model(models: &Models, id: &str) -> Option<ClassifierModel> {
    match models.get_model_of_type(ModelType::Classifier, "cloudflare-workers-ai", id) {
        Some(AnyModel::Classifier(model)) => Some(model),
        _ => None,
    }
}

fn setup() -> (Models, ClassifierModel) {
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(cloudflare_workers_ai_provider());
    let jev = classifier_model(&models, "typesafe/jev").expect("missing Cloudflare Jev model");
    (models, jev)
}

fn auth(fetch: FetchFunction) -> ClassifierOptions {
    ClassifierOptions {
        request: ProviderRequestOptions {
            api_key: Some("cf-key".to_owned()),
            env: Some(
                [("CLOUDFLARE_ACCOUNT_ID".to_owned(), "account-id".to_owned())]
                    .into_iter()
                    .collect(),
            ),
            fetch: Some(fetch),
            ..ProviderRequestOptions::default()
        },
        temperature: None,
    }
}

#[test]
fn exposes_jev_only_through_classifier_catalog_accessors() {
    let (models, jev) = setup();
    assert_eq!(
        Some(&jev),
        get_builtin_classifier_model("cloudflare-workers-ai", "typesafe/jev").as_ref()
    );
    assert_eq!(jev.api, "cloudflare-workers-ai-system-one");
    assert!(models
        .get_model("cloudflare-workers-ai", "typesafe/jev")
        .is_none());
}

#[tokio::test]
async fn runs_jev_through_the_account_scoped_ai_run_endpoint() {
    let (models, jev) = setup();
    let (fetch, requests) =
        mock_fetch(|_| json_response(200, &rest_response("Completed", &jev_output())));

    let result = models.classify(&jev, &context(), auth(fetch).into()).await;

    let requests = recorded(&requests);
    let payload = requests[0].json();
    assert_eq!(payload["model"], "typesafe/jev");
    assert_eq!(payload["input"]["state"], json!(context().state));
    assert_eq!(payload["input"]["questions"]["is_urgent"]["type"], "noul");
    assert_eq!(
        payload["input"]["questions"]["department"]["type"],
        "choice"
    );
    assert_eq!(requests[0].header("authorization"), Some("Bearer cf-key"));
    assert_eq!(
        requests[0].url,
        "https://api.cloudflare.com/client/v4/accounts/account-id/ai/run"
    );
    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(
        result.answers["is_urgent"],
        ClassifierAnswer::Bool { probability: 0.95 }
    );
    assert!(matches!(
        &result.answers["department"],
        ClassifierAnswer::Choice { choice, confidence, .. } if choice == "billing" && (*confidence - 0.8).abs() < f64::EPSILON
    ));
    let usage = result.usage.expect("usage");
    assert_eq!(
        (usage.input, usage.output, usage.total_tokens),
        (426, 73, 499)
    );
}

async fn runs_clef_through_ai_run_and_parses_its_direct_output(id: &str, input_price: f64) {
    let (models, _) = setup();
    let clef = classifier_model(&models, id).expect("missing Cloudflare clef model");
    let (fetch, requests) = mock_fetch(|_| {
        json_response(
            200,
            &json!({ "result": clef_output(), "success": true, "errors": [], "messages": [] }),
        )
    });

    let result = models.classify(&clef, &context(), auth(fetch).into()).await;

    let requests = recorded(&requests);
    let payload = requests[0].json();
    assert_eq!(payload["model"], id);
    assert_eq!(payload["input"]["state"], json!(context().state));
    assert_eq!(payload["input"]["questions"]["is_urgent"]["type"], "noul");
    assert_eq!(
        requests[0].url,
        "https://api.cloudflare.com/client/v4/accounts/account-id/ai/run"
    );
    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(
        result.answers["is_urgent"],
        ClassifierAnswer::Bool {
            probability: 0.9912
        }
    );
    assert!(matches!(
        &result.answers["department"],
        ClassifierAnswer::Choice { choice, confidence, .. } if choice == "technical" && (*confidence - 0.4538).abs() < f64::EPSILON
    ));
    let usage = result.usage.expect("usage");
    assert_eq!(
        (usage.input, usage.output, usage.total_tokens),
        (222, 0, 222)
    );
    assert!((usage.cost.input - 222.0 * input_price / 1_000_000.0).abs() < 5e-3);
}

#[tokio::test]
async fn runs_cf_cloudflare_clef_through_ai_run_and_parses_its_direct_output() {
    runs_clef_through_ai_run_and_parses_its_direct_output("@cf/cloudflare/clef", 0.24).await;
}

#[tokio::test]
async fn runs_cf_cloudflare_clef_flash_through_ai_run_and_parses_its_direct_output() {
    runs_clef_through_ai_run_and_parses_its_direct_output("@cf/cloudflare/clef-flash", 0.09).await;
}

#[tokio::test]
async fn reports_runs_that_did_not_complete() {
    let (models, jev) = setup();
    let (fetch, _) = mock_fetch(|_| json_response(200, &rest_response("Queued", &JsonValue::Null)));
    let result = models.classify(&jev, &context(), auth(fetch).into()).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert!(result
        .error_message
        .expect("message")
        .contains("run did not complete (state: Queued)"));
}

#[tokio::test]
async fn reports_cloudflare_envelope_errors() {
    let (models, jev) = setup();
    let (fetch, _) = mock_fetch(|_| {
        json_response(
            200,
            &json!({ "success": false, "errors": [{ "code": 5007, "message": "No such model" }], "result": null }),
        )
    });
    let result = models.classify(&jev, &context(), auth(fetch).into()).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert!(result
        .error_message
        .expect("message")
        .contains("Cloudflare Workers AI error: No such model"));
}
