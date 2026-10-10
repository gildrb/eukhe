//! Port of `test/classifier-models.test.ts`.
//!
//! "rejects chat models at the classifier entry point at runtime" casts a
//! chat model to a classifier model; Rust's `Models::classify` takes a
//! `&ClassifierModel`, so the closest Rust-observable equivalent checks the
//! runtime narrowing `classify` performs. The `fetch` halves of the Jev
//! routing cases and of "routes `OpenAI` GPT-6 Luna through the Decisions API
//! with images" are deferred to the `typesafe-system-one` and
//! `openai-decisions` modules (the mock `fetch` helpers are crate-private).

mod common;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use common::{
    ambient_auth, api_key, assert_json_eq, assert_match_object, now, now_f64, oauth,
    silent_streams, store,
};
use eukhe_pi_ai::api::ProviderClassifier;
use eukhe_pi_ai::auth::{AuthOperationOptions, InMemoryCredentialStore, ProviderAuth};
use eukhe_pi_ai::models::{
    create_models, create_provider, get_model_type, CreateModelsOptions, CreateProviderOptions,
    ModelsClassifierOptions, ProviderApi,
};
use eukhe_pi_ai::providers::all::{
    builtin_models, get_all_builtin_models, get_builtin_classifier_model,
    get_builtin_classifier_models,
};
use eukhe_pi_ai::utils::model_operations::assert_classifier_model;
use eukhe_types::pi_ai::{
    AnyModel, ClassifierContext, ClassifierModel, ClassifierResult, ClassifierStopReason, IndexMap,
    Model, ModelType,
};
use serde_json::json;

fn classifier_model(provider: &str, id: &str) -> ClassifierModel {
    serde_json::from_value(json!({
        "type": "classifier",
        "id": id,
        "name": id,
        "api": "test-classifier",
        "provider": provider,
        "baseUrl": "https://example.test/v1",
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1000,
    }))
    .expect("classifier model")
}

fn chat_model(provider: &str, id: &str) -> Model {
    serde_json::from_value(json!({
        "id": id,
        "name": id,
        "api": "test-chat",
        "provider": provider,
        "baseUrl": "https://example.test/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1000,
        "maxTokens": 100,
    }))
    .expect("chat model")
}

fn context() -> ClassifierContext {
    serde_json::from_value(json!({
        "state": { "text": "yes" },
        "questions": {
            "approved": {
                "type": "bool",
                "instructions": "Does this express approval?",
                "criteria": { "true": "Approval", "false": "No approval" },
            },
        },
    }))
    .expect("classifier context")
}

fn ambient() -> ProviderAuth {
    ProviderAuth {
        api_key: Some(ambient_auth()),
        oauth: None,
    }
}

#[tokio::test]
async fn keeps_chat_and_classifier_entries_with_the_same_provider_and_id_separate() {
    let chat = chat_model("test", "shared");
    let classifier = classifier_model("test", "shared");
    let classify: eukhe_pi_ai::api::ClassifyFn = Arc::new(|model: &ClassifierModel, _, _| {
        let result: ClassifierResult = serde_json::from_value(json!({
            "api": model.api,
            "provider": model.provider,
            "model": model.id,
            "answers": { "approved": { "type": "bool", "probability": 0.9 } },
            "stopReason": "stop",
            "timestamp": now(),
        }))
        .expect("classifier result");
        Box::pin(async move { result })
    });
    let provider = create_provider(CreateProviderOptions {
        id: "test".into(),
        auth: ambient(),
        models: vec![
            AnyModel::Chat(chat.clone()),
            AnyModel::Classifier(classifier.clone()),
        ],
        api: Some(ProviderApi::ByApi(IndexMap::from([(
            "test-chat".to_owned(),
            silent_streams(),
        )]))),
        classifiers: Some(IndexMap::from([(
            "test-classifier".to_owned(),
            ProviderClassifier { classify },
        )])),
        ..CreateProviderOptions::default()
    })
    .expect("provider");
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(provider);

    let listed_chat = models.get_model("test", "shared").expect("chat");
    assert_eq!(
        get_model_type(&AnyModel::Chat(listed_chat)),
        ModelType::Chat
    );
    assert_eq!(
        models
            .get_model_of_type(ModelType::Classifier, "test", "shared")
            .map(|model| model.model_type()),
        Some(ModelType::Classifier)
    );
    assert_eq!(
        models.get_models_of_type(ModelType::Classifier, None),
        [AnyModel::Classifier(classifier.clone())]
    );
    assert_eq!(models.get_all_models(None).len(), 2);
    assert_eq!(
        models
            .get_available_of_type(ModelType::Classifier, None, AuthOperationOptions::default())
            .await
            .expect("available"),
        [AnyModel::Classifier(classifier.clone())]
    );
    let result = models
        .classify(&classifier, &context(), ModelsClassifierOptions::default())
        .await;
    assert_json_eq(
        &result.answers.get("approved"),
        &json!({ "type": "bool", "probability": 0.9 }),
    );
}

fn with_images(images: &serde_json::Value) -> ClassifierContext {
    serde_json::from_value(json!({
        "state": { "text": "yes" },
        "questions": {
            "approved": {
                "type": "bool",
                "instructions": "Does this express approval?",
                "criteria": { "true": "Approval", "false": "No approval" },
            },
        },
        "images": images,
    }))
    .expect("classifier context")
}

#[tokio::test]
async fn rejects_images_for_classifier_models_without_image_input_before_calling_the_provider() {
    let classifier = classifier_model("test", "text-only");
    let calls = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&calls);
    let classify: eukhe_pi_ai::api::ClassifyFn = Arc::new(move |model: &ClassifierModel, _, _| {
        counter.fetch_add(1, Ordering::SeqCst);
        let result: ClassifierResult = serde_json::from_value(json!({
            "api": model.api,
            "provider": model.provider,
            "model": model.id,
            "answers": {},
            "stopReason": "stop",
            "timestamp": now(),
        }))
        .expect("classifier result");
        Box::pin(async move { result })
    });
    let provider = create_provider(CreateProviderOptions {
        id: "test".into(),
        auth: ambient(),
        models: vec![AnyModel::Classifier(classifier.clone())],
        classifiers: Some(IndexMap::from([(
            "test-classifier".to_owned(),
            ProviderClassifier { classify },
        )])),
        ..CreateProviderOptions::default()
    })
    .expect("provider");
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(provider);

    let result = models
        .classify(
            &classifier,
            &with_images(
                &json!([{ "type": "image", "data": "aW1hZ2U=", "mimeType": "image/png" }]),
            ),
            ModelsClassifierOptions::default(),
        )
        .await;
    let without_images = models
        .classify(
            &classifier,
            &with_images(&json!([])),
            ModelsClassifierOptions::default(),
        )
        .await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert_eq!(
        result.error_message.as_deref(),
        Some("Model test/text-only does not accept image input")
    );
    assert_eq!(without_images.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

/// The catalog half of the TS case; the request through a custom `fetch` is
/// in the `openai-decisions` module tests.
#[test]
fn routes_openai_gpt_6_luna_through_the_decisions_api_with_images() {
    let models = builtin_models(CreateModelsOptions::default());
    let luna = models
        .get_model_of_type(ModelType::Classifier, "openai", "gpt-6-luna")
        .expect("missing OpenAI Decisions model");
    assert_match_object(
        &luna,
        &json!({ "api": "openai-decisions", "input": ["text", "image"], "contextWindow": 922_000 }),
    );
    // The chat entry with the same id stays separate.
    assert_eq!(
        models
            .get_model("openai", "gpt-6-luna")
            .map(|model| model.api),
        Some("openai-responses".into())
    );
}

#[tokio::test]
async fn lists_openai_decisions_models_only_for_api_key_credentials() {
    let api_key_store = Arc::new(InMemoryCredentialStore::new());
    store(api_key_store.as_ref(), "openai", api_key("secret")).await;
    let oauth_store = Arc::new(InMemoryCredentialStore::new());
    store(
        oauth_store.as_ref(),
        "openai",
        oauth("access", "refresh", now_f64() + 3_600_000.0),
    )
    .await;

    let with_api_key = builtin_models(CreateModelsOptions {
        credentials: Some(api_key_store),
        ..CreateModelsOptions::default()
    });
    let with_oauth = builtin_models(CreateModelsOptions {
        credentials: Some(oauth_store),
        ..CreateModelsOptions::default()
    });

    let api_key_ids: Vec<String> = with_api_key
        .get_available_of_type(
            ModelType::Classifier,
            Some("openai"),
            AuthOperationOptions::default(),
        )
        .await
        .expect("available")
        .iter()
        .map(|model| model.id().to_owned())
        .collect();
    assert_eq!(api_key_ids, ["gpt-6-luna"]);
    assert_eq!(
        with_oauth
            .get_available_of_type(
                ModelType::Classifier,
                Some("openai"),
                AuthOperationOptions::default(),
            )
            .await
            .expect("available"),
        []
    );
    // Chat models stay available with ChatGPT OAuth.
    assert!(with_oauth
        .get_available(Some("openai"), AuthOperationOptions::default())
        .await
        .expect("available")
        .iter()
        .any(|model| model.id == "gpt-6-luna"));
}

/// Closest Rust equivalent: `Models::classify` narrows with
/// `assert_classifier_model`, which rejects chat models.
#[test]
fn rejects_chat_models_at_the_classifier_entry_point_at_runtime() {
    let chat = AnyModel::Chat(chat_model("test", "chat"));
    let error = assert_classifier_model(&chat).expect_err("chat model rejected");
    assert!(error.message.contains("is not a classifier model"));
}

#[test]
fn exposes_jev_only_through_classifier_catalog_accessors() {
    let jev = get_builtin_classifier_model("typesafe", "jev-latest").expect("jev");
    assert_match_object(
        &jev,
        &json!({
            "type": "classifier",
            "api": "typesafe-system-one",
            "provider": "typesafe",
            "contextWindow": 64000,
        }),
    );
    assert_eq!(
        get_builtin_classifier_models("typesafe"),
        std::slice::from_ref(&jev)
    );
    assert_eq!(
        get_all_builtin_models("typesafe"),
        [AnyModel::Classifier(jev.clone())]
    );

    let models = builtin_models(CreateModelsOptions::default());
    assert_eq!(models.get_model("typesafe", "jev-latest"), None);
    assert_eq!(
        models.get_model_of_type(ModelType::Classifier, "typesafe", "jev-latest"),
        Some(AnyModel::Classifier(jev))
    );
}

/// The catalog half of the TS case; its request/answer assertions through
/// a custom `fetch` are deferred to the `typesafe-system-one` module.
fn routes_jev_to_its_typesafe_compatible_endpoint(provider: &str, id: &str) {
    let models = builtin_models(CreateModelsOptions::default());
    let jev = models
        .get_model_of_type(ModelType::Classifier, provider, id)
        .unwrap_or_else(|| panic!("missing {provider} Jev model"));
    assert_match_object(
        &jev,
        &json!({ "api": "typesafe-system-one", "contextWindow": 32000 }),
    );
    assert_eq!(models.get_model(provider, id), None);
}

#[test]
fn routes_vercel_ai_gateway_jev_typesafe_ai_jev_to_its_typesafe_compatible_endpoint() {
    routes_jev_to_its_typesafe_compatible_endpoint("vercel-ai-gateway", "typesafe-ai/jev");
}

#[test]
fn routes_opencode_jev_jev_1_13_to_its_typesafe_compatible_endpoint() {
    routes_jev_to_its_typesafe_compatible_endpoint("opencode", "jev-1.13");
}

#[test]
fn routes_opencode_jev_jev_1_13_free_to_its_typesafe_compatible_endpoint() {
    routes_jev_to_its_typesafe_compatible_endpoint("opencode", "jev-1.13-free");
}

#[test]
fn routes_openrouter_classifier_models_through_the_system_one_api() {
    let models = builtin_models(CreateModelsOptions::default());
    for model in get_builtin_classifier_models("openrouter") {
        assert_match_object(
            &model,
            &json!({ "api": "typesafe-system-one", "baseUrl": "https://openrouter.ai/api/v1" }),
        );
        assert_eq!(models.get_model("openrouter", &model.id), None);
        assert_eq!(
            models.get_model_of_type(ModelType::Classifier, "openrouter", &model.id),
            Some(AnyModel::Classifier(model))
        );
    }
}
