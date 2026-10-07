//! Port of `test/images-models.test.ts`.
//!
//! "rejects chat models at the image entry point at runtime" and "rejects
//! image models at the stream entry points at runtime" cast between model
//! types; Rust's `Models::generate_images` takes `&ImageModel` and
//! `Models::stream_simple` takes `&Model`, so the closest Rust-observable
//! equivalents check the runtime narrowing those entry points perform.

mod common;

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use common::{ambient_auth, assert_json_eq, now, silent_streams, FnApiKeyAuth};
use eukhe_chord::context::AbortController;
use eukhe_pi_ai::api::{ProviderImages, ProviderStreams};
use eukhe_pi_ai::auth::{
    AuthContext, AuthOperationOptions, AuthResolutionOverrides, AuthResult, ModelAuth, ProviderAuth,
};
use eukhe_pi_ai::compat::get_models as get_compat_models;
use eukhe_pi_ai::models::{
    create_models, create_provider, get_model_type, has_api, is_model_type, CreateModelsOptions,
    CreateProviderOptions, Models, ModelsImagesOptions, ModelsRefreshOptions, ModelsRequestOptions,
    Provider, ProviderApi,
};
use eukhe_pi_ai::models_store::{InMemoryModelsStore, ModelsStore, ModelsStoreOperationOptions};
use eukhe_pi_ai::providers::all::{
    builtin_models, get_all_builtin_models, get_builtin_classifier_models, get_builtin_image_model,
    get_builtin_image_models, get_builtin_models,
};
use eukhe_pi_ai::types::ImagesOptions;
use eukhe_pi_ai::utils::model_operations::{assert_chat_model, assert_image_model};
use eukhe_types::pi_ai::{
    AnyModel, AssistantImages, ImageModel, ImagesContext, ImagesStopReason, IndexMap, Model,
    ModelType, ProviderEnv, ProviderHeaders,
};
use futures::future::BoxFuture;
use serde_json::json;

struct FakeAuthContext {
    env: HashMap<String, String>,
}

impl AuthContext for FakeAuthContext {
    fn env<'a>(&'a self, name: &'a str) -> BoxFuture<'a, Option<String>> {
        let value = self.env.get(name).cloned();
        Box::pin(async move { value })
    }
    fn file_exists<'a>(&'a self, _path: &'a str) -> BoxFuture<'a, bool> {
        Box::pin(async { false })
    }
}

fn fake_auth_context(env: &[(&str, &str)]) -> Arc<dyn AuthContext> {
    Arc::new(FakeAuthContext {
        env: env
            .iter()
            .map(|(name, value)| ((*name).to_owned(), (*value).to_owned()))
            .collect(),
    })
}

fn models_with_env(env: &[(&str, &str)]) -> Models {
    create_models(CreateModelsOptions {
        auth_context: Some(fake_auth_context(env)),
        ..CreateModelsOptions::default()
    })
}

fn image_model(provider: &str, id: &str) -> ImageModel {
    serde_json::from_value(json!({
        "type": "image",
        "id": id,
        "name": id,
        "api": "test-images",
        "provider": provider,
        "baseUrl": "https://example.test/v1",
        "input": ["text"],
        "output": ["image"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
    }))
    .expect("image model")
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

fn ok_result(model: &ImageModel) -> AssistantImages {
    serde_json::from_value(json!({
        "api": model.api,
        "provider": model.provider,
        "model": model.id,
        "output": [{ "type": "image", "data": "aGk=", "mimeType": "image/png" }],
        "stopReason": "stop",
        "timestamp": now(),
    }))
    .expect("images result")
}

/// One recorded `generateImages` dispatch.
#[derive(Clone)]
struct GenerateCall {
    options: ImagesOptions,
}

type GenerateCalls = Arc<Mutex<Vec<GenerateCall>>>;

fn recorded(calls: &GenerateCalls) -> Vec<GenerateCall> {
    calls.lock().unwrap_or_else(PoisonError::into_inner).clone()
}

fn recording_images(calls: Option<GenerateCalls>) -> ProviderImages {
    ProviderImages {
        generate_images: Arc::new(move |model: &ImageModel, _context, options| {
            if let Some(calls) = &calls {
                calls
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(GenerateCall { options });
            }
            let result = ok_result(model);
            Box::pin(async move { result })
        }),
    }
}

fn ambient() -> ProviderAuth {
    ProviderAuth {
        api_key: Some(ambient_auth()),
        oauth: None,
    }
}

/// Input of [`test_provider`].
#[derive(Default)]
struct TestProvider {
    id: String,
    models: Option<Vec<AnyModel>>,
    env_var: Option<String>,
    calls: Option<GenerateCalls>,
    images: Option<Vec<&'static str>>,
}

/// TS `testProvider()`: chat streams for `test-chat` plus recording image
/// generation for each listed images api.
fn test_provider(input: TestProvider) -> Provider {
    let image_apis = input.images.unwrap_or_else(|| vec!["test-images"]);
    let all_models = input
        .models
        .unwrap_or_else(|| vec![AnyModel::Image(image_model(&input.id, "model-a"))]);
    let env_var = input.env_var;
    let auth = FnApiKeyAuth::new("Test key", move |resolve_input| {
        let env_var = env_var.clone();
        async move {
            let Some(env_var) = env_var else {
                return Ok(Some(AuthResult::default()));
            };
            let stored = resolve_input
                .credential
                .as_ref()
                .and_then(|credential| credential.key.clone());
            let key = match stored {
                Some(key) => Some(key),
                None => resolve_input.ctx.env(&env_var).await,
            };
            Ok(key.map(|key| AuthResult {
                auth: ModelAuth {
                    api_key: Some(key),
                    ..ModelAuth::default()
                },
                env: None,
                source: Some(if resolve_input.credential.is_some() {
                    "stored".to_owned()
                } else {
                    env_var
                }),
            }))
        }
    });
    create_provider(CreateProviderOptions {
        id: input.id,
        auth: ProviderAuth {
            api_key: Some(auth.arc()),
            oauth: None,
        },
        models: all_models,
        api: Some(ProviderApi::ByApi(IndexMap::from([(
            "test-chat".to_owned(),
            silent_streams(),
        )]))),
        images: Some(
            image_apis
                .into_iter()
                .map(|api| (api.to_owned(), recording_images(input.calls.clone())))
                .collect(),
        ),
        ..CreateProviderOptions::default()
    })
    .expect("provider")
}

fn images_context() -> ImagesContext {
    serde_json::from_value(json!({ "input": [{ "type": "text", "text": "a red circle" }] }))
        .expect("images context")
}

fn ids(models: &[AnyModel]) -> Vec<String> {
    models.iter().map(|model| model.id().to_owned()).collect()
}

fn chat_ids(models: &[Model]) -> Vec<String> {
    models.iter().map(|model| model.id.clone()).collect()
}

fn image_of(models: &Models, provider: &str, id: &str) -> ImageModel {
    match models.get_model_of_type(ModelType::Image, provider, id) {
        Some(AnyModel::Image(image)) => image,
        other => panic!("expected image model {provider}/{id}, got {other:?}"),
    }
}

fn with_api_key(api_key: &str) -> ModelsImagesOptions {
    let mut options = ModelsImagesOptions::default();
    options.options.request.api_key = Some(api_key.to_owned());
    options
}

// --- model discriminants ---

#[test]
fn treats_models_without_a_type_as_chat_models() {
    let chat = chat_model("p", "c");
    let image = image_model("p", "i");

    assert_eq!(chat.model_type, None);
    assert_eq!(
        get_model_type(&AnyModel::Chat(chat.clone())),
        ModelType::Chat
    );
    let mut typed_chat = serde_json::to_value(&chat).expect("serialize");
    typed_chat["type"] = json!("chat");
    let typed_chat: Model = serde_json::from_value(typed_chat).expect("typed chat");
    assert_eq!(get_model_type(&AnyModel::Chat(typed_chat)), ModelType::Chat);
    assert_eq!(
        get_model_type(&AnyModel::Image(image.clone())),
        ModelType::Image
    );
    assert!(is_model_type(
        &AnyModel::Chat(chat.clone()),
        ModelType::Chat
    ));
    assert!(!is_model_type(
        &AnyModel::Chat(chat.clone()),
        ModelType::Image
    ));
    assert!(is_model_type(
        &AnyModel::Image(image.clone()),
        ModelType::Image
    ));

    // hasApi never matches an image model, even on an equal api string
    let mut chat_api_image = image;
    chat_api_image.api = "test-chat".into();
    assert!(!has_api(&AnyModel::Image(chat_api_image), "test-chat"));
    assert!(has_api(&AnyModel::Chat(chat), "test-chat"));
}

// --- Models with image models ---

#[tokio::test]
async fn lists_models_without_a_type_as_chat_models_at_create_provider_boundaries() {
    let provider = create_provider(CreateProviderOptions {
        id: "legacy".into(),
        auth: ambient(),
        models: vec![
            AnyModel::Chat(chat_model("legacy", "static")),
            AnyModel::Image(image_model("legacy", "static")),
        ],
        fetch_models: Some(Arc::new(|_context| {
            Box::pin(async { Ok(vec![AnyModel::Chat(chat_model("legacy", "dynamic"))]) })
        })),
        api: Some(ProviderApi::Single(silent_streams())),
        ..CreateProviderOptions::default()
    })
    .expect("provider");
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(provider);
    let provider = models.get_provider("legacy").expect("provider");

    assert_eq!(
        chat_ids(&(provider.get_models)().expect("models")),
        ["static"]
    );
    models
        .refresh(ModelsRefreshOptions {
            providers: Some(vec![provider.id.clone()]),
            ..ModelsRefreshOptions::default()
        })
        .await;
    let listed = (provider.get_models)().expect("models");
    assert_eq!(chat_ids(&listed), ["static", "dynamic"]);
    assert_eq!(
        listed
            .iter()
            .map(|model| model.model_type)
            .collect::<Vec<_>>(),
        [None, None]
    );
    assert_eq!(
        ids(&models.get_models_of_type(ModelType::Image, Some("legacy"))),
        ["static"]
    );
}

#[test]
fn lists_chat_image_and_all_models_through_typed_accessors() {
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        models: Some(vec![
            AnyModel::Chat(chat_model("p1", "c1")),
            AnyModel::Image(image_model("p1", "i1")),
            AnyModel::Image(image_model("p1", "i2")),
        ]),
        ..TestProvider::default()
    }));
    models.set_provider(test_provider(TestProvider {
        id: "p2".into(),
        models: Some(vec![AnyModel::Image(image_model("p2", "i3"))]),
        ..TestProvider::default()
    }));

    assert_eq!(chat_ids(&models.get_models(None)), ["c1"]);
    assert_eq!(
        ids(&models.get_models_of_type(ModelType::Chat, None)),
        ["c1"]
    );
    assert_eq!(
        ids(&models.get_models_of_type(ModelType::Image, None)),
        ["i1", "i2", "i3"]
    );
    assert_eq!(
        ids(&models.get_models_of_type(ModelType::Image, Some("p1"))),
        ["i1", "i2"]
    );
    assert_eq!(models.get_models_of_type(ModelType::Classifier, None), []);
    assert_eq!(ids(&models.get_all_models(None)), ["c1", "i1", "i2", "i3"]);

    assert_eq!(
        models
            .get_model("p1", "c1")
            .map(|model| model.id)
            .as_deref(),
        Some("c1")
    );
    assert_eq!(models.get_model("p1", "i1"), None);
    assert_eq!(
        models
            .get_model_of_type(ModelType::Chat, "p1", "c1")
            .map(|model| model.id().to_owned())
            .as_deref(),
        Some("c1")
    );
    assert_eq!(
        models
            .get_model_of_type(ModelType::Image, "p1", "i1")
            .map(|model| model.id().to_owned())
            .as_deref(),
        Some("i1")
    );
    assert_eq!(models.get_model_of_type(ModelType::Image, "p1", "c1"), None);
}

#[tokio::test]
async fn splits_available_models_by_type() {
    let models = models_with_env(&[("KEY", "k")]);
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        env_var: Some("KEY".into()),
        models: Some(vec![
            AnyModel::Chat(chat_model("p1", "c1")),
            AnyModel::Image(image_model("p1", "i1")),
        ]),
        ..TestProvider::default()
    }));
    models.set_provider(test_provider(TestProvider {
        id: "p2".into(),
        env_var: Some("MISSING".into()),
        models: Some(vec![AnyModel::Image(image_model("p2", "i2"))]),
        ..TestProvider::default()
    }));
    let default = AuthOperationOptions::default;

    assert_eq!(
        chat_ids(
            &models
                .get_available(None, default())
                .await
                .expect("available")
        ),
        ["c1"]
    );
    assert_eq!(
        ids(&models
            .get_available_of_type(ModelType::Chat, None, default())
            .await
            .expect("available")),
        ["c1"]
    );
    assert_eq!(
        ids(&models
            .get_available_of_type(ModelType::Image, None, default())
            .await
            .expect("available")),
        ["i1"]
    );
    assert_eq!(
        ids(&models
            .get_all_available(None, default())
            .await
            .expect("available")),
        ["c1", "i1"]
    );
}

#[tokio::test]
async fn resolves_auth_through_the_provider_and_merges_it_into_image_requests_explicit_options_win()
{
    let calls = GenerateCalls::default();
    let models = models_with_env(&[("TEST_KEY", "env-key")]);
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        env_var: Some("TEST_KEY".into()),
        calls: Some(calls.clone()),
        ..TestProvider::default()
    }));
    let model = image_of(&models, "p1", "model-a");

    let api_key = |result: Option<AuthResult>| result.and_then(|result| result.auth.api_key);
    assert_eq!(
        api_key(
            models
                .get_auth_for_model(&model, AuthResolutionOverrides::default())
                .await
                .expect("auth")
        )
        .as_deref(),
        Some("env-key")
    );
    assert_eq!(
        api_key(
            models
                .get_auth(&model.provider, AuthResolutionOverrides::default())
                .await
                .expect("auth")
        )
        .as_deref(),
        Some("env-key")
    );
    assert_eq!(
        api_key(
            models
                .get_auth_for_model(
                    &model,
                    AuthResolutionOverrides {
                        api_key: Some("explicit-key".into()),
                        ..AuthResolutionOverrides::default()
                    }
                )
                .await
                .expect("auth")
        )
        .as_deref(),
        Some("explicit-key")
    );

    let result = models
        .generate_images(&model, &images_context(), ModelsImagesOptions::default())
        .await;
    assert_eq!(result.stop_reason, ImagesStopReason::Stop);
    assert_eq!(
        recorded(&calls)[0].options.request.api_key.as_deref(),
        Some("env-key")
    );

    models
        .generate_images(&model, &images_context(), with_api_key("explicit"))
        .await;
    assert_eq!(
        recorded(&calls)[1].options.request.api_key.as_deref(),
        Some("explicit")
    );
}

#[tokio::test]
async fn merges_provider_resolved_env_and_applies_header_transforms() {
    let calls = GenerateCalls::default();
    let models = create_models(CreateModelsOptions::default());
    let auth = FnApiKeyAuth::new("Test key", |_| async {
        Ok(Some(AuthResult {
            auth: ModelAuth {
                api_key: Some("provider-key".into()),
                headers: Some(ProviderHeaders::from([(
                    "x-base".to_owned(),
                    Some("1".to_owned()),
                )])),
                base_url: None,
            },
            env: Some(ProviderEnv::from([
                ("PROVIDER_ONLY".to_owned(), "provider".to_owned()),
                ("SHARED".to_owned(), "provider".to_owned()),
            ])),
            source: None,
        }))
    });
    models.set_provider(
        create_provider(CreateProviderOptions {
            id: "p1".into(),
            auth: ProviderAuth {
                api_key: Some(auth.arc()),
                oauth: None,
            },
            models: vec![AnyModel::Image(image_model("p1", "model-a"))],
            images: Some(IndexMap::from([(
                "test-images".to_owned(),
                recording_images(Some(calls.clone())),
            )])),
            ..CreateProviderOptions::default()
        })
        .expect("provider"),
    );
    let model = image_of(&models, "p1", "model-a");

    let mut options = ModelsRequestOptions {
        options: ImagesOptions::default(),
        transform_headers: Some(Arc::new(|mut headers: ProviderHeaders| {
            headers.insert("x-extra".to_owned(), Some("2".to_owned()));
            Box::pin(async move { Ok(headers) })
        })),
    };
    options.options.request.api_key = Some("request-key".into());
    options.options.request.env = Some(ProviderEnv::from([
        ("REQUEST_ONLY".to_owned(), "request".to_owned()),
        ("SHARED".to_owned(), "request".to_owned()),
    ]));
    models
        .generate_images(&model, &images_context(), options)
        .await;

    let call = &recorded(&calls)[0];
    assert_eq!(call.options.request.api_key.as_deref(), Some("request-key"));
    assert_json_eq(
        &call.options.request.env,
        &json!({
            "PROVIDER_ONLY": "provider",
            "REQUEST_ONLY": "request",
            "SHARED": "request",
        }),
    );
    assert_json_eq(
        &call.options.request.headers,
        &json!({ "x-base": "1", "x-extra": "2" }),
    );
}

#[tokio::test]
async fn returns_error_results_instead_of_rejecting() {
    let models = models_with_env(&[]);
    let context = images_context();

    let ghost = models
        .generate_images(
            &image_model("ghost", "m"),
            &context,
            ModelsImagesOptions::default(),
        )
        .await;
    assert_eq!(ghost.stop_reason, ImagesStopReason::Error);
    assert!(ghost
        .error_message
        .unwrap_or_default()
        .contains("Unknown provider: ghost"));

    // Unconfigured auth is an error, matching stream().
    let calls = GenerateCalls::default();
    models.set_provider(test_provider(TestProvider {
        id: "p1".into(),
        env_var: Some("MISSING".into()),
        calls: Some(calls.clone()),
        ..TestProvider::default()
    }));
    let model = image_of(&models, "p1", "model-a");
    assert_eq!(
        models
            .get_auth_for_model(&model, AuthResolutionOverrides::default())
            .await
            .expect("auth"),
        None
    );
    let unconfigured = models
        .generate_images(&model, &context, ModelsImagesOptions::default())
        .await;
    assert_eq!(unconfigured.stop_reason, ImagesStopReason::Error);
    assert!(unconfigured
        .error_message
        .unwrap_or_default()
        .contains("not configured"));
    assert!(recorded(&calls).is_empty());

    let controller = AbortController::new();
    controller.abort(None);
    let mut options = ModelsImagesOptions::default();
    options.options.request.signal = Some(controller.signal());
    let cancelled = models.generate_images(&model, &context, options).await;
    assert_eq!(cancelled.stop_reason, ImagesStopReason::Aborted);
    assert!(recorded(&calls).is_empty());

    // A provider without any images implementation rejects image models it lists.
    models.set_provider(
        create_provider(CreateProviderOptions {
            id: "chat-only".into(),
            auth: ambient(),
            models: vec![AnyModel::Image(image_model("chat-only", "i"))],
            api: Some(ProviderApi::Single(silent_streams())),
            ..CreateProviderOptions::default()
        })
        .expect("provider"),
    );
    let unsupported = models
        .generate_images(
            &image_of(&models, "chat-only", "i"),
            &context,
            ModelsImagesOptions::default(),
        )
        .await;
    assert_eq!(unsupported.stop_reason, ImagesStopReason::Error);
    assert!(unsupported
        .error_message
        .unwrap_or_default()
        .contains("does not support image generation"));

    // An images map without the model's api yields a provider error result.
    models.set_provider(test_provider(TestProvider {
        id: "wrong-api".into(),
        models: Some(vec![AnyModel::Image(image_model("wrong-api", "i"))]),
        images: Some(vec!["other-images"]),
        ..TestProvider::default()
    }));
    let missing_api = models
        .generate_images(
            &image_of(&models, "wrong-api", "i"),
            &context,
            ModelsImagesOptions::default(),
        )
        .await;
    assert_eq!(missing_api.stop_reason, ImagesStopReason::Error);
    assert!(missing_api
        .error_message
        .unwrap_or_default()
        .contains("no image generation implementation for \"test-images\""));
}

/// Closest Rust equivalent: `Models::generate_images` narrows with
/// `assert_image_model`, which rejects chat models.
#[test]
fn rejects_chat_models_at_the_image_entry_point_at_runtime() {
    let chat = AnyModel::Chat(chat_model("p1", "chat"));
    let error = assert_image_model(&chat).expect_err("chat model rejected");
    assert!(error.message.contains("is not an image model"));
}

/// Closest Rust equivalent: the stream entry points narrow with
/// `assert_chat_model`, which rejects image models.
#[test]
fn rejects_image_models_at_the_stream_entry_points_at_runtime() {
    let image = AnyModel::Image(image_model("p1", "model-a"));
    let error = assert_chat_model(&image).expect_err("image model rejected");
    assert!(error.message.contains("is not a chat model"));
}

#[test]
fn requires_at_least_one_concrete_operation_implementation() {
    let create_empty_provider = |implementations: CreateProviderOptions| {
        create_provider(CreateProviderOptions {
            id: "empty".into(),
            auth: ambient(),
            models: Vec::new(),
            ..implementations
        })
    };

    let message = "at least one of \"api\", \"images\", or \"classifiers\"";
    let error_of = |options: CreateProviderOptions| match create_empty_provider(options) {
        Ok(_) => panic!("create_provider should fail"),
        Err(error) => error.to_string(),
    };
    assert!(error_of(CreateProviderOptions::default()).contains(message));
    assert!(error_of(CreateProviderOptions {
        api: Some(ProviderApi::ByApi(
            IndexMap::<String, ProviderStreams>::new()
        )),
        ..CreateProviderOptions::default()
    })
    .contains(message));
    assert!(error_of(CreateProviderOptions {
        images: Some(IndexMap::new()),
        ..CreateProviderOptions::default()
    })
    .contains(message));
    assert!(error_of(CreateProviderOptions {
        classifiers: Some(IndexMap::new()),
        ..CreateProviderOptions::default()
    })
    .contains(message));
}

#[tokio::test]
async fn supports_dynamic_providers_listing_image_models_via_refresh() {
    let fetches = Arc::new(AtomicUsize::new(0));
    let models_store = Arc::new(InMemoryModelsStore::new());
    let models = create_models(CreateModelsOptions {
        models_store: Some(models_store.clone()),
        ..CreateModelsOptions::default()
    });
    let counter = Arc::clone(&fetches);
    models.set_provider(
        create_provider(CreateProviderOptions {
            id: "dyn".into(),
            auth: ambient(),
            models: Vec::new(),
            fetch_models: Some(Arc::new(move |_context| {
                counter.fetch_add(1, Ordering::SeqCst);
                Box::pin(async {
                    Ok(vec![
                        AnyModel::Image(image_model("dyn", "listed")),
                        AnyModel::Chat(chat_model("dyn", "chat")),
                    ])
                })
            })),
            images: Some(IndexMap::from([(
                "test-images".to_owned(),
                recording_images(None),
            )])),
            ..CreateProviderOptions::default()
        })
        .expect("provider"),
    );

    assert_eq!(models.get_all_models(Some("dyn")), []);
    let result = models
        .refresh(ModelsRefreshOptions {
            providers: Some(vec!["dyn".into()]),
            ..ModelsRefreshOptions::default()
        })
        .await;
    assert!(result.errors.is_empty());
    assert_eq!(fetches.load(Ordering::SeqCst), 1);
    assert!(models
        .get_model_of_type(ModelType::Image, "dyn", "listed")
        .is_some());
    assert!(models.get_model("dyn", "chat").is_some());
    let stored = models_store
        .read("dyn", ModelsStoreOperationOptions::default())
        .await
        .expect("read")
        .expect("entry");
    assert_eq!(ids(&stored.models), ["listed", "chat"]);
}

#[test]
fn keeps_existing_built_in_and_compat_model_reads_chat_only() {
    let chat = get_builtin_models("openrouter");
    let images = get_builtin_image_models("openrouter");
    let all = get_all_builtin_models("openrouter");
    let compat = get_compat_models("openrouter");

    assert!(chat
        .iter()
        .all(|model| is_model_type(&AnyModel::Chat(model.clone()), ModelType::Chat)));
    assert!(images
        .iter()
        .all(|model| is_model_type(&AnyModel::Image(model.clone()), ModelType::Image)));
    assert!(all
        .iter()
        .any(|model| is_model_type(model, ModelType::Image)));
    assert_eq!(compat, chat);
    assert!(chat.iter().all(|model| model.context_window > 0));
    assert_eq!(
        chat.len() + images.len() + get_builtin_classifier_models("openrouter").len(),
        all.len()
    );
    assert!(get_builtin_image_model("openrouter", "black-forest-labs/flux.2-pro").is_some());
}

#[tokio::test]
async fn builtin_models_exposes_openrouter_image_models_under_the_openrouter_provider() {
    let models = builtin_models(CreateModelsOptions {
        auth_context: Some(fake_auth_context(&[("OPENROUTER_API_KEY", "or-key")])),
        ..CreateModelsOptions::default()
    });
    let provider = models.get_provider("openrouter").expect("openrouter");
    let images = models.get_models_of_type(ModelType::Image, Some("openrouter"));
    assert!(!images.is_empty());
    assert!((provider.get_models)()
        .expect("models")
        .into_iter()
        .all(|model| is_model_type(&AnyModel::Chat(model), ModelType::Chat)));
    let get_all_models = provider.get_all_models.as_ref().expect("getAllModels");
    assert!(get_all_models()
        .expect("all models")
        .iter()
        .any(|model| is_model_type(model, ModelType::Image)));
    assert!(images
        .iter()
        .all(|model| matches!(model, AnyModel::Image(image) if image.api == "openrouter-images")));
    assert!(models
        .get_models_of_type(ModelType::Image, None)
        .iter()
        .all(|model| model.provider() == "openrouter"));

    // One upstream id can expose separate chat and image operations.
    let chat = models
        .get_model("openrouter", "google/gemini-3-pro-image")
        .expect("chat");
    let image =
        models.get_model_of_type(ModelType::Image, "openrouter", "google/gemini-3-pro-image");
    assert_eq!(chat.api, "openai-completions");
    assert_eq!(image.as_ref().map(AnyModel::api), Some("openrouter-images"));

    // One credential covers both.
    let api_key = |result: Option<AuthResult>| result.and_then(|result| result.auth.api_key);
    assert_eq!(
        api_key(
            models
                .get_auth_for_model(&images[0], AuthResolutionOverrides::default())
                .await
                .expect("auth")
        )
        .as_deref(),
        Some("or-key")
    );
    assert_eq!(
        api_key(
            models
                .get_auth_for_model(&chat, AuthResolutionOverrides::default())
                .await
                .expect("auth")
        )
        .as_deref(),
        Some("or-key")
    );
    assert!(provider.generate_images.is_some());
}
