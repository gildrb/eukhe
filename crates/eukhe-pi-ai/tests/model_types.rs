//! Port of `test/model-types.test.ts`.

mod common;

use std::sync::Arc;

use common::{ambient_auth, silent_streams};
use eukhe_pi_ai::auth::ProviderAuth;
use eukhe_pi_ai::compat::get_model as get_compat_model;
use eukhe_pi_ai::models::{
    create_models, create_provider, get_model_type, has_api, is_model_type, models_are_equal,
    CreateModelsOptions, CreateProviderOptions, FetchModelsFn, ModelsRefreshOptions, Provider,
    ProviderApi,
};
use eukhe_pi_ai::models_store::{
    InMemoryModelsStore, ModelsStore, ModelsStoreEntry, ModelsStoreOperationOptions,
};
use eukhe_pi_ai::providers::all::get_builtin_model;
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{
    AnyModel, ChatModelType, Context, ImageModel, Message, Model, ModelType, StopReason,
    UserContent, UserMessage,
};
use serde_json::{json, Value};

fn chat_model_json(provider: &str, id: &str) -> Value {
    json!({
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
    })
}

fn image_model_json(provider: &str, id: &str) -> Value {
    json!({
        "type": "image",
        "id": id,
        "name": id,
        "api": "test-images",
        "provider": provider,
        "baseUrl": "https://example.test/v1",
        "input": ["text"],
        "output": ["image"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
    })
}

fn image_model(provider: &str, id: &str) -> ImageModel {
    serde_json::from_value(image_model_json(provider, id)).expect("image model")
}

/// `{ ...value, type }`.
fn with_type(mut value: Value, model_type: &str) -> Value {
    value["type"] = json!(model_type);
    value
}

fn any_ids(models: &[AnyModel]) -> Vec<String> {
    models.iter().map(|model| model.id().to_owned()).collect()
}

#[tokio::test]
async fn work_through_a_handwritten_provider_without_get_all_models() {
    let faux = faux_provider(RegisterFauxProviderOptions {
        provider: Some("handwritten".to_owned()),
        ..RegisterFauxProviderOptions::default()
    });
    let faux_models = faux.models().to_vec();
    let listed = faux_models.clone();
    let handwritten = Provider {
        id: "handwritten".to_owned(),
        name: "Handwritten".to_owned(),
        base_url: None,
        headers: None,
        auth: faux.provider.auth.clone(),
        get_models: Arc::new(move || Ok(listed.clone())),
        get_all_models: None,
        refresh_models: None,
        filter_models: None,
        filter_all_models: None,
        stream: Arc::clone(&faux.provider.stream),
        stream_simple: Arc::clone(&faux.provider.stream_simple),
        fetch_deferred: None,
        cancel_deferred: None,
        generate_images: None,
        classify: None,
    };
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(handwritten);

    let model = models
        .get_model("handwritten", &faux_models[0].id)
        .expect("model");
    assert_eq!(model.model_type, None);
    let any = AnyModel::Chat(model.clone());
    assert_eq!(get_model_type(&any), ModelType::Chat);
    assert!(has_api(&any, &model.api));
    let typed = AnyModel::Chat(Model {
        model_type: Some(ChatModelType::Chat),
        ..model.clone()
    });
    assert!(models_are_equal(Some(&any), Some(&typed)));
    let image = AnyModel::Image(image_model(&model.provider, &model.id));
    assert!(!models_are_equal(Some(&any), Some(&image)));
    let expected: Vec<AnyModel> = faux_models.iter().cloned().map(AnyModel::Chat).collect();
    assert_eq!(
        models.get_models_of_type(ModelType::Chat, Some("handwritten")),
        expected
    );
    assert_eq!(models.get_all_models(Some("handwritten")), expected);
    assert_eq!(
        models.get_models_of_type(ModelType::Image, Some("handwritten")),
        Vec::<AnyModel>::new()
    );

    faux.set_responses(vec![faux_assistant_message(
        "hi",
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let result = models
        .complete(
            &model,
            Context {
                system_prompt: None,
                messages: vec![Message::User(UserMessage {
                    content: UserContent::Text("hi".to_owned()),
                    timestamp: 0,
                })],
                tools: None,
            },
            ProviderStreamOptions::default().into(),
        )
        .await;
    assert_eq!(result.stop_reason, StopReason::Stop);
}

#[test]
fn narrow_mixed_lists_with_is_model_type() {
    let mixed: Vec<AnyModel> = [
        chat_model_json("p", "c"),
        with_type(chat_model_json("p", "typed"), "chat"),
        image_model_json("p", "i"),
    ]
    .into_iter()
    .map(|value| serde_json::from_value(value).expect("model"))
    .collect();
    let of_type = |model_type: ModelType| -> Vec<AnyModel> {
        mixed
            .iter()
            .filter(|model| is_model_type(model, model_type))
            .cloned()
            .collect()
    };
    assert_eq!(any_ids(&of_type(ModelType::Chat)), ["c", "typed"]);
    assert_eq!(any_ids(&of_type(ModelType::Image)), ["i"]);
    assert_eq!(of_type(ModelType::Classifier), Vec::<AnyModel>::new());
}

/// TS compile-time regression check: the getters' return type does not
/// carry literal model ids, so one binding takes either model.
#[test]
fn return_model_shapes_that_can_be_reassigned_within_one_api() {
    let mut model = get_builtin_model("openai", "gpt-4o-mini");
    assert!(model.is_some());
    model = get_builtin_model("openai", "gpt-4o");
    let mut compat = get_compat_model("openai", "gpt-4o-mini");
    assert!(compat.is_some());
    compat = get_compat_model("openai", "gpt-4o");

    assert_eq!(model.expect("model").id, "gpt-4o");
    assert_eq!(compat.expect("compat").id, "gpt-4o");
}

/// Rust deviation: `FetchModelsFn` returns typed `AnyModel`s, so a fetched
/// model of an unknown type is unrepresentable after parsing. The fetch
/// closure parses the provider's JSON with the same known-type filter the
/// TS `withKnownModelTypes` applies (`ModelsStoreEntry` deserialization).
#[tokio::test]
async fn are_dropped_instead_of_failing_the_refresh() {
    let models_store = Arc::new(InMemoryModelsStore::new());
    let stored: ModelsStoreEntry = serde_json::from_value(json!({
        "models": [
            chat_model_json("dyn", "stored-chat"),
            image_model_json("dyn", "stored-image"),
            with_type(chat_model_json("dyn", "future-embedding"), "embedding"),
            with_type(image_model_json("dyn", "future-video"), "video"),
        ],
    }))
    .expect("stored entry");
    models_store
        .write("dyn", stored, ModelsStoreOperationOptions::default())
        .await
        .expect("write");

    let fetched: Arc<std::sync::Mutex<Value>> = Arc::new(std::sync::Mutex::new(json!([])));
    let fetch_source = Arc::clone(&fetched);
    let fetch_models: FetchModelsFn = Arc::new(move |_context| {
        let value = fetch_source
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        Box::pin(async move {
            let entry: ModelsStoreEntry = serde_json::from_value(json!({ "models": value }))
                .map_err(|error| common::error(&error.to_string()))?;
            Ok(entry.models)
        })
    });
    let models = create_models(CreateModelsOptions {
        models_store: Some(Arc::clone(&models_store) as Arc<dyn ModelsStore>),
        ..CreateModelsOptions::default()
    });
    models.set_provider(
        create_provider(CreateProviderOptions {
            id: "dyn".to_owned(),
            auth: ProviderAuth {
                api_key: Some(ambient_auth()),
                oauth: None,
            },
            models: Vec::new(),
            fetch_models: Some(fetch_models),
            api: Some(ProviderApi::Single(silent_streams())),
            ..CreateProviderOptions::default()
        })
        .expect("provider"),
    );

    let restored = models
        .refresh(ModelsRefreshOptions {
            providers: Some(vec!["dyn".to_owned()]),
            allow_network: Some(false),
            ..ModelsRefreshOptions::default()
        })
        .await;
    assert_eq!(restored.errors.len(), 0);
    assert_eq!(
        any_ids(&models.get_all_models(Some("dyn"))),
        ["stored-chat", "stored-image"]
    );

    *fetched
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner) = json!([
        chat_model_json("dyn", "fetched-chat"),
        with_type(image_model_json("dyn", "fetched-video"), "video"),
    ]);
    let refreshed = models
        .refresh(ModelsRefreshOptions {
            providers: Some(vec!["dyn".to_owned()]),
            ..ModelsRefreshOptions::default()
        })
        .await;
    assert_eq!(refreshed.errors.len(), 0);
    assert_eq!(
        any_ids(&models.get_all_models(Some("dyn"))),
        ["fetched-chat"]
    );
    let persisted = models_store
        .read("dyn", ModelsStoreOperationOptions::default())
        .await
        .expect("read")
        .expect("entry");
    assert_eq!(any_ids(&persisted.models), ["fetched-chat"]);
}
