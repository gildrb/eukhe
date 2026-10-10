//! Port of `test/telemetry-options.test.ts`.
//!
//! "is inherited by every request option surface and simple-stream
//! conversion" asserts `buildBaseOptions` of `api/simple-options.ts`; it is
//! ported at `src/api/openai_completions/tests/telemetry_options.rs`.

mod common;

use std::sync::{Arc, Mutex, PoisonError};

use common::ambient_auth;
use eukhe_pi_ai::api::{ProviderImages, ProviderStreams};
use eukhe_pi_ai::auth::ProviderAuth;
use eukhe_pi_ai::images::generate_images;
use eukhe_pi_ai::images_api_registry::{register_images_api_provider, ImagesApiProvider};
use eukhe_pi_ai::models::{create_models, create_provider, CreateProviderOptions, ProviderApi};
use eukhe_pi_ai::types::{
    DeferredCancelOptions, DeferredFetchOptions, ImagesOptions, ProviderImagesOptions,
    ProviderRequestOptions, ProviderStreamOptions, SimpleStreamOptions, SpanAttributes,
    SpanCallback, SpanOptions, SpanStatus, TelemetryContext, TelemetrySpan,
};
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    AnyModel, AssistantImages, AssistantMessage, AssistantMessageEvent, Context, DeferredHandle,
    DoneReason, ImageModel, ImagesContext, IndexMap, Model, StopReason, Usage,
};
use futures::future::BoxFuture;
use serde_json::json;

/// TS `NOOP_TELEMETRY_CONTEXT`: runs span callbacks without recording.
struct NoopTelemetry;

impl TelemetryContext for NoopTelemetry {
    fn start_span(&self, _options: SpanOptions, callback: SpanCallback) -> BoxFuture<'static, ()> {
        let span: Arc<dyn TelemetrySpan> = Arc::new(Self);
        callback(span)
    }
}

impl TelemetrySpan for NoopTelemetry {
    fn add_event(&self, _name: &str, _attributes: Option<SpanAttributes>) {}
    fn set_attributes(&self, _attributes: SpanAttributes) {}
    fn set_status(&self, _status: SpanStatus) {}
}

type Observed = Arc<Mutex<Vec<Option<Arc<dyn TelemetryContext>>>>>;

fn observe(observed: &Observed, telemetry: Option<Arc<dyn TelemetryContext>>) {
    observed
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .push(telemetry);
}

/// Every observed value is the caller's telemetry context (TS `toBe`).
fn assert_all_same(observed: &Observed, telemetry: &Arc<dyn TelemetryContext>, count: usize) {
    let observed = observed.lock().unwrap_or_else(PoisonError::into_inner);
    assert_eq!(observed.len(), count);
    assert!(observed.iter().all(|value| value
        .as_ref()
        .is_some_and(|value| Arc::ptr_eq(value, telemetry))));
}

fn model() -> Model {
    serde_json::from_value(json!({
        "id": "model",
        "name": "Model",
        "api": "telemetry-test",
        "provider": "telemetry-provider",
        "baseUrl": "https://example.test",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1000,
        "maxTokens": 100,
    }))
    .expect("model")
}

fn image_model() -> ImageModel {
    serde_json::from_value(json!({
        "type": "image",
        "id": "image-model",
        "name": "Image Model",
        "api": "telemetry-test-images",
        "provider": "telemetry-image-provider",
        "baseUrl": "https://example.test",
        "input": ["text"],
        "output": ["image"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
    }))
    .expect("image model")
}

fn images_context() -> ImagesContext {
    serde_json::from_value(json!({ "input": [{ "type": "text", "text": "circle" }] }))
        .expect("images context")
}

fn empty_context() -> Context {
    Context {
        system_prompt: None,
        messages: Vec::new(),
        tools: None,
    }
}

fn completed_stream(request_model: &Model) -> AssistantMessageEventStream {
    let stream = AssistantMessageEventStream::new();
    let message = AssistantMessage {
        content: Vec::new(),
        api: request_model.api.clone(),
        provider: request_model.provider.clone(),
        model: request_model.id.clone(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: StopReason::Stop,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: 0,
        duration_ms: None,
    };
    stream.push(AssistantMessageEvent::Done {
        reason: DoneReason::Stop,
        message,
    });
    stream
}

fn images_result(request_model: &ImageModel) -> AssistantImages {
    serde_json::from_value(json!({
        "api": request_model.api,
        "provider": request_model.provider,
        "model": request_model.id,
        "output": [],
        "stopReason": "stop",
        "timestamp": 0,
    }))
    .expect("images result")
}

fn request(telemetry: &Arc<dyn TelemetryContext>) -> ProviderRequestOptions<Model> {
    ProviderRequestOptions {
        telemetry_context: Some(Arc::clone(telemetry)),
        ..ProviderRequestOptions::default()
    }
}

fn stream_options(telemetry: &Arc<dyn TelemetryContext>) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request = request(telemetry);
    options
}

fn simple_options(telemetry: &Arc<dyn TelemetryContext>) -> SimpleStreamOptions {
    let mut options = SimpleStreamOptions::default();
    options.stream.request = request(telemetry);
    options
}

fn fetch_options(telemetry: &Arc<dyn TelemetryContext>) -> DeferredFetchOptions {
    DeferredFetchOptions {
        request: request(telemetry),
        ..DeferredFetchOptions::default()
    }
}

fn cancel_options(telemetry: &Arc<dyn TelemetryContext>) -> DeferredCancelOptions {
    request(telemetry)
}

fn images_options(telemetry: &Arc<dyn TelemetryContext>) -> ImagesOptions {
    ImagesOptions {
        request: ProviderRequestOptions {
            telemetry_context: Some(Arc::clone(telemetry)),
            ..ProviderRequestOptions::default()
        },
        ..ImagesOptions::default()
    }
}

#[tokio::test]
async fn survives_provider_and_models_stream_deferred_dispatch() {
    let telemetry: Arc<dyn TelemetryContext> = Arc::new(NoopTelemetry);
    let observed: Observed = Arc::default();
    let model = model();
    let handle = DeferredHandle {
        provider: model.provider.clone(),
        model_id: model.id.clone(),
        api: model.api.clone(),
        id: "response".to_owned(),
        expires_at: None,
        poll_after_ms: None,
        data: None,
    };
    let (on_stream, on_simple, on_fetch, on_cancel) = (
        Arc::clone(&observed),
        Arc::clone(&observed),
        Arc::clone(&observed),
        Arc::clone(&observed),
    );
    let provider = create_provider(CreateProviderOptions {
        id: model.provider.clone(),
        auth: ProviderAuth {
            api_key: Some(ambient_auth()),
            oauth: None,
        },
        models: vec![AnyModel::Chat(model.clone())],
        api: Some(ProviderApi::Single(ProviderStreams {
            stream: Arc::new(move |request_model, _context, options| {
                observe(&on_stream, options.stream.request.telemetry_context);
                completed_stream(request_model)
            }),
            stream_simple: Arc::new(move |request_model, _context, options| {
                observe(&on_simple, options.stream.request.telemetry_context);
                completed_stream(request_model)
            }),
            fetch_deferred: Some(Arc::new(move |request_model, _handle, options| {
                observe(&on_fetch, options.request.telemetry_context);
                completed_stream(request_model)
            })),
            cancel_deferred: Some(Arc::new(move |_request_model, _handle, options| {
                observe(&on_cancel, options.telemetry_context);
                Box::pin(async { Ok(()) })
            })),
        })),
        ..CreateProviderOptions::default()
    })
    .expect("provider");

    let context = normalize_context(empty_context());
    (provider.stream)(&model, &context, stream_options(&telemetry))
        .result()
        .await;
    (provider.stream_simple)(&model, &context, simple_options(&telemetry))
        .result()
        .await;
    (provider.fetch_deferred.as_ref().expect("fetchDeferred"))(
        &model,
        &handle,
        fetch_options(&telemetry),
    )
    .result()
    .await;
    (provider.cancel_deferred.as_ref().expect("cancelDeferred"))(
        &model,
        &handle,
        cancel_options(&telemetry),
    )
    .await
    .expect("cancel");

    let models = create_models(eukhe_pi_ai::models::CreateModelsOptions::default());
    models.set_provider(provider);
    models
        .stream(&model, empty_context(), stream_options(&telemetry).into())
        .result()
        .await;
    models
        .stream_simple(&model, empty_context(), simple_options(&telemetry).into())
        .result()
        .await;
    models
        .fetch_deferred(&model, &handle, fetch_options(&telemetry).into())
        .await;
    models
        .cancel_deferred(&model, &handle, cancel_options(&telemetry).into())
        .await
        .expect("cancel");

    assert_all_same(&observed, &telemetry, 8);
}

#[tokio::test]
async fn survives_direct_and_models_image_dispatch() {
    let telemetry: Arc<dyn TelemetryContext> = Arc::new(NoopTelemetry);
    let observed: Observed = Arc::default();
    let image_model = image_model();
    let images_context = images_context();
    let on_direct = Arc::clone(&observed);
    register_images_api_provider(
        ImagesApiProvider {
            api: image_model.api.clone(),
            generate_images: Arc::new(move |request_model, _context, options| {
                observe(&on_direct, options.images.request.telemetry_context);
                let result = images_result(request_model);
                Box::pin(async move { Ok(result) })
            }),
        },
        None,
    );
    generate_images(
        &image_model,
        &images_context,
        ProviderImagesOptions {
            images: images_options(&telemetry),
            ..ProviderImagesOptions::default()
        },
    )
    .await
    .expect("generate images");

    let models = create_models(eukhe_pi_ai::models::CreateModelsOptions::default());
    let on_models = Arc::clone(&observed);
    models.set_provider(
        create_provider(CreateProviderOptions {
            id: image_model.provider.clone(),
            auth: ProviderAuth {
                api_key: Some(ambient_auth()),
                oauth: None,
            },
            models: vec![AnyModel::Image(image_model.clone())],
            images: Some(IndexMap::from([(
                image_model.api.clone(),
                ProviderImages {
                    generate_images: Arc::new(move |request_model, _context, options| {
                        observe(&on_models, options.request.telemetry_context);
                        let result = images_result(request_model);
                        Box::pin(async move { result })
                    }),
                },
            )])),
            ..CreateProviderOptions::default()
        })
        .expect("provider"),
    );
    models
        .generate_images(
            &image_model,
            &images_context,
            images_options(&telemetry).into(),
        )
        .await;

    assert_all_same(&observed, &telemetry, 2);
}
