//! Request operations of [`Models`]: auth application and dispatch to the
//! owning provider, with the TS error-to-stream semantics.

use std::fmt;
use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    AnyModel, AssistantImages, AssistantMessage, AssistantMessageEvent, ClassifierContext,
    ClassifierModel, ClassifierResult, Context, DeferredHandle, ImageModel, ImagesContext, Model,
    ProviderEnv, ProviderHeaders, StreamFailureKind,
};
use futures::future::BoxFuture;
use futures::StreamExt;

use super::collection::{models_error, Models};
use super::provider::Provider;
use super::{merge_headers, CatalogModel};
use crate::api::lazy::{watched_lazy_stream, StreamWatch};
use crate::auth::{
    refresh_stored_oauth_credential, AuthOperationOptions, AuthResolutionOverrides, Credential,
};
use crate::types::{
    ClassifierOptions, DeferredCancelOptions, DeferredFetchOptions, ImagesOptions,
    ProviderRequestOptions, ProviderStreamOptions, SimpleStreamOptions,
};
use crate::utils::abort::operation_signal;
use crate::utils::diagnostics::Thrown;
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::model_operations::{
    assert_chat_model, assert_classifier_input_supported, assert_classifier_model,
    assert_image_model, classifier_error_result, image_error_result,
};
use crate::utils::models_error::ModelsErrorCode;
use crate::utils::stream_idle::StreamIdle;
use crate::utils::stream_repeat::StreamRepeat;
use crate::utils::transcript::normalize_context;

/// Transforms fully assembled model/auth/request headers before provider
/// dispatch: TS `ModelsRequestTransforms.transformHeaders`.
pub type TransformHeadersFn = Arc<
    dyn Fn(ProviderHeaders) -> BoxFuture<'static, Result<ProviderHeaders, Thrown>> + Send + Sync,
>;

/// Provider request options plus the Models-only request transforms: TS
/// `ProviderRequestOptions & ModelsRequestTransforms`.
#[derive(Clone, Default)]
pub struct ModelsRequestOptions<O> {
    pub options: O,
    /// Runs once, after auth and explicit headers merged; never reaches the
    /// provider.
    pub transform_headers: Option<TransformHeadersFn>,
}

impl<O: fmt::Debug> fmt::Debug for ModelsRequestOptions<O> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ModelsRequestOptions")
            .field("options", &self.options)
            .field("transform_headers", &self.transform_headers.is_some())
            .finish()
    }
}

impl<O> From<O> for ModelsRequestOptions<O> {
    fn from(options: O) -> Self {
        Self {
            options,
            transform_headers: None,
        }
    }
}

/// TS `ModelsApiStreamOptions<TApi>`.
pub type ModelsApiStreamOptions = ModelsRequestOptions<ProviderStreamOptions>;
/// TS `ModelsSimpleStreamOptions`.
pub type ModelsSimpleStreamOptions = ModelsRequestOptions<SimpleStreamOptions>;
/// TS `ModelsDeferredFetchOptions`.
pub type ModelsDeferredFetchOptions = ModelsRequestOptions<DeferredFetchOptions>;
/// TS `ModelsDeferredCancelOptions`.
pub type ModelsDeferredCancelOptions = ModelsRequestOptions<DeferredCancelOptions>;
/// TS `ModelsImagesOptions`.
pub type ModelsImagesOptions = ModelsRequestOptions<ImagesOptions>;
/// TS `ModelsClassifierOptions`.
pub type ModelsClassifierOptions = ModelsRequestOptions<ClassifierOptions>;

/// Access to the shared [`ProviderRequestOptions`] inside each request
/// options type.
pub(crate) trait RequestOptions<M>: Send + 'static {
    fn request(&self) -> &ProviderRequestOptions<M>;
    fn request_mut(&mut self) -> &mut ProviderRequestOptions<M>;
}

impl RequestOptions<Model> for ProviderStreamOptions {
    fn request(&self) -> &ProviderRequestOptions<Model> {
        &self.stream.request
    }
    fn request_mut(&mut self) -> &mut ProviderRequestOptions<Model> {
        &mut self.stream.request
    }
}

impl RequestOptions<Model> for SimpleStreamOptions {
    fn request(&self) -> &ProviderRequestOptions<Model> {
        &self.stream.request
    }
    fn request_mut(&mut self) -> &mut ProviderRequestOptions<Model> {
        &mut self.stream.request
    }
}

impl RequestOptions<Model> for DeferredFetchOptions {
    fn request(&self) -> &ProviderRequestOptions<Model> {
        &self.request
    }
    fn request_mut(&mut self) -> &mut ProviderRequestOptions<Model> {
        &mut self.request
    }
}

impl RequestOptions<Model> for DeferredCancelOptions {
    fn request(&self) -> &ProviderRequestOptions<Model> {
        self
    }
    fn request_mut(&mut self) -> &mut ProviderRequestOptions<Model> {
        self
    }
}

impl RequestOptions<ImageModel> for ImagesOptions {
    fn request(&self) -> &ProviderRequestOptions<ImageModel> {
        &self.request
    }
    fn request_mut(&mut self) -> &mut ProviderRequestOptions<ImageModel> {
        &mut self.request
    }
}

impl RequestOptions<ClassifierModel> for ClassifierOptions {
    fn request(&self) -> &ProviderRequestOptions<ClassifierModel> {
        &self.request
    }
    fn request_mut(&mut self) -> &mut ProviderRequestOptions<ClassifierModel> {
        &mut self.request
    }
}

fn signal_aborted(signal: Option<&AbortSignal>) -> bool {
    signal.is_some_and(AbortSignal::aborted)
}

impl Models {
    fn require_provider<M: CatalogModel>(&self, model: &M) -> Result<Arc<Provider>, Thrown> {
        self.get_provider(model.provider_id()).ok_or_else(|| {
            models_error(
                ModelsErrorCode::Provider,
                format!("Unknown provider: {}", model.provider_id()),
            )
        })
    }

    fn require_chat_provider(&self, model: &Model) -> Result<Arc<Provider>, Thrown> {
        assert_chat_model(&AnyModel::Chat(model.clone()))
            .map_err(|error| Arc::new(error) as Thrown)?;
        self.require_provider(model)
    }

    /// Resolves auth for `model` and merges it into the request: explicit
    /// request options win per field; the Models-only transform runs last.
    pub(super) async fn apply_auth<M: CatalogModel, O: RequestOptions<M>>(
        &self,
        model: &M,
        options: ModelsRequestOptions<O>,
    ) -> Result<(M, O), Thrown> {
        self.require_provider(model)?;
        let ModelsRequestOptions {
            options: mut provider_options,
            transform_headers,
        } = options;
        let request = provider_options.request();
        let resolution = self
            .get_auth_for_model(
                model,
                AuthResolutionOverrides {
                    api_key: request.api_key.clone(),
                    env: request.env.clone(),
                    signal: request.signal.clone(),
                    ..AuthResolutionOverrides::default()
                },
            )
            .await?
            .ok_or_else(|| {
                models_error(
                    ModelsErrorCode::Auth,
                    format!("Provider is not configured: {}", model.provider_id()),
                )
            })?;
        let auth = resolution.auth;

        let api_key = request.api_key.clone().or(auth.api_key);
        let mut headers = merge_headers(auth.headers.as_ref(), request.headers.as_ref());
        if let Some(transform) = transform_headers {
            headers = Some(transform(headers.unwrap_or_default()).await?);
        }
        let env: Option<ProviderEnv> = if resolution.env.is_some() || request.env.is_some() {
            let mut env = resolution.env.unwrap_or_default();
            for (name, value) in request.env.iter().flatten() {
                env.insert(name.clone(), value.clone());
            }
            Some(env)
        } else {
            None
        };
        let mut request_model = model.clone();
        if let Some(base_url) = auth.base_url.filter(|base_url| !base_url.is_empty()) {
            request_model.set_base_url(base_url);
        }
        let request = provider_options.request_mut();
        request.api_key = api_key;
        request.headers = headers;
        request.env = env;
        Ok((request_model, provider_options))
    }

    /// Issue a chat request with resolved auth. When the request rode the
    /// stored OAuth credential and the provider rejects it as
    /// unauthenticated before any content, that credential is refreshed
    /// once and the request re-issued: a provider can retire a token its
    /// local expiry still calls valid (revocation, a peer client's
    /// rotation, clock skew), and only that expiry ever triggers a refresh
    /// otherwise, so every later request would fail the same way.
    async fn issue_with_reauth<O: RequestOptions<Model> + Clone>(
        &self,
        request: &Model,
        options: ModelsRequestOptions<O>,
        issue: impl Fn(&Model, O) -> AssistantMessageEventStream,
    ) -> Result<AssistantMessageEventStream, Thrown> {
        let explicit_key = options.options.request().api_key.is_some();
        let signal = operation_signal(options.options.request().signal.clone());
        let (request_model, request_options) = self.apply_auth(request, options.clone()).await?;
        let oauth = self
            .get_provider(&request.provider)
            .and_then(|provider| provider.auth.oauth.clone())
            .filter(|_| !explicit_key);
        let used = match &oauth {
            Some(_) => match self
                .inner
                .credentials
                .read(&request.provider, AuthOperationOptions::default())
                .await
            {
                Ok(Some(Credential::OAuth(used))) => Some(used),
                Ok(Some(Credential::ApiKey(_)) | None) | Err(_) => None,
            },
            None => None,
        };
        let first = issue(&request_model, request_options);
        let (Some(oauth), Some(used)) = (oauth, used) else {
            return Ok(first);
        };
        // Hold the first events until the attempt shows content or ends:
        // only an error before any content is retried.
        let mut events = first.events();
        let mut held = Vec::new();
        let rejected = loop {
            let Some(event) = events.next().await else {
                break false;
            };
            let decided = match &event {
                AssistantMessageEvent::Start { .. } => None,
                // The provider classified the failure as unauthenticated
                // (its newest `provider_stream_failure` diagnostic).
                AssistantMessageEvent::Error { error, .. } => Some(
                    error
                        .diagnostics
                        .as_deref()
                        .unwrap_or_default()
                        .iter()
                        .rev()
                        .find(|diagnostic| diagnostic.kind == "provider_stream_failure")
                        .and_then(|diagnostic| diagnostic.details.as_ref()?.get("kind")?.as_str())
                        == Some(StreamFailureKind::Auth.as_str()),
                ),
                AssistantMessageEvent::TextStart { .. }
                | AssistantMessageEvent::TextDelta { .. }
                | AssistantMessageEvent::TextEnd { .. }
                | AssistantMessageEvent::ThinkingStart { .. }
                | AssistantMessageEvent::ThinkingDelta { .. }
                | AssistantMessageEvent::ThinkingEnd { .. }
                | AssistantMessageEvent::ToolCallStart { .. }
                | AssistantMessageEvent::ToolCallDelta { .. }
                | AssistantMessageEvent::ToolCallEnd { .. }
                | AssistantMessageEvent::Done { .. } => Some(false),
            };
            held.push(event);
            if let Some(rejected) = decided {
                break rejected;
            }
        };
        if rejected {
            let rejected_access = used.access.clone();
            let refreshed = refresh_stored_oauth_credential(
                self.inner.credentials.as_ref(),
                &request.provider,
                &oauth,
                move |current| current.access == rejected_access,
                &signal,
            )
            .await;
            if matches!(&refreshed, Ok(Some(fresh)) if fresh.access != used.access) {
                let (request_model, request_options) = self.apply_auth(request, options).await?;
                return Ok(issue(&request_model, request_options));
            }
        }
        let relay = AssistantMessageEventStream::new();
        for event in held {
            relay.push(event);
        }
        let tail = relay.clone();
        tokio::spawn(async move {
            while let Some(event) = events.next().await {
                tail.push(event);
            }
            tail.end(Some(first.result().await));
        });
        Ok(relay)
    }

    /// Streams a chat request with full (API-specific) options. Setup
    /// failures (unknown provider, missing auth) end the stream with an
    /// error event. The stream runs under the stream-idle deadline
    /// (`stream_idle_timeout_ms`, [`StreamIdle`]) and the repetition guard
    /// (`stream_repeat_limit`, [`StreamRepeat`]).
    #[must_use]
    pub fn stream(
        &self,
        model: &Model,
        context: Context,
        mut options: ModelsApiStreamOptions,
    ) -> AssistantMessageEventStream {
        let transcript = normalize_context(context);
        let this = self.clone();
        let request = model.clone();
        let stream = &mut options.options.stream;
        let watch = StreamWatch {
            idle: StreamIdle::arm(
                &mut stream.request,
                Some(&mut stream.on_provider_stream_event),
            ),
            repeat: Some(StreamRepeat::arm(&mut stream.request)),
        };
        watched_lazy_stream(model, watch, async move {
            let provider = this.require_chat_provider(&request)?;
            let issue = provider.stream.clone();
            this.issue_with_reauth(&request, options, move |model, options| {
                issue(model, &transcript, options)
            })
            .await
        })
    }

    /// [`Models::stream`] resolved to the final message.
    pub async fn complete(
        &self,
        model: &Model,
        context: Context,
        options: ModelsApiStreamOptions,
    ) -> AssistantMessage {
        self.stream(model, context, options).into_result().await
    }

    /// Streams a chat request with provider-neutral options, under the
    /// stream-idle deadline and the repetition guard like [`Models::stream`].
    #[must_use]
    pub fn stream_simple(
        &self,
        model: &Model,
        context: Context,
        mut options: ModelsSimpleStreamOptions,
    ) -> AssistantMessageEventStream {
        let transcript = normalize_context(context);
        let this = self.clone();
        let request = model.clone();
        let stream = &mut options.options.stream;
        let watch = StreamWatch {
            idle: StreamIdle::arm(
                &mut stream.request,
                Some(&mut stream.on_provider_stream_event),
            ),
            repeat: Some(StreamRepeat::arm(&mut stream.request)),
        };
        watched_lazy_stream(model, watch, async move {
            let provider = this.require_chat_provider(&request)?;
            let issue = provider.stream_simple.clone();
            this.issue_with_reauth(&request, options, move |model, options| {
                issue(model, &transcript, options)
            })
            .await
        })
    }

    /// [`Models::stream_simple`] resolved to the final message.
    pub async fn complete_simple(
        &self,
        model: &Model,
        context: Context,
        options: ModelsSimpleStreamOptions,
    ) -> AssistantMessage {
        self.stream_simple(model, context, options)
            .into_result()
            .await
    }

    /// Streams the continuation of a deferred response, under the
    /// stream-idle deadline like [`Models::stream`].
    #[must_use]
    pub fn stream_deferred(
        &self,
        model: &Model,
        handle: &DeferredHandle,
        mut options: ModelsDeferredFetchOptions,
    ) -> AssistantMessageEventStream {
        let this = self.clone();
        let request = model.clone();
        let handle = handle.clone();
        let watch = StreamWatch {
            idle: StreamIdle::arm(&mut options.options.request, None),
            repeat: None,
        };
        watched_lazy_stream(model, watch, async move {
            let provider = this.require_chat_provider(&request)?;
            let fetch_deferred = provider.fetch_deferred.clone().ok_or_else(|| {
                models_error(
                    ModelsErrorCode::Provider,
                    format!(
                        "Provider {} does not support deferred responses",
                        request.provider
                    ),
                )
            })?;
            let (request_model, request_options) = this.apply_auth(&request, options).await?;
            Ok(fetch_deferred(&request_model, &handle, request_options))
        })
    }

    /// [`Models::stream_deferred`] resolved to the final message.
    pub async fn fetch_deferred(
        &self,
        model: &Model,
        handle: &DeferredHandle,
        options: ModelsDeferredFetchOptions,
    ) -> AssistantMessage {
        self.stream_deferred(model, handle, options)
            .into_result()
            .await
    }

    /// Best-effort cancellation of a deferred response.
    ///
    /// # Errors
    ///
    /// `ModelsError` "provider" for an unknown provider, a non-chat model, or
    /// a provider without deferred cancellation; "auth" when the provider is
    /// unconfigured; the provider's cancellation failure.
    pub async fn cancel_deferred(
        &self,
        model: &Model,
        handle: &DeferredHandle,
        options: ModelsDeferredCancelOptions,
    ) -> Result<(), Thrown> {
        let provider = self.require_chat_provider(model)?;
        let cancel_deferred = provider.cancel_deferred.clone().ok_or_else(|| {
            models_error(
                ModelsErrorCode::Provider,
                format!(
                    "Provider {} does not support deferred responses",
                    model.provider
                ),
            )
        })?;
        let (request_model, request_options) = self.apply_auth(model, options).await?;
        cancel_deferred(&request_model, handle, request_options).await
    }

    async fn try_generate_images(
        &self,
        model: &ImageModel,
        context: &ImagesContext,
        options: ModelsImagesOptions,
    ) -> Result<AssistantImages, Thrown> {
        assert_image_model(&AnyModel::Image(model.clone()))
            .map_err(|error| Arc::new(error) as Thrown)?;
        let provider = self.require_provider(model)?;
        let generate_images = provider.generate_images.clone().ok_or_else(|| {
            models_error(
                ModelsErrorCode::Provider,
                format!(
                    "Provider {} does not support image generation",
                    model.provider
                ),
            )
        })?;
        let (request_model, request_options) = self.apply_auth(model, options).await?;
        Ok(generate_images(&request_model, context, request_options).await)
    }

    /// Generates images through the owning provider with auth resolved like
    /// [`Models::stream`]. Never fails: unknown providers, unconfigured auth,
    /// and providers without image generation return an error result.
    pub async fn generate_images(
        &self,
        model: &ImageModel,
        context: &ImagesContext,
        options: ModelsImagesOptions,
    ) -> AssistantImages {
        let signal = options.options.request.signal.clone();
        match self.try_generate_images(model, context, options).await {
            Ok(images) => images,
            Err(error) => image_error_result(model, &error, signal_aborted(signal.as_ref())),
        }
    }

    async fn try_classify(
        &self,
        model: &ClassifierModel,
        context: &ClassifierContext,
        options: ModelsClassifierOptions,
    ) -> Result<ClassifierResult, Thrown> {
        assert_classifier_model(&AnyModel::Classifier(model.clone()))
            .map_err(|error| Arc::new(error) as Thrown)?;
        assert_classifier_input_supported(model, context)
            .map_err(|error| Arc::new(error) as Thrown)?;
        let provider = self.require_provider(model)?;
        let classify = provider.classify.clone().ok_or_else(|| {
            models_error(
                ModelsErrorCode::Provider,
                format!(
                    "Provider {} does not support classification",
                    model.provider
                ),
            )
        })?;
        let (request_model, request_options) = self.apply_auth(model, options).await?;
        Ok(classify(&request_model, context, request_options).await)
    }

    /// Classifies structured state through the owning provider. Never fails.
    pub async fn classify(
        &self,
        model: &ClassifierModel,
        context: &ClassifierContext,
        options: ModelsClassifierOptions,
    ) -> ClassifierResult {
        let signal = options.options.request.signal.clone();
        match self.try_classify(model, context, options).await {
            Ok(result) => result,
            Err(error) => classifier_error_result(model, &error, signal_aborted(signal.as_ref())),
        }
    }
}
