//! Request operations of [`Models`]: auth application and dispatch to the
//! owning provider, with the TS error-to-stream semantics.

use std::fmt;
use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    AnyModel, AssistantImages, AssistantMessage, ClassifierContext, ClassifierModel,
    ClassifierResult, Context, DeferredHandle, ImageModel, ImagesContext, Model, ProviderEnv,
    ProviderHeaders,
};
use futures::future::BoxFuture;

use super::collection::{models_error, Models};
use super::provider::Provider;
use super::{merge_headers, CatalogModel};
use crate::api::lazy::lazy_stream;
use crate::auth::AuthResolutionOverrides;
use crate::types::{
    ClassifierOptions, DeferredCancelOptions, DeferredFetchOptions, ImagesOptions,
    ProviderRequestOptions, ProviderStreamOptions, SimpleStreamOptions,
};
use crate::utils::diagnostics::Thrown;
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::model_operations::{
    assert_chat_model, assert_classifier_input_supported, assert_classifier_model,
    assert_image_model, classifier_error_result, image_error_result,
};
use crate::utils::models_error::ModelsErrorCode;
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
    async fn apply_auth<M: CatalogModel, O: RequestOptions<M>>(
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

    /// Streams a chat request with full (API-specific) options. Setup
    /// failures (unknown provider, missing auth) end the stream with an
    /// error event.
    #[must_use]
    pub fn stream(
        &self,
        model: &Model,
        context: Context,
        options: ModelsApiStreamOptions,
    ) -> AssistantMessageEventStream {
        let transcript = normalize_context(context);
        let this = self.clone();
        let request = model.clone();
        lazy_stream(model, async move {
            let provider = this.require_chat_provider(&request)?;
            let (request_model, request_options) = this.apply_auth(&request, options).await?;
            Ok((provider.stream)(
                &request_model,
                &transcript,
                request_options,
            ))
        })
    }

    /// [`Models::stream`] resolved to the final message.
    pub async fn complete(
        &self,
        model: &Model,
        context: Context,
        options: ModelsApiStreamOptions,
    ) -> AssistantMessage {
        self.stream(model, context, options).result().await
    }

    /// Streams a chat request with provider-neutral options.
    #[must_use]
    pub fn stream_simple(
        &self,
        model: &Model,
        context: Context,
        options: ModelsSimpleStreamOptions,
    ) -> AssistantMessageEventStream {
        let transcript = normalize_context(context);
        let this = self.clone();
        let request = model.clone();
        lazy_stream(model, async move {
            let provider = this.require_chat_provider(&request)?;
            let (request_model, request_options) = this.apply_auth(&request, options).await?;
            Ok((provider.stream_simple)(
                &request_model,
                &transcript,
                request_options,
            ))
        })
    }

    /// [`Models::stream_simple`] resolved to the final message.
    pub async fn complete_simple(
        &self,
        model: &Model,
        context: Context,
        options: ModelsSimpleStreamOptions,
    ) -> AssistantMessage {
        self.stream_simple(model, context, options).result().await
    }

    /// Streams the continuation of a deferred response.
    #[must_use]
    pub fn stream_deferred(
        &self,
        model: &Model,
        handle: &DeferredHandle,
        options: ModelsDeferredFetchOptions,
    ) -> AssistantMessageEventStream {
        let this = self.clone();
        let request = model.clone();
        let handle = handle.clone();
        lazy_stream(model, async move {
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
        self.stream_deferred(model, handle, options).result().await
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
