//! Capability operations of [`Models`]: the rulebook names the dialect that
//! serves an operation for the model's provider; auth resolves like a chat
//! request; the dialect module runs the request. A capability the provider
//! lacks fails with [`CapabilityError::Unsupported`], never a fallback.

use eukhe_types::pi_ai::{
    AnyModel, AssistantImages, Context, ImagesContext, ImagesStopReason, Model, ModelType,
    TextContent, UserContentBlock,
};

use super::collection::Models;
use super::requests::{ModelsRequestOptions, RequestOptions};
use crate::api::classifier_shared::error;
use crate::capabilities::{
    anthropic, capabilities_of, deepseek, google, llama_cpp, openai, openrouter, xai, AccountUsage,
    Capabilities, Capability, CapabilityError, CapabilityOptions, Compaction, Dialect,
    EmbedRequest, Embeddings, GeneratedImages, ImageRequest, ListedModel, Support, TokenCount,
    Tokens, Unsupported, WebSearchRequest, WebSearchResult,
};
use crate::types::{ImagesOptions, ProviderRequestOptions};
use crate::utils::transcript::normalize_context;

/// Capability options plus the Models-only request transforms.
pub type ModelsCapabilityOptions = ModelsRequestOptions<CapabilityOptions>;

impl RequestOptions<Model> for CapabilityOptions {
    fn request(&self) -> &ProviderRequestOptions<Model> {
        &self.request
    }
    fn request_mut(&mut self) -> &mut ProviderRequestOptions<Model> {
        &mut self.request
    }
}

fn unsupported(capability: Capability, model: &Model) -> CapabilityError {
    CapabilityError::Unsupported(Unsupported {
        capability,
        provider: model.provider.clone(),
    })
}

impl Models {
    /// What `model`'s provider supports, from the quirks rulebook. Sends
    /// nothing.
    #[must_use]
    pub fn capabilities(&self, model: &Model) -> Capabilities {
        capabilities_of(model)
    }

    /// The capabilities of each distinct API and base URL among the chat
    /// models of `provider`, in catalog order. Empty for an unknown
    /// provider or one without chat models. Sends nothing.
    #[must_use]
    pub fn provider_capabilities(&self, provider: &str) -> Vec<Capabilities> {
        let mut rows: Vec<Capabilities> = Vec::new();
        for model in self.get_models(Some(provider)) {
            let known = rows
                .iter()
                .any(|row| row.api == model.api && row.base_url == model.base_url);
            if !known {
                rows.push(capabilities_of(&model));
            }
        }
        rows
    }

    /// The dialect that serves `capability` for `model`, and the model and
    /// options with the provider's auth applied.
    async fn capability_request(
        &self,
        model: &Model,
        capability: Capability,
        options: ModelsCapabilityOptions,
    ) -> Result<(Dialect, Model, ProviderRequestOptions), CapabilityError> {
        let dialect = match capabilities_of(model).support(capability) {
            Support::Native { dialect, .. } => dialect,
            Support::Unsupported => return Err(unsupported(capability, model)),
        };
        let (request_model, request_options) = self.apply_auth(model, options).await?;
        Ok((dialect, request_model, request_options.request))
    }

    /// Counts the input tokens `context` costs on `model`, with the
    /// provider's own counter.
    ///
    /// # Errors
    ///
    /// [`CapabilityError::Unsupported`] when the provider has no counter;
    /// [`CapabilityError::Request`] for setup and request failures.
    #[tracing::instrument(skip_all, fields(provider = %model.provider, model = %model.id))]
    pub async fn count_tokens(
        &self,
        model: &Model,
        context: Context,
        options: ModelsCapabilityOptions,
    ) -> Result<TokenCount, CapabilityError> {
        let capability = Capability::CountTokens;
        let (dialect, model, options) = self.capability_request(model, capability, options).await?;
        let context = normalize_context(context);
        match dialect {
            Dialect::Anthropic => Ok(anthropic::count_tokens(&model, &context, &options).await?),
            Dialect::OpenAi => Ok(openai::count_tokens(&model, &context, &options).await?),
            Dialect::Google => Ok(google::count_tokens(&model, &context, &options).await?),
            Dialect::LlamaCpp => Ok(llama_cpp::count_tokens(&model, &context, &options).await?),
            Dialect::Xai | Dialect::OpenRouter | Dialect::DeepSeek => {
                Err(unsupported(capability, &model))
            }
        }
    }

    /// The models the provider's API lists now (model discovery).
    ///
    /// # Errors
    ///
    /// As [`Models::count_tokens`].
    #[tracing::instrument(skip_all, fields(provider = %model.provider))]
    pub async fn list_models(
        &self,
        model: &Model,
        options: ModelsCapabilityOptions,
    ) -> Result<Vec<ListedModel>, CapabilityError> {
        let capability = Capability::ListModels;
        let (dialect, model, options) = self.capability_request(model, capability, options).await?;
        match dialect {
            Dialect::Anthropic => Ok(anthropic::list_models(&model, &options).await?),
            Dialect::OpenAi => Ok(openai::list_models(&model, &options).await?),
            Dialect::Google => Ok(google::list_models(&model, &options).await?),
            Dialect::LlamaCpp | Dialect::Xai | Dialect::OpenRouter | Dialect::DeepSeek => {
                Err(unsupported(capability, &model))
            }
        }
    }

    /// Embeds `request.inputs` with the provider's embedding model
    /// `request.model`.
    ///
    /// # Errors
    ///
    /// As [`Models::count_tokens`].
    #[tracing::instrument(skip_all, fields(provider = %model.provider, embedding_model = %request.model))]
    pub async fn embed(
        &self,
        model: &Model,
        request: &EmbedRequest,
        options: ModelsCapabilityOptions,
    ) -> Result<Embeddings, CapabilityError> {
        let capability = Capability::Embed;
        let (dialect, model, options) = self.capability_request(model, capability, options).await?;
        match dialect {
            Dialect::OpenAi => Ok(openai::embed(&model, request, &options).await?),
            Dialect::Google => Ok(google::embed(&model, request, &options).await?),
            Dialect::Anthropic
            | Dialect::LlamaCpp
            | Dialect::Xai
            | Dialect::OpenRouter
            | Dialect::DeepSeek => Err(unsupported(capability, &model)),
        }
    }

    /// Generates images with the provider's image model `request.model`.
    ///
    /// # Errors
    ///
    /// As [`Models::count_tokens`].
    #[tracing::instrument(skip_all, fields(provider = %model.provider, image_model = %request.model))]
    pub async fn generate_image(
        &self,
        model: &Model,
        request: &ImageRequest,
        options: ModelsCapabilityOptions,
    ) -> Result<GeneratedImages, CapabilityError> {
        let capability = Capability::GenerateImage;
        let dialect = match capabilities_of(model).support(capability) {
            Support::Native { dialect, .. } => dialect,
            Support::Unsupported => return Err(unsupported(capability, model)),
        };
        match dialect {
            Dialect::OpenAi => {
                let (model, options) = self.apply_auth(model, options).await?;
                Ok(openai::generate_image(&model, request, &options.request).await?)
            }
            Dialect::OpenRouter => self.generate_catalog_image(model, request, options).await,
            Dialect::Anthropic
            | Dialect::Google
            | Dialect::LlamaCpp
            | Dialect::Xai
            | Dialect::DeepSeek => Err(unsupported(capability, model)),
        }
    }

    /// Image generation through the provider's catalog image model, which
    /// has its own wire API (`openrouter-images`).
    async fn generate_catalog_image(
        &self,
        model: &Model,
        request: &ImageRequest,
        options: ModelsCapabilityOptions,
    ) -> Result<GeneratedImages, CapabilityError> {
        let Some(AnyModel::Image(image_model)) =
            self.get_model_of_type(ModelType::Image, &model.provider, &request.model)
        else {
            return Err(CapabilityError::Request(error(format!(
                "Unknown image model of provider {}: {}",
                model.provider, request.model
            ))));
        };
        let ModelsRequestOptions {
            options: CapabilityOptions {
                request: chat_request,
            },
            transform_headers,
        } = options;
        // The `onPayload`/`onResponse` hooks observe chat-model requests; the
        // image request has its own model type, so they stay out of it.
        let images_options = ModelsRequestOptions {
            options: ImagesOptions {
                request: ProviderRequestOptions {
                    signal: chat_request.signal,
                    telemetry_context: chat_request.telemetry_context,
                    api_key: chat_request.api_key,
                    fetch: chat_request.fetch,
                    env: chat_request.env,
                    on_payload: None,
                    on_response: None,
                    headers: chat_request.headers,
                    timeout_ms: chat_request.timeout_ms,
                    max_retries: chat_request.max_retries,
                    max_retry_delay_ms: chat_request.max_retry_delay_ms,
                    stream_idle_timeout_ms: chat_request.stream_idle_timeout_ms,
                    stream_clock: chat_request.stream_clock,
                    stream_repeat_limit: chat_request.stream_repeat_limit,
                },
                metadata: None,
            },
            transform_headers,
        };
        let context = ImagesContext {
            input: vec![UserContentBlock::Text(TextContent::new(
                request.prompt.clone(),
            ))],
        };
        let mut images = GeneratedImages { images: Vec::new() };
        for _ in 0..request.count.max(1) {
            let output: AssistantImages = self
                .generate_images(&image_model, &context, images_options.clone())
                .await;
            match output.stop_reason {
                ImagesStopReason::Stop => images.images.extend(openrouter::images_of(&output)),
                ImagesStopReason::Error | ImagesStopReason::Aborted => {
                    return Err(CapabilityError::Request(error(
                        output
                            .error_message
                            .unwrap_or_else(|| "image generation failed".to_owned()),
                    )));
                }
            }
        }
        Ok(images)
    }

    /// Token ids of `text` in `model`'s vocabulary.
    ///
    /// # Errors
    ///
    /// As [`Models::count_tokens`].
    #[tracing::instrument(skip_all, fields(provider = %model.provider, model = %model.id))]
    pub async fn tokenize(
        &self,
        model: &Model,
        text: &str,
        options: ModelsCapabilityOptions,
    ) -> Result<Tokens, CapabilityError> {
        let capability = Capability::Tokenize;
        let (dialect, model, options) = self.capability_request(model, capability, options).await?;
        match dialect {
            Dialect::LlamaCpp => Ok(llama_cpp::tokenize(&model, text, &options).await?),
            Dialect::Xai => Ok(xai::tokenize(&model, text, &options).await?),
            Dialect::Anthropic
            | Dialect::OpenAi
            | Dialect::Google
            | Dialect::OpenRouter
            | Dialect::DeepSeek => Err(unsupported(capability, &model)),
        }
    }

    /// The account's usage, credits, or balance on the provider.
    ///
    /// # Errors
    ///
    /// As [`Models::count_tokens`].
    #[tracing::instrument(skip_all, fields(provider = %model.provider))]
    pub async fn usage(
        &self,
        model: &Model,
        options: ModelsCapabilityOptions,
    ) -> Result<AccountUsage, CapabilityError> {
        let capability = Capability::Usage;
        let (dialect, model, options) = self.capability_request(model, capability, options).await?;
        match dialect {
            Dialect::OpenRouter => Ok(openrouter::usage(&model, &options).await?),
            Dialect::DeepSeek => Ok(deepseek::usage(&model, &options).await?),
            Dialect::Anthropic
            | Dialect::OpenAi
            | Dialect::Google
            | Dialect::LlamaCpp
            | Dialect::Xai => Err(unsupported(capability, &model)),
        }
    }

    /// Answers `request.query` with `model` and the provider's own web
    /// search tool.
    ///
    /// # Errors
    ///
    /// As [`Models::count_tokens`].
    #[tracing::instrument(skip_all, fields(provider = %model.provider, model = %model.id))]
    pub async fn web_search(
        &self,
        model: &Model,
        request: &WebSearchRequest,
        options: ModelsCapabilityOptions,
    ) -> Result<WebSearchResult, CapabilityError> {
        let capability = Capability::WebSearch;
        let (dialect, model, options) = self.capability_request(model, capability, options).await?;
        match dialect {
            Dialect::Anthropic => Ok(anthropic::web_search(&model, request, &options).await?),
            Dialect::OpenAi => Ok(openai::web_search(&model, request, &options).await?),
            Dialect::Google => Ok(google::web_search(&model, request, &options).await?),
            Dialect::LlamaCpp | Dialect::Xai | Dialect::OpenRouter | Dialect::DeepSeek => {
                Err(unsupported(capability, &model))
            }
        }
    }

    /// Compacts `context` on the provider: the replacement items to send
    /// as the next request's input.
    ///
    /// # Errors
    ///
    /// As [`Models::count_tokens`].
    #[tracing::instrument(skip_all, fields(provider = %model.provider, model = %model.id))]
    pub async fn compact(
        &self,
        model: &Model,
        context: Context,
        options: ModelsCapabilityOptions,
    ) -> Result<Compaction, CapabilityError> {
        let capability = Capability::Compact;
        let (dialect, model, options) = self.capability_request(model, capability, options).await?;
        let context = normalize_context(context);
        match dialect {
            Dialect::OpenAi => Ok(openai::compact(&model, &context, &options).await?),
            Dialect::Anthropic
            | Dialect::Google
            | Dialect::LlamaCpp
            | Dialect::Xai
            | Dialect::OpenRouter
            | Dialect::DeepSeek => Err(unsupported(capability, &model)),
        }
    }
}

#[cfg(test)]
#[path = "capabilities_tests.rs"]
mod tests;
