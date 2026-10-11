//! Built-in API registry and the lazy API constructors providers bind to.
//! Port of the `src/api/*.lazy.ts` files; the registry tables replace the TS
//! dynamic `import()` of each API module.
//!
//! See the [module-level contract](super) for how an API module registers.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::{ClassifierModel, ImageModel};

use super::lazy::{lazy_api, LazyApiCapabilities, LoadApi};
use super::{ProviderClassifier, ProviderImages, ProviderStreams};
use crate::utils::diagnostics::Thrown;
use crate::utils::model_operations::{classifier_error_result, image_error_result};

/// A registry table: `(api id, module constructor)` entries.
type ApiTable<T> = &'static [(&'static str, fn() -> T)];

/// Built-in chat API modules.
static BUILTIN_STREAM_APIS: ApiTable<ProviderStreams> = &[
    ("anthropic-messages", super::anthropic_messages::streams),
    (
        "azure-openai-responses",
        super::azure_openai_responses::streams,
    ),
    (
        "bedrock-converse-stream",
        super::bedrock_converse_stream::streams,
    ),
    ("google-generative-ai", super::google_generative_ai::streams),
    ("google-vertex", super::google_vertex::streams),
    (
        "mistral-conversations",
        super::mistral_conversations::streams,
    ),
    (
        "openai-codex-responses",
        super::openai_codex_responses::streams,
    ),
    ("openai-completions", super::openai_completions::streams),
    ("openai-responses", super::openai_responses::streams),
    ("pi-messages", super::pi_messages::streams),
];

/// Built-in image API modules.
static BUILTIN_IMAGE_APIS: ApiTable<ProviderImages> =
    &[("openrouter-images", super::openrouter_images::images)];

/// Built-in classifier API modules.
static BUILTIN_CLASSIFIER_APIS: ApiTable<ProviderClassifier> = &[
    (
        "typesafe-system-one",
        super::typesafe_system_one::classifier,
    ),
    (
        "cloudflare-workers-ai-system-one",
        super::cloudflare_workers_ai_system_one::classifier,
    ),
    ("llama-cpp-classify", super::llama_cpp_classify::classifier),
    ("openai-decisions", super::openai_decisions::classifier),
];

/// Loading an API module whose id has no registry entry: the Rust
/// counterpart of a failed TS dynamic import.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("Cannot load API module \"{api}\": no implementation is registered")]
pub struct ApiModuleNotFound {
    pub api: String,
}

fn not_found(api: &str) -> Thrown {
    Arc::new(ApiModuleNotFound {
        api: api.to_owned(),
    })
}

/// Resolves a built-in chat API module by id.
///
/// # Errors
///
/// Returns [`ApiModuleNotFound`] when no module is registered for `api`.
pub fn load_stream_api(api: &str) -> Result<ProviderStreams, Thrown> {
    BUILTIN_STREAM_APIS
        .iter()
        .find(|(id, _)| *id == api)
        .map(|(_, constructor)| constructor())
        .ok_or_else(|| not_found(api))
}

/// Resolves a built-in image API module by id.
///
/// # Errors
///
/// Returns [`ApiModuleNotFound`] when no module is registered for `api`.
pub fn load_image_api(api: &str) -> Result<ProviderImages, Thrown> {
    BUILTIN_IMAGE_APIS
        .iter()
        .find(|(id, _)| *id == api)
        .map(|(_, constructor)| constructor())
        .ok_or_else(|| not_found(api))
}

/// Resolves a built-in classifier API module by id.
///
/// # Errors
///
/// Returns [`ApiModuleNotFound`] when no module is registered for `api`.
pub fn load_classifier_api(api: &str) -> Result<ProviderClassifier, Thrown> {
    BUILTIN_CLASSIFIER_APIS
        .iter()
        .find(|(id, _)| *id == api)
        .map(|(_, constructor)| constructor())
        .ok_or_else(|| not_found(api))
}

fn builtin_loader(api: &'static str) -> LoadApi {
    Arc::new(move || Box::pin(async move { load_stream_api(api) }))
}

fn lazy_builtin(api: &'static str) -> ProviderStreams {
    lazy_api(builtin_loader(api), LazyApiCapabilities::default())
}

/// TS `anthropicMessagesApi()`.
#[must_use]
pub fn anthropic_messages_api() -> ProviderStreams {
    lazy_builtin("anthropic-messages")
}

/// TS `azureOpenAIResponsesApi()`.
#[must_use]
pub fn azure_openai_responses_api() -> ProviderStreams {
    lazy_builtin("azure-openai-responses")
}

/// Overrides the resolved Bedrock implementation: TS
/// `setBedrockProviderModule()`.
static BEDROCK_MODULE_OVERRIDE: Mutex<Option<ProviderStreams>> = Mutex::new(None);

/// Overrides the Bedrock implementation that [`bedrock_converse_stream_api`]
/// resolves, in place of the registry entry. TS uses it to bundle the
/// Node-only AWS SDK into the Bun binary.
pub fn set_bedrock_provider_module(module: ProviderStreams) {
    *BEDROCK_MODULE_OVERRIDE
        .lock()
        .unwrap_or_else(PoisonError::into_inner) = Some(module);
}

/// TS `bedrockConverseStreamApi()`: the override set by
/// [`set_bedrock_provider_module`], else the registered module.
#[must_use]
pub fn bedrock_converse_stream_api() -> ProviderStreams {
    lazy_api(
        Arc::new(|| {
            Box::pin(async {
                let override_module = BEDROCK_MODULE_OVERRIDE
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .clone();
                match override_module {
                    Some(module) => Ok(module),
                    None => load_stream_api("bedrock-converse-stream"),
                }
            })
        }),
        LazyApiCapabilities::default(),
    )
}

/// TS `googleGenerativeAIApi()`.
#[must_use]
pub fn google_generative_ai_api() -> ProviderStreams {
    lazy_builtin("google-generative-ai")
}

/// TS `googleVertexApi()`.
#[must_use]
pub fn google_vertex_api() -> ProviderStreams {
    lazy_builtin("google-vertex")
}

/// TS `mistralConversationsApi()`.
#[must_use]
pub fn mistral_conversations_api() -> ProviderStreams {
    lazy_builtin("mistral-conversations")
}

/// TS `openAICodexResponsesApi()`.
#[must_use]
pub fn openai_codex_responses_api() -> ProviderStreams {
    lazy_builtin("openai-codex-responses")
}

/// TS `openAICompletionsApi()`.
#[must_use]
pub fn openai_completions_api() -> ProviderStreams {
    lazy_builtin("openai-completions")
}

/// TS `openAIResponsesApi()`.
#[must_use]
pub fn openai_responses_api() -> ProviderStreams {
    lazy_builtin("openai-responses")
}

/// TS `piMessagesApi()`.
#[must_use]
pub fn pi_messages_api() -> ProviderStreams {
    lazy_builtin("pi-messages")
}

fn lazy_classifier(api: &'static str) -> ProviderClassifier {
    ProviderClassifier {
        classify: Arc::new(move |model: &ClassifierModel, context, options| {
            match load_classifier_api(api) {
                Ok(module) => (module.classify)(model, context, options),
                Err(error) => {
                    let result = classifier_error_result(model, &error, false);
                    Box::pin(async move { result })
                }
            }
        }),
    }
}

/// TS `openrouterImagesApi()`.
#[must_use]
pub fn openrouter_images_api() -> ProviderImages {
    ProviderImages {
        generate_images: Arc::new(|model: &ImageModel, context, options| {
            match load_image_api("openrouter-images") {
                Ok(module) => (module.generate_images)(model, context, options),
                Err(error) => {
                    let result = image_error_result(model, &error, false);
                    Box::pin(async move { result })
                }
            }
        }),
    }
}

/// TS `typesafeSystemOneApi()`.
#[must_use]
pub fn typesafe_system_one_api() -> ProviderClassifier {
    lazy_classifier("typesafe-system-one")
}

/// TS `cloudflareWorkersAISystemOneApi()`.
#[must_use]
pub fn cloudflare_workers_ai_system_one_api() -> ProviderClassifier {
    lazy_classifier("cloudflare-workers-ai-system-one")
}

/// TS `llamaCppClassifyApi()`.
#[must_use]
pub fn llama_cpp_classify_api() -> ProviderClassifier {
    lazy_classifier("llama-cpp-classify")
}

/// TS `openAIDecisionsApi()`.
#[must_use]
pub fn openai_decisions_api() -> ProviderClassifier {
    lazy_classifier("openai-decisions")
}
