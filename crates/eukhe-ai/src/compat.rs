//! Temporary compatibility entry point preserving the old global pi-ai API
//! surface: api-dispatch `stream()`/`complete()` with env API key injection,
//! the api registry, generated catalog reads (`get_model`/`get_models`/
//! `get_providers`), per-API lazy stream wrappers, and image generation.
//! Port of `compat.ts`. New code uses `create_models()` and the provider
//! factories.

pub mod extension_oauth_types;

use std::sync::{Arc, LazyLock, Mutex, MutexGuard, Once, PoisonError};

use eukhe_types::pi_ai::{AssistantMessage, Context, IndexMap, Model, TranscriptContext};

pub use crate::api::builtin::{
    anthropic_messages_api, azure_openai_responses_api, bedrock_converse_stream_api,
    google_generative_ai_api, google_vertex_api, mistral_conversations_api,
    openai_codex_responses_api, openai_completions_api, openai_responses_api, pi_messages_api,
    set_bedrock_provider_module,
};
use crate::api::{ProviderStreams, StreamFn, StreamSimpleFn};
pub use crate::env_api_keys::*;
pub use crate::image_models::*;
pub use crate::images::*;
pub use crate::images_api_registry::*;
pub use crate::legacy_api_aliases::*;
use crate::models::{Models, Provider};
use crate::providers::all::builtin_models;
pub use crate::providers::all::{
    get_builtin_model as get_model, get_builtin_models as get_models,
    get_builtin_providers as get_providers,
};
use crate::providers::faux::{
    random_base36, FauxCore, FauxProviderState, FauxResponseStep, RegisterFauxProviderOptions,
};
pub use crate::providers::images::register_builtins::*;
use crate::types::{ProviderStreamOptions, SimpleStreamOptions, StreamOptions};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::transcript::normalize_context;

/// A registered stream function: TS `ApiStreamFunction`. Fails synchronously
/// on a model whose api does not match the registration.
pub type ApiStreamFunction = Arc<
    dyn Fn(
            &Model,
            &TranscriptContext,
            ProviderStreamOptions,
        ) -> Result<AssistantMessageEventStream, Thrown>
        + Send
        + Sync,
>;

/// A registered simple stream function: TS `ApiStreamSimpleFunction`.
pub type ApiStreamSimpleFunction = Arc<
    dyn Fn(
            &Model,
            &TranscriptContext,
            SimpleStreamOptions,
        ) -> Result<AssistantMessageEventStream, Thrown>
        + Send
        + Sync,
>;

/// An API implementation to register: TS `ApiProvider`.
#[derive(Clone)]
pub struct ApiProvider {
    pub api: String,
    pub stream: StreamFn,
    pub stream_simple: StreamSimpleFn,
}

/// A registered API implementation: TS `ApiProviderInternal`.
#[derive(Clone)]
pub struct ApiProviderInternal {
    pub api: String,
    pub stream: ApiStreamFunction,
    pub stream_simple: ApiStreamSimpleFunction,
}

struct RegisteredApiProvider {
    provider: Arc<ApiProviderInternal>,
    source_id: Option<String>,
}

static API_PROVIDER_REGISTRY: LazyLock<Mutex<IndexMap<String, RegisteredApiProvider>>> =
    LazyLock::new(|| Mutex::new(IndexMap::new()));

/// The instance each builtin api id resolved to when builtins registered.
static BUILTIN_API_PROVIDER_INSTANCES: LazyLock<
    Mutex<IndexMap<String, Option<Arc<ApiProviderInternal>>>>,
> = LazyLock::new(|| Mutex::new(IndexMap::new()));

static COMPAT_MODELS: LazyLock<Models> =
    LazyLock::new(|| builtin_models(crate::models::CreateModelsOptions::default()));

static INITIALIZED: Once = Once::new();

const AMBIENT_AUTH_MARKER: &str = "<authenticated>";

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The TS module side effect: registers the builtin APIs once per process.
fn ensure_initialized() {
    INITIALIZED.call_once(register_built_in_api_providers_inner);
}

fn mismatched(model: &Model, api: &str) -> Thrown {
    ErrorObject::new(format!("Mismatched api: {} expected {api}", model.api)).thrown()
}

fn wrap_stream(api: String, stream: StreamFn) -> ApiStreamFunction {
    Arc::new(move |model, context, options| {
        if model.api != api {
            return Err(mismatched(model, &api));
        }
        Ok(stream(model, context, options))
    })
}

fn wrap_stream_simple(api: String, stream_simple: StreamSimpleFn) -> ApiStreamSimpleFunction {
    Arc::new(move |model, context, options| {
        if model.api != api {
            return Err(mismatched(model, &api));
        }
        Ok(stream_simple(model, context, options))
    })
}

fn register_api_provider_inner(provider: ApiProvider, source_id: Option<String>) {
    let ApiProvider {
        api,
        stream,
        stream_simple,
    } = provider;
    let internal = ApiProviderInternal {
        api: api.clone(),
        stream: wrap_stream(api.clone(), stream),
        stream_simple: wrap_stream_simple(api.clone(), stream_simple),
    };
    lock(&API_PROVIDER_REGISTRY).insert(
        api,
        RegisteredApiProvider {
            provider: Arc::new(internal),
            source_id,
        },
    );
}

/// Registers (or replaces) the implementation for `provider.api`.
pub fn register_api_provider(provider: ApiProvider, source_id: Option<String>) {
    ensure_initialized();
    register_api_provider_inner(provider, source_id);
}

fn get_api_provider_arc(api: &str) -> Option<Arc<ApiProviderInternal>> {
    lock(&API_PROVIDER_REGISTRY)
        .get(api)
        .map(|entry| Arc::clone(&entry.provider))
}

/// The registered implementation for `api`.
#[must_use]
pub fn get_api_provider(api: &str) -> Option<ApiProviderInternal> {
    ensure_initialized();
    get_api_provider_arc(api).map(|provider| (*provider).clone())
}

/// Every registered implementation, in registration order.
#[must_use]
pub fn get_api_providers() -> Vec<ApiProviderInternal> {
    ensure_initialized();
    lock(&API_PROVIDER_REGISTRY)
        .values()
        .map(|entry| (*entry.provider).clone())
        .collect()
}

/// Removes every implementation registered with `source_id`.
pub fn unregister_api_providers(source_id: &str) {
    ensure_initialized();
    lock(&API_PROVIDER_REGISTRY).retain(|_, entry| entry.source_id.as_deref() != Some(source_id));
}

/// A faux provider registered in the global api registry: TS
/// `FauxProviderRegistration`.
#[derive(Clone)]
pub struct FauxProviderRegistration {
    core: FauxCore,
    source_id: String,
}

impl FauxProviderRegistration {
    #[must_use]
    pub fn api(&self) -> &str {
        self.core.api()
    }

    #[must_use]
    pub fn models(&self) -> &[Model] {
        self.core.models()
    }

    #[must_use]
    pub fn get_model(&self) -> Model {
        self.core.get_model()
    }

    #[must_use]
    pub fn get_model_by_id(&self, model_id: &str) -> Option<Model> {
        self.core.get_model_by_id(model_id)
    }

    #[must_use]
    pub fn state(&self) -> FauxProviderState {
        self.core.state()
    }

    pub fn set_responses(&self, responses: Vec<FauxResponseStep>) {
        self.core.set_responses(responses);
    }

    pub fn append_responses(&self, responses: Vec<FauxResponseStep>) {
        self.core.append_responses(responses);
    }

    #[must_use]
    pub fn get_pending_response_count(&self) -> usize {
        self.core.get_pending_response_count()
    }

    /// Removes the registration from the global api registry.
    pub fn unregister(&self) {
        unregister_api_providers(&self.source_id);
    }
}

/// Registers a faux provider in the global api registry: TS
/// `registerFauxProvider()`.
#[must_use]
pub fn register_faux_provider(options: RegisterFauxProviderOptions) -> FauxProviderRegistration {
    let core = FauxCore::new(options);
    let source_id = format!(
        "faux-provider-{}",
        random_base36().chars().take(8).collect::<String>()
    );
    let streams = core.streams();
    register_api_provider(
        ApiProvider {
            api: core.api().to_owned(),
            stream: streams.stream,
            stream_simple: streams.stream_simple,
        },
        Some(source_id.clone()),
    );
    FauxProviderRegistration { core, source_id }
}

fn builtin_apis() -> Vec<(&'static str, ProviderStreams)> {
    vec![
        ("anthropic-messages", anthropic_messages_api()),
        ("openai-completions", openai_completions_api()),
        ("openai-responses", openai_responses_api()),
        ("openai-codex-responses", openai_codex_responses_api()),
        ("azure-openai-responses", azure_openai_responses_api()),
        ("google-generative-ai", google_generative_ai_api()),
        ("google-vertex", google_vertex_api()),
        ("mistral-conversations", mistral_conversations_api()),
        ("bedrock-converse-stream", bedrock_converse_stream_api()),
        ("pi-messages", pi_messages_api()),
    ]
}

fn register_built_in_api_providers_inner() {
    for (api, streams) in builtin_apis() {
        if get_api_provider_arc(api).is_none() {
            register_api_provider_inner(
                ApiProvider {
                    api: api.to_owned(),
                    stream: streams.stream,
                    stream_simple: streams.stream_simple,
                },
                None,
            );
        }
        lock(&BUILTIN_API_PROVIDER_INSTANCES).insert(api.to_owned(), get_api_provider_arc(api));
    }
}

/// Registers the builtin API implementations without clobbering existing
/// entries: a test or extension may already have registered an override for
/// a builtin api id.
pub fn register_built_in_api_providers() {
    ensure_initialized();
    register_built_in_api_providers_inner();
}

/// Clears the registry and re-registers the builtins.
pub fn reset_api_providers() {
    ensure_initialized();
    lock(&API_PROVIDER_REGISTRY).clear();
    lock(&BUILTIN_API_PROVIDER_INSTANCES).clear();
    register_built_in_api_providers_inner();
}

fn has_explicit_api_key(api_key: Option<&String>) -> bool {
    api_key.is_some_and(|key| !crate::utils::js::js_trim(key).is_empty())
}

fn with_env_api_key(model: &Model, options: &mut StreamOptions) {
    if has_explicit_api_key(options.request.api_key.as_ref()) {
        return;
    }
    let Some(api_key) = get_env_api_key(&model.provider, options.request.env.as_ref()) else {
        return;
    };
    if api_key.is_empty() || api_key == AMBIENT_AUTH_MARKER {
        return;
    }
    options.request.api_key = Some(api_key);
}

fn has_resolved_cloudflare_auth(options: &StreamOptions) -> bool {
    has_explicit_api_key(options.request.api_key.as_ref())
        || options
            .request
            .headers
            .as_ref()
            .is_some_and(|headers| matches!(headers.get("cf-aig-authorization"), Some(Some(_))))
}

fn get_builtin_provider_for_model(model: &Model) -> Option<Arc<Provider>> {
    let registered = get_api_provider_arc(&model.api);
    let builtin = lock(&BUILTIN_API_PROVIDER_INSTANCES)
        .get(&model.api)
        .cloned()
        .flatten();
    let same = match (&registered, &builtin) {
        (Some(registered), Some(builtin)) => Arc::ptr_eq(registered, builtin),
        (None, None) => true,
        (Some(_), None) | (None, Some(_)) => false,
    };
    if !same {
        return None;
    }
    let provider = COMPAT_MODELS.get_provider(&model.provider)?;
    let models = (provider.get_models)().ok()?;
    models
        .iter()
        .any(|candidate| candidate.api == model.api)
        .then_some(provider)
}

fn resolve_api_provider(api: &str) -> Result<Arc<ApiProviderInternal>, Thrown> {
    get_api_provider_arc(api).ok_or_else(|| {
        ErrorObject::new(format!("No API provider registered for api: {api}")).thrown()
    })
}

fn transcript_as_context(transcript: &TranscriptContext) -> Context {
    Context {
        system_prompt: None,
        messages: transcript.messages().to_vec(),
        tools: None,
    }
}

/// Streams through the builtin provider of `model` (with env API key
/// injection) or the api registry.
///
/// # Errors
///
/// "No API provider registered for api: …" or "Mismatched api: …"; these TS
/// throws happen before a stream exists.
pub fn stream(
    model: &Model,
    context: Context,
    options: ProviderStreamOptions,
) -> Result<AssistantMessageEventStream, Thrown> {
    ensure_initialized();
    let transcript = normalize_context(context);
    let mut options = options;
    if let Some(provider) = get_builtin_provider_for_model(model) {
        if model.provider.starts_with("cloudflare-")
            && !has_resolved_cloudflare_auth(&options.stream)
        {
            return Ok(COMPAT_MODELS.stream(
                model,
                transcript_as_context(&transcript),
                options.into(),
            ));
        }
        with_env_api_key(model, &mut options.stream);
        return Ok((provider.stream)(model, &transcript, options));
    }
    let provider = resolve_api_provider(&model.api)?;
    with_env_api_key(model, &mut options.stream);
    (provider.stream)(model, &transcript, options)
}

/// [`stream`] resolved to the final message.
///
/// # Errors
///
/// Like [`stream`].
pub async fn complete(
    model: &Model,
    context: Context,
    options: ProviderStreamOptions,
) -> Result<AssistantMessage, Thrown> {
    Ok(stream(model, context, options)?.result().await)
}

/// Simple-options counterpart of [`stream`].
///
/// # Errors
///
/// Like [`stream`].
pub fn stream_simple(
    model: &Model,
    context: Context,
    options: SimpleStreamOptions,
) -> Result<AssistantMessageEventStream, Thrown> {
    ensure_initialized();
    let transcript = normalize_context(context);
    let mut options = options;
    if let Some(provider) = get_builtin_provider_for_model(model) {
        if model.provider.starts_with("cloudflare-")
            && !has_resolved_cloudflare_auth(&options.stream)
        {
            return Ok(COMPAT_MODELS.stream_simple(
                model,
                transcript_as_context(&transcript),
                options.into(),
            ));
        }
        with_env_api_key(model, &mut options.stream);
        return Ok((provider.stream_simple)(model, &transcript, options));
    }
    let provider = resolve_api_provider(&model.api)?;
    with_env_api_key(model, &mut options.stream);
    (provider.stream_simple)(model, &transcript, options)
}

/// [`stream_simple`] resolved to the final message.
///
/// # Errors
///
/// Like [`stream`].
pub async fn complete_simple(
    model: &Model,
    context: Context,
    options: SimpleStreamOptions,
) -> Result<AssistantMessage, Thrown> {
    Ok(stream_simple(model, context, options)?.result().await)
}
