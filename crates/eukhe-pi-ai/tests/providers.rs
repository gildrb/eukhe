//! Port of `test/providers.test.ts`.

mod common;

use std::collections::{HashMap, VecDeque};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use common::context;
use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_pi_ai::api::builtin::{load_classifier_api, load_image_api, load_stream_api};
use eukhe_pi_ai::api::lazy::{lazy_api, LazyApiCapabilities};
use eukhe_pi_ai::api::ProviderStreams;
use eukhe_pi_ai::auth::{
    env_api_key_auth, ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthContext, AuthEvent,
    AuthInteraction, AuthPrompt, AuthPromptKind, AuthResolutionOverrides, AuthResult, ModelAuth,
    ProviderAuth, ProviderAuthInteraction,
};
use eukhe_pi_ai::compat::{get_model as get_compat_model, get_models as get_compat_models};
use eukhe_pi_ai::models::{
    create_models, create_provider, get_supported_thinking_levels, CreateModelsOptions,
    CreateProviderOptions, ModelsRefreshOptions, ModelsRequestOptions, Provider, ProviderApi,
};
use eukhe_pi_ai::models_store::{InMemoryModelsStore, ModelsStore, ModelsStoreOperationOptions};
use eukhe_pi_ai::providers::all::{
    builtin_models, builtin_providers, get_all_builtin_models, get_builtin_classifier_model,
    get_builtin_classifier_models, get_builtin_image_model, get_builtin_image_models,
    get_builtin_model, get_builtin_models, get_builtin_providers,
};
use eukhe_pi_ai::providers::amazon_bedrock::amazon_bedrock_provider;
use eukhe_pi_ai::providers::anthropic::anthropic_provider;
use eukhe_pi_ai::providers::cloudflare_ai_gateway::cloudflare_ai_gateway_provider;
use eukhe_pi_ai::providers::cloudflare_workers_ai::cloudflare_workers_ai_provider;
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, FauxDeferredOptions,
    FauxResponseStep, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::providers::google_vertex::google_vertex_provider;
use eukhe_pi_ai::types::{
    DeferredCancelOptions, DeferredFetchOptions, DeferredRequest, DeferredWindow, ProviderEnv,
    SimpleStreamOptions,
};
use eukhe_pi_ai::utils::diagnostics::Thrown;
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    AnyModel, AssistantContentBlock, AssistantMessageEvent, DeferredHandle, DoneReason, IndexMap,
    Modality, Model, ModelImageResizeOptions, ModelThinkingLevel, ProviderHeaders, StopReason,
    TextContent,
};
use futures::future::BoxFuture;
use futures::StreamExt;
use tokio::sync::Notify;

struct FakeAuthContext {
    env: HashMap<String, String>,
    files: Vec<String>,
}

impl AuthContext for FakeAuthContext {
    fn env<'a>(&'a self, name: &'a str) -> BoxFuture<'a, Option<String>> {
        let value = self.env.get(name).cloned();
        Box::pin(async move { value })
    }
    fn file_exists<'a>(&'a self, path: &'a str) -> BoxFuture<'a, bool> {
        let exists = self.files.iter().any(|file| file == path);
        Box::pin(async move { exists })
    }
}

fn fake_auth_context(env: &[(&str, &str)], files: &[&str]) -> Arc<dyn AuthContext> {
    Arc::new(FakeAuthContext {
        env: env
            .iter()
            .map(|(k, v)| ((*k).to_owned(), (*v).to_owned()))
            .collect(),
        files: files.iter().map(|file| (*file).to_owned()).collect(),
    })
}

fn models_with_env(env: &[(&str, &str)], files: &[&str]) -> eukhe_pi_ai::models::Models {
    create_models(CreateModelsOptions {
        auth_context: Some(fake_auth_context(env, files)),
        ..CreateModelsOptions::default()
    })
}

fn never_aborted_signal() -> AbortSignal {
    AbortController::new().signal()
}

/// Answers prompts from a queue and records events.
struct ScriptedInteraction {
    answers: Mutex<VecDeque<String>>,
    events: Mutex<Vec<AuthEvent>>,
    prompts: Mutex<Vec<AuthPromptKind>>,
}

impl ScriptedInteraction {
    fn new(answers: &[&str]) -> Arc<Self> {
        Arc::new(Self {
            answers: Mutex::new(answers.iter().map(|answer| (*answer).to_owned()).collect()),
            events: Mutex::new(Vec::new()),
            prompts: Mutex::new(Vec::new()),
        })
    }
    fn events(&self) -> Vec<AuthEvent> {
        self.events
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

impl AuthInteraction for ScriptedInteraction {
    fn signal(&self) -> Option<AbortSignal> {
        None
    }
    fn prompt(&self, prompt: AuthPrompt) -> BoxFuture<'_, Result<String, Thrown>> {
        self.prompts
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(prompt.kind);
        let answer = self
            .answers
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .pop_front()
            .unwrap_or_default();
        Box::pin(async move { Ok(answer) })
    }
    fn notify(&self, event: AuthEvent) {
        self.events
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(event);
    }
}

async fn login(
    auth: &Arc<dyn ApiKeyAuth>,
    interaction: &Arc<ScriptedInteraction>,
) -> ApiKeyCredential {
    let interaction: Arc<dyn AuthInteraction> = interaction.clone();
    auth.login(ProviderAuthInteraction::new(
        interaction,
        never_aborted_signal(),
    ))
    .expect("login")
    .await
    .expect("login succeeds")
}

fn env_of(entries: &[(&str, &str)]) -> ProviderEnv {
    entries
        .iter()
        .map(|(k, v)| ((*k).to_owned(), (*v).to_owned()))
        .collect()
}

fn info_link_label(event: &AuthEvent) -> Option<String> {
    match event {
        AuthEvent::Info { links, .. } => links.as_ref()?.first()?.label.clone(),
        AuthEvent::AuthUrl { .. } | AuthEvent::DeviceCode { .. } | AuthEvent::Progress { .. } => {
            None
        }
    }
}

fn default_image_resize() -> ModelImageResizeOptions {
    serde_json::from_value(serde_json::json!({
        "maxWidth": 2000, "maxHeight": 2000, "maxBytes": 4_718_592, "jpegQuality": 80,
    }))
    .expect("resize")
}

fn model_json(model: &Model) -> serde_json::Value {
    serde_json::to_value(model).expect("json")
}

#[test]
fn builtin_models_registers_every_builtin_provider_with_models() {
    let models = builtin_models(CreateModelsOptions::default());
    let providers = models.get_providers();
    assert_eq!(providers.len(), builtin_providers().len());
    assert!(providers.iter().any(|provider| provider.id == "anthropic"));

    let anthropic = models.get_model("anthropic", "claude-haiku-4-5");
    assert_eq!(
        anthropic.map(|model| model.api).as_deref(),
        Some("anthropic-messages")
    );

    assert!(models.get_models(None).len() > 500);

    for provider in &providers {
        let list = models.get_all_models(Some(&provider.id));
        assert!(!list.is_empty(), "{}", provider.id);
        assert!(list.iter().all(|model| model.provider() == provider.id));
    }
    let radius = get_builtin_model("radius", "balanced").expect("radius balanced");
    assert_eq!(
        (radius.api.as_str(), radius.provider.as_str()),
        ("pi-messages", "radius")
    );
}

#[test]
fn returns_empty_results_for_unknown_provider_ids() {
    assert!(get_builtin_model("not-a-provider", "x").is_none());
    assert!(get_builtin_image_model("not-a-provider", "x").is_none());
    assert!(get_builtin_classifier_model("not-a-provider", "x").is_none());
    assert!(get_builtin_models("not-a-provider").is_empty());
    assert!(get_builtin_image_models("not-a-provider").is_empty());
    assert!(get_builtin_classifier_models("not-a-provider").is_empty());
    assert!(get_all_builtin_models("not-a-provider").is_empty());
    assert!(get_compat_model("not-a-provider", "x").is_none());
    assert!(get_compat_models("not-a-provider").is_empty());
}

#[test]
fn stores_native_constrained_sampling_capabilities_in_model_metadata() {
    let gpt4o = model_json(&get_builtin_model("openai", "gpt-4o").expect("gpt-4o"));
    assert_eq!(gpt4o["compat"]["supportsStrictMode"], true);
    assert!(gpt4o["compat"].get("supportsOpenAIGrammarTools").is_none());
    let gpt5_4 = model_json(&get_builtin_model("openai", "gpt-5.4").expect("gpt-5.4"));
    assert_eq!(gpt5_4["compat"]["supportsStrictMode"], true);
    assert_eq!(gpt5_4["compat"]["supportsOpenAIGrammarTools"], true);
    let haiku = model_json(&get_builtin_model("anthropic", "claude-haiku-4-5").expect("haiku"));
    assert_eq!(haiku["compat"]["supportsStrictTools"], true);
}

#[test]
fn keeps_the_conservative_resize_profile_on_every_vision_model() {
    let vision_models: Vec<Model> = get_builtin_providers()
        .into_iter()
        .flat_map(get_builtin_models)
        .filter(|model| model.input.contains(&Modality::Image))
        .collect();
    assert!(!vision_models.is_empty());
    for model in vision_models {
        let resize = model
            .input_limits
            .as_ref()
            .and_then(|limits| limits.images.as_ref())
            .and_then(|images| images.resize.clone());
        assert_eq!(
            resize,
            Some(default_image_resize()),
            "{}/{}",
            model.provider,
            model.id
        );
    }
}

#[test]
fn records_known_direct_provider_image_request_limits() {
    let limits = |provider: &str, id: &str| {
        serde_json::to_value(get_builtin_model(provider, id).expect("model").input_limits)
            .expect("json")
    };
    let haiku = limits("anthropic", "claude-haiku-4-5");
    assert_eq!(haiku["maxRequestBytes"], 32 * 1024 * 1024);
    assert_eq!(haiku["images"]["maxPerRequest"], 100);
    assert_eq!(
        limits("anthropic", "claude-opus-5")["images"]["maxPerRequest"],
        600
    );
    assert_eq!(
        limits("amazon-bedrock", "anthropic.claude-haiku-4-5-20251001-v1:0")["images"]
            ["maxPerMessage"],
        20
    );
    let gpt4o = limits("openai", "gpt-4o");
    assert_eq!(gpt4o["maxRequestBytes"], 512 * 1024 * 1024);
    assert_eq!(gpt4o["images"]["maxPerRequest"], 1500);
    let flash = limits("google", "gemini-2.5-flash");
    assert_eq!(flash["maxRequestBytes"], 20 * 1024 * 1024);
    assert_eq!(flash["images"]["maxPerRequest"], 3600);
}

#[test]
fn does_not_infer_image_limits_from_gateway_api_compatibility() {
    let open_router_model = get_builtin_models("openrouter")
        .into_iter()
        .find(|model| model.input.contains(&Modality::Image))
        .expect("vision model");
    assert_eq!(
        serde_json::to_value(open_router_model.input_limits).expect("json"),
        serde_json::json!({ "images": { "resize": serde_json::to_value(default_image_resize()).expect("json") } })
    );
}

fn levels(provider: &str, id: &str) -> Vec<ModelThinkingLevel> {
    get_supported_thinking_levels(&get_builtin_model(provider, id).expect("model"))
}

#[test]
fn uses_models_dev_effort_levels_for_google_thinking_models() {
    // Regression test for https://github.com/earendil-works/pi/issues/9455
    use ModelThinkingLevel::{High, Low, Medium, Minimal};
    for provider in ["google", "google-vertex"] {
        assert!(levels(provider, "gemini-3.6-flash").contains(&Minimal));
        assert_eq!(levels(provider, "gemini-3.8-flash"), [Low, Medium, High]);
        assert_eq!(
            levels(provider, "gemini-3.1-pro-preview"),
            [Low, Medium, High]
        );
    }
    assert_eq!(levels("opencode", "gemini-3.8-flash"), [Low, Medium, High]);
    assert_eq!(levels("google", "gemma-4-31b-it"), [Minimal, High]);
}

fn compat_json(
    models: &eukhe_pi_ai::models::Models,
    provider: &str,
    id: &str,
) -> serde_json::Value {
    let model = models
        .get_model(provider, id)
        .unwrap_or_else(|| panic!("{provider}/{id}"));
    serde_json::to_value(model.compat).expect("json")
}

#[test]
fn enables_mid_conversation_system_messages_only_for_verified_models() {
    let models = builtin_models(CreateModelsOptions::default());
    let supported = [
        ("moonshotai", "kimi-k2.6"),
        ("moonshotai", "kimi-k2.7-code"),
        ("moonshotai", "kimi-k2.7-code-highspeed"),
        ("moonshotai", "kimi-k3"),
        ("moonshotai-cn", "kimi-k2.6"),
        ("moonshotai-cn", "kimi-k2.7-code"),
        ("moonshotai-cn", "kimi-k2.7-code-highspeed"),
        ("moonshotai-cn", "kimi-k3"),
        ("fireworks", "accounts/fireworks/models/kimi-k3"),
        ("fireworks", "accounts/fireworks/routers/kimi-k3-fast"),
        ("openai", "gpt-5.4"),
        ("openai", "gpt-5.5"),
        ("openai", "gpt-6-astra"),
        ("openai-codex", "gpt-5.5"),
        ("anthropic", "claude-opus-5"),
        ("opencode", "gpt-5.4"),
        ("opencode", "gpt-5.6-terra"),
        ("opencode-go", "gpt-5.6-luna"),
        ("opencode", "claude-opus-4-8"),
        ("opencode", "claude-opus-5"),
        ("opencode", "kimi-k3"),
        ("opencode-go", "kimi-k3"),
        ("github-copilot", "gpt-5.6-terra"),
        ("github-copilot", "claude-opus-5"),
        ("github-copilot", "claude-opus-4.8"),
        ("github-copilot", "kimi-k3"),
        ("deepseek", "deepseek-v4-pro"),
        ("openrouter", "openai/gpt-5.6-terra"),
    ];
    let unsupported = [
        (
            "fireworks",
            "accounts/fireworks/models/nemotron-3-ultra-nvfp4",
        ),
        ("openai", "gpt-4.1"),
        ("openai", "gpt-5.2"),
        ("anthropic", "claude-sonnet-4-5"),
        ("google", "gemini-2.5-pro"),
        ("opencode", "gpt-5.2"),
        ("opencode", "claude-sonnet-4-5"),
        ("github-copilot", "claude-sonnet-4.6"),
        ("deepseek", "deepseek-flash"),
        ("openrouter", "anthropic/claude-opus-5"),
        ("openrouter", "moonshotai/kimi-k3"),
        ("openrouter", "openai/gpt-5.6-terra:batch"),
    ];
    for (provider, id) in supported {
        assert_eq!(
            compat_json(&models, provider, id)["supportsMidConvoSystemMessages"],
            true,
            "{provider}/{id}"
        );
    }
    for (provider, id) in unsupported {
        assert!(
            compat_json(&models, provider, id)
                .get("supportsMidConvoSystemMessages")
                .is_none(),
            "{provider}/{id}"
        );
    }
}

#[test]
fn routes_proxied_tool_changes_through_verified_transports_only() {
    let models = builtin_models(CreateModelsOptions::default());
    for (provider, id) in [
        ("opencode", "gpt-5.6-terra"),
        ("github-copilot", "gpt-5.6-terra"),
    ] {
        // Proxies pass `additional_tools` through to OpenAI but are not verified for tool search.
        let compat = compat_json(&models, provider, id);
        assert_eq!(compat["supportsAdditionalTools"], true, "{provider}/{id}");
        assert!(
            compat.get("supportsToolSearch").is_none(),
            "{provider}/{id}"
        );
    }
    // Proxied Anthropic endpoints reject `tool_addition`/`tool_removal` blocks.
    for provider in ["opencode", "github-copilot"] {
        assert!(compat_json(&models, provider, "claude-opus-5")
            .get("supportsMidConvoToolChanges")
            .is_none());
    }
    assert_eq!(
        compat_json(&models, "anthropic", "claude-opus-5")["supportsMidConvoToolChanges"],
        true
    );
    // Kimi-style tool-bearing system messages survive Moonshot and OpenCode but not Copilot.
    for provider in ["moonshotai", "moonshotai-cn", "opencode", "opencode-go"] {
        assert_eq!(
            compat_json(&models, provider, "kimi-k3")["supportsMidConvoToolAdditions"],
            true,
            "{provider}"
        );
    }
    for provider in ["moonshotai", "moonshotai-cn"] {
        for id in ["kimi-k2.6", "kimi-k2.7-code", "kimi-k2.7-code-highspeed"] {
            assert!(compat_json(&models, provider, id)
                .get("supportsMidConvoToolAdditions")
                .is_none());
        }
    }
    assert!(compat_json(&models, "github-copilot", "kimi-k3")
        .get("supportsMidConvoToolAdditions")
        .is_none());
    assert!(compat_json(&models, "openrouter", "openai/gpt-5.6-terra")
        .get("supportsMidConvoToolAdditions")
        .is_none());
}

fn cost_json(models: &eukhe_pi_ai::models::Models, provider: &str, id: &str) -> serde_json::Value {
    serde_json::to_value(models.get_model(provider, id).expect("model").cost).expect("json")
}

#[test]
fn uses_official_kimi_k3_pricing_for_moonshot_providers() {
    let models = builtin_models(CreateModelsOptions::default());
    for provider in ["moonshotai", "moonshotai-cn"] {
        assert_eq!(
            cost_json(&models, provider, "kimi-k3"),
            serde_json::json!({ "input": 3, "output": 15, "cacheRead": 0.3, "cacheWrite": 0 })
        );
    }
}

#[test]
fn uses_api_equivalent_implied_pricing_for_kimi_coding_subscription_models() {
    let models = builtin_models(CreateModelsOptions::default());
    assert_eq!(
        cost_json(&models, "kimi-coding", "k3"),
        serde_json::json!({ "input": 3, "output": 15, "cacheRead": 0.3, "cacheWrite": 0 })
    );
    assert_eq!(
        cost_json(&models, "kimi-coding", "kimi-for-coding-highspeed"),
        serde_json::json!({ "input": 1.9, "output": 8, "cacheRead": 0.38, "cacheWrite": 0 })
    );
}

fn auth_json(result: Option<AuthResult>) -> serde_json::Value {
    serde_json::to_value(result).expect("json")
}

#[tokio::test]
async fn resolves_anthropic_bearer_auth_from_env_with_auth_token_precedence() {
    let models = models_with_env(
        &[
            ("ANTHROPIC_AUTH_TOKEN", "auth-token"),
            ("ANTHROPIC_OAUTH_TOKEN", "oauth-token"),
            ("ANTHROPIC_API_KEY", "api-key"),
        ],
        &[],
    );
    models.set_provider(anthropic_provider());

    assert_eq!(
        auth_json(
            models
                .get_auth("anthropic", AuthResolutionOverrides::default())
                .await
                .expect("auth")
        ),
        serde_json::json!({
            "auth": { "headers": { "Authorization": "Bearer auth-token" } },
            "source": "ANTHROPIC_AUTH_TOKEN",
        })
    );
}

#[tokio::test]
async fn preserves_anthropic_oauth_token_precedence_over_the_api_key() {
    let models = models_with_env(
        &[
            ("ANTHROPIC_API_KEY", "key"),
            ("ANTHROPIC_OAUTH_TOKEN", "oauth-token"),
        ],
        &[],
    );
    models.set_provider(anthropic_provider());

    let result = models
        .get_auth("anthropic", AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(result.auth.api_key.as_deref(), Some("oauth-token"));
    assert_eq!(result.source.as_deref(), Some("ANTHROPIC_OAUTH_TOKEN"));
}

#[tokio::test]
async fn runs_provider_owned_bedrock_bearer_token_and_aws_profile_login_flows() {
    let auth = amazon_bedrock_provider()
        .auth
        .api_key
        .expect("api key auth");
    let bearer = ScriptedInteraction::new(&["bearer-token", "bedrock-token"]);
    assert_eq!(
        login(&auth, &bearer).await,
        ApiKeyCredential::with_key("bedrock-token")
    );

    let profile = ScriptedInteraction::new(&["aws-profile", "work"]);
    assert_eq!(
        login(&auth, &profile).await,
        ApiKeyCredential {
            env: Some(env_of(&[("AWS_PROFILE", "work")])),
            ..ApiKeyCredential::default()
        }
    );
    let events = profile.events();
    assert_eq!(events.len(), 1);
    assert_eq!(
        info_link_label(&events[0]).as_deref(),
        Some("AWS credential provider chain")
    );
    let resolved = auth
        .resolve(ApiKeyResolveInput {
            ctx: fake_auth_context(&[], &[]),
            credential: Some(ApiKeyCredential {
                env: Some(env_of(&[("AWS_PROFILE", "work")])),
                ..ApiKeyCredential::default()
            }),
            signal: never_aborted_signal(),
        })
        .await
        .expect("resolve")
        .expect("configured");
    assert_eq!(resolved.auth, ModelAuth::default());
    assert_eq!(resolved.env, Some(env_of(&[("AWS_PROFILE", "work")])));
}

#[tokio::test]
async fn reports_bedrock_as_configured_from_ambient_aws_credentials_without_an_api_key() {
    let models = models_with_env(&[("AWS_PROFILE", "dev")], &[]);
    models.set_provider(amazon_bedrock_provider());
    let model = models.get_models(Some("amazon-bedrock")).remove(0);

    let result = models
        .get_auth(&model.provider, AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(result.auth, ModelAuth::default());
    assert_eq!(result.source.as_deref(), Some("AWS_PROFILE"));

    let unconfigured = models_with_env(&[], &[]);
    unconfigured.set_provider(amazon_bedrock_provider());
    assert_eq!(
        unconfigured
            .get_auth(&model.provider, AuthResolutionOverrides::default())
            .await
            .expect("auth"),
        None
    );
}

#[tokio::test]
async fn requires_cloudflare_workers_ai_account_config_and_returns_scoped_env() {
    let missing_account = models_with_env(&[("CLOUDFLARE_API_KEY", "cf-key")], &[]);
    missing_account.set_provider(cloudflare_workers_ai_provider());
    let model = missing_account
        .get_models(Some("cloudflare-workers-ai"))
        .remove(0);
    assert_eq!(
        missing_account
            .get_auth(&model.provider, AuthResolutionOverrides::default())
            .await
            .expect("auth"),
        None
    );

    let configured = models_with_env(
        &[
            ("CLOUDFLARE_API_KEY", "cf-key"),
            ("CLOUDFLARE_ACCOUNT_ID", "account-id"),
        ],
        &[],
    );
    configured.set_provider(cloudflare_workers_ai_provider());
    let result = configured
        .get_auth(&model.provider, AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(
        serde_json::to_value(&result.auth).expect("json"),
        serde_json::json!({ "apiKey": "cf-key" })
    );
    assert_eq!(
        result.env,
        Some(env_of(&[("CLOUDFLARE_ACCOUNT_ID", "account-id")]))
    );
}

#[tokio::test]
async fn requires_cloudflare_ai_gateway_account_and_gateway_config_and_returns_scoped_env_headers()
{
    let missing_gateway = models_with_env(
        &[
            ("CLOUDFLARE_API_KEY", "cf-key"),
            ("CLOUDFLARE_ACCOUNT_ID", "account-id"),
        ],
        &[],
    );
    missing_gateway.set_provider(cloudflare_ai_gateway_provider());
    let model = missing_gateway
        .get_models(Some("cloudflare-ai-gateway"))
        .remove(0);
    assert_eq!(
        missing_gateway
            .get_auth(&model.provider, AuthResolutionOverrides::default())
            .await
            .expect("auth"),
        None
    );

    let configured = models_with_env(
        &[
            ("CLOUDFLARE_API_KEY", "cf-key"),
            ("CLOUDFLARE_ACCOUNT_ID", "account-id"),
            ("CLOUDFLARE_GATEWAY_ID", "gateway-id"),
        ],
        &[],
    );
    configured.set_provider(cloudflare_ai_gateway_provider());
    let result = configured
        .get_auth(&model.provider, AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(
        serde_json::to_value(&result.auth).expect("json"),
        serde_json::json!({
            "headers": { "cf-aig-authorization": "Bearer cf-key", "Authorization": null, "x-api-key": null },
        })
    );
    assert_eq!(
        result.env,
        Some(env_of(&[
            ("CLOUDFLARE_ACCOUNT_ID", "account-id"),
            ("CLOUDFLARE_GATEWAY_ID", "gateway-id")
        ]))
    );
}

#[tokio::test]
async fn runs_provider_owned_vertex_api_key_and_adc_login_flows() {
    let auth = google_vertex_provider().auth.api_key.expect("api key auth");
    let key = ScriptedInteraction::new(&["api-key", "vertex-key"]);
    assert_eq!(
        login(&auth, &key).await,
        ApiKeyCredential::with_key("vertex-key")
    );

    let adc = ScriptedInteraction::new(&["adc", "project-id", "us-central1"]);
    let project_env = env_of(&[
        ("GOOGLE_CLOUD_PROJECT", "project-id"),
        ("GOOGLE_CLOUD_LOCATION", "us-central1"),
    ]);
    assert_eq!(
        login(&auth, &adc).await,
        ApiKeyCredential {
            env: Some(project_env.clone()),
            ..ApiKeyCredential::default()
        }
    );
    let events = adc.events();
    assert_eq!(events.len(), 1);
    assert_eq!(
        info_link_label(&events[0]).as_deref(),
        Some("Application Default Credentials")
    );
    let resolved = auth
        .resolve(ApiKeyResolveInput {
            ctx: fake_auth_context(
                &[],
                &["~/.config/gcloud/application_default_credentials.json"],
            ),
            credential: Some(ApiKeyCredential {
                env: Some(project_env.clone()),
                ..ApiKeyCredential::default()
            }),
            signal: never_aborted_signal(),
        })
        .await
        .expect("resolve")
        .expect("configured");
    assert_eq!(resolved.auth, ModelAuth::default());
    assert_eq!(resolved.env, Some(project_env));
}

#[tokio::test]
async fn resolves_vertex_via_adc_file_plus_project_and_location() {
    let adc = "~/.config/gcloud/application_default_credentials.json";
    let configured = models_with_env(
        &[
            ("GOOGLE_CLOUD_PROJECT", "proj"),
            ("GOOGLE_CLOUD_LOCATION", "us-central1"),
        ],
        &[adc],
    );
    configured.set_provider(google_vertex_provider());
    let model = configured.get_models(Some("google-vertex")).remove(0);

    let result = configured
        .get_auth(&model.provider, AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(result.auth, ModelAuth::default());
    assert!(result
        .source
        .expect("source")
        .contains("application default"));

    // ADC without project/location is not configured
    let partial = models_with_env(&[("GOOGLE_CLOUD_PROJECT", "proj")], &[adc]);
    partial.set_provider(google_vertex_provider());
    assert_eq!(
        partial
            .get_auth(&model.provider, AuthResolutionOverrides::default())
            .await
            .expect("auth"),
        None
    );

    // explicit key wins over ADC
    let keyed = models_with_env(&[("GOOGLE_CLOUD_API_KEY", "vertex-key")], &[]);
    keyed.set_provider(google_vertex_provider());
    let result = keyed
        .get_auth(&model.provider, AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(result.auth.api_key.as_deref(), Some("vertex-key"));
}

#[tokio::test]
async fn prefers_the_stored_credential_key_and_falls_back_through_env_vars_in_order() {
    let auth = env_api_key_auth("Test key", &["FIRST_KEY", "SECOND_KEY"]);
    let resolve = |ctx: Arc<dyn AuthContext>, credential: Option<ApiKeyCredential>| {
        auth.resolve(ApiKeyResolveInput {
            ctx,
            credential,
            signal: never_aborted_signal(),
        })
    };

    let stored = resolve(
        fake_auth_context(&[("FIRST_KEY", "env")], &[]),
        Some(ApiKeyCredential::with_key("stored")),
    )
    .await
    .expect("resolve")
    .expect("configured");
    assert_eq!(stored.auth.api_key.as_deref(), Some("stored"));
    assert_eq!(stored.source.as_deref(), Some("stored credential"));

    let second = resolve(fake_auth_context(&[("SECOND_KEY", "second")], &[]), None)
        .await
        .expect("resolve")
        .expect("configured");
    assert_eq!(second.auth.api_key.as_deref(), Some("second"));
    assert_eq!(second.source.as_deref(), Some("SECOND_KEY"));

    assert_eq!(
        resolve(fake_auth_context(&[], &[]), None)
            .await
            .expect("resolve"),
        None
    );
}

#[tokio::test]
async fn login_prompts_for_a_secret_and_returns_an_api_key_credential() {
    let auth = env_api_key_auth("Test key", &["TEST_KEY"]);
    let interaction = ScriptedInteraction::new(&["entered-key"]);
    assert_eq!(
        login(&auth, &interaction).await,
        ApiKeyCredential::with_key("entered-key")
    );
    let prompts = interaction
        .prompts
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert!(matches!(prompts[0], AuthPromptKind::Secret { .. }));
}

fn recording_streams(label: &'static str, calls: Arc<Mutex<Vec<String>>>) -> ProviderStreams {
    let respond = move |model: &Model| {
        calls
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(format!("{label}:{}", model.id));
        let stream = AssistantMessageEventStream::new();
        let message = faux_assistant_message("ok", FauxAssistantMessageOptions::default());
        stream.push(AssistantMessageEvent::Start {
            partial: message.clone(),
        });
        stream.push(AssistantMessageEvent::Done {
            reason: DoneReason::Stop,
            message: message.clone(),
        });
        stream.end(Some(message));
        stream
    };
    let simple = respond.clone();
    ProviderStreams {
        stream: Arc::new(move |model, _context, _options| respond(model)),
        stream_simple: Arc::new(move |model, _context, _options| simple(model)),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}

fn mixed_model(api: &str, id: &str) -> Model {
    let mut model = common::test_model("mixed", id);
    api.clone_into(&mut model.api);
    model
}

fn keyless_auth() -> ProviderAuth {
    ProviderAuth {
        api_key: Some(common::ambient_auth()),
        oauth: None,
    }
}

fn handle_for(model: &Model) -> DeferredHandle {
    DeferredHandle {
        provider: model.provider.clone(),
        model_id: model.id.clone(),
        api: model.api.clone(),
        id: "response-1".into(),
        expires_at: None,
        poll_after_ms: None,
        data: None,
    }
}

#[tokio::test]
async fn lazily_exposes_only_declared_deferred_capabilities() {
    let loads = Arc::new(AtomicUsize::new(0));
    let mut streams = recording_streams("deferred", Arc::default());
    let simple = Arc::clone(&streams.stream_simple);
    streams.fetch_deferred = Some(Arc::new(move |model, _handle, _options| {
        simple(
            model,
            &normalize_context(context()),
            SimpleStreamOptions::default(),
        )
    }));
    let counter = Arc::clone(&loads);
    let api = lazy_api(
        Arc::new(move || {
            counter.fetch_add(1, Ordering::SeqCst);
            let streams = streams.clone();
            Box::pin(async move { Ok(streams) })
        }),
        LazyApiCapabilities {
            fetch_deferred: true,
            cancel_deferred: false,
        },
    );
    let model = mixed_model("api-a", "model-a");
    let handle = handle_for(&model);

    assert_eq!(loads.load(Ordering::SeqCst), 0);
    assert!(api.cancel_deferred.is_none());
    let fetch = api.fetch_deferred.expect("declared");
    assert_eq!(
        fetch(&model, &handle, DeferredFetchOptions::default())
            .result()
            .await
            .stop_reason,
        StopReason::Stop
    );
    assert_eq!(loads.load(Ordering::SeqCst), 1);
}

#[tokio::test]
async fn dispatches_on_model_api_for_mixed_api_providers() {
    let calls: Arc<Mutex<Vec<String>>> = Arc::default();
    let provider = create_provider(CreateProviderOptions {
        id: "mixed".into(),
        auth: keyless_auth(),
        models: vec![
            AnyModel::Chat(mixed_model("api-a", "model-a")),
            AnyModel::Chat(mixed_model("api-b", "model-b")),
        ],
        api: Some(ProviderApi::ByApi(IndexMap::from([
            (
                "api-a".to_owned(),
                recording_streams("a", Arc::clone(&calls)),
            ),
            (
                "api-b".to_owned(),
                recording_streams("b", Arc::clone(&calls)),
            ),
        ]))),
        ..CreateProviderOptions::default()
    })
    .expect("provider");
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(provider);

    models
        .complete_simple(
            &mixed_model("api-a", "model-a"),
            context(),
            SimpleStreamOptions::default().into(),
        )
        .await;
    models
        .complete_simple(
            &mixed_model("api-b", "model-b"),
            context(),
            SimpleStreamOptions::default().into(),
        )
        .await;
    assert_eq!(
        *calls.lock().unwrap_or_else(PoisonError::into_inner),
        ["a:model-a", "b:model-b"]
    );
}

fn resolving_auth(result: AuthResult) -> ProviderAuth {
    ProviderAuth {
        api_key: Some(
            common::FnApiKeyAuth::new("Test", move |_| {
                let result = result.clone();
                async move { Ok(Some(result)) }
            })
            .arc(),
        ),
        oauth: None,
    }
}

#[tokio::test]
async fn merges_provider_resolved_env_into_stream_options() {
    let captured: Arc<Mutex<(Option<ProviderEnv>, Option<String>)>> = Arc::default();
    let mut env_model = mixed_model("api-a", "model-a");
    env_model.provider = "env-provider".into();
    let base = recording_streams("a", Arc::default());
    let (stream_capture, simple_capture) = (Arc::clone(&captured), Arc::clone(&captured));
    let (base_stream, base_simple) = (Arc::clone(&base.stream), Arc::clone(&base.stream_simple));
    let provider = create_provider(CreateProviderOptions {
        id: "env-provider".into(),
        auth: resolving_auth(AuthResult {
            auth: ModelAuth {
                api_key: Some("provider-key".into()),
                ..ModelAuth::default()
            },
            env: Some(env_of(&[
                ("PROVIDER_ONLY", "provider"),
                ("SHARED", "provider"),
            ])),
            source: None,
        }),
        models: vec![AnyModel::Chat(env_model.clone())],
        api: Some(ProviderApi::Single(ProviderStreams {
            stream: Arc::new(move |model, context, options| {
                *stream_capture
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner) = (
                    options.stream.request.env.clone(),
                    options.stream.request.api_key.clone(),
                );
                base_stream(model, context, options)
            }),
            stream_simple: Arc::new(move |model, context, options| {
                *simple_capture
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner) = (
                    options.stream.request.env.clone(),
                    options.stream.request.api_key.clone(),
                );
                base_simple(model, context, options)
            }),
            fetch_deferred: None,
            cancel_deferred: None,
        })),
        ..CreateProviderOptions::default()
    })
    .expect("provider");
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(provider);

    let mut options = SimpleStreamOptions::default();
    options.stream.request.api_key = Some("request-key".into());
    options.stream.request.env = Some(env_of(&[
        ("REQUEST_ONLY", "request"),
        ("SHARED", "request"),
    ]));
    models
        .complete_simple(&env_model, context(), options.into())
        .await;

    let (env, api_key) = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(api_key.as_deref(), Some("request-key"));
    // TS `toEqual` ignores key order; the merged env keeps provider keys first.
    let mut env: Vec<(String, String)> = env.expect("env").into_iter().collect();
    env.sort();
    assert_eq!(
        env,
        [
            ("PROVIDER_ONLY".to_owned(), "provider".to_owned()),
            ("REQUEST_ONLY".to_owned(), "request".to_owned()),
            ("SHARED".to_owned(), "request".to_owned()),
        ]
    );
}

fn headers(entries: &[(&str, &str)]) -> ProviderHeaders {
    entries
        .iter()
        .map(|(k, v)| ((*k).to_owned(), Some((*v).to_owned())))
        .collect()
}

type FetchedDeferred = Arc<Mutex<Option<(Model, DeferredFetchOptions)>>>;
type CancelledDeferred = Arc<Mutex<Option<DeferredCancelOptions>>>;

/// The provider of the deferred request-options test: records what its
/// deferred fetch and cancel implementations receive.
fn deferred_recording_provider(
    deferred_model: &Model,
    fetched: &FetchedDeferred,
    cancelled: &CancelledDeferred,
) -> Provider {
    let mut streams = recording_streams("deferred", Arc::default());
    let simple = Arc::clone(&streams.stream_simple);
    let fetch_record = Arc::clone(fetched);
    streams.fetch_deferred = Some(Arc::new(move |model, _handle, options| {
        *fetch_record.lock().unwrap_or_else(PoisonError::into_inner) =
            Some((model.clone(), options));
        simple(
            model,
            &normalize_context(context()),
            SimpleStreamOptions::default(),
        )
    }));
    let cancel_record = Arc::clone(cancelled);
    streams.cancel_deferred = Some(Arc::new(move |_model, _handle, options| {
        *cancel_record.lock().unwrap_or_else(PoisonError::into_inner) = Some(options);
        Box::pin(async { Ok(()) })
    }));
    create_provider(CreateProviderOptions {
        id: "deferred-provider".into(),
        auth: resolving_auth(AuthResult {
            auth: ModelAuth {
                api_key: Some("provider-key".into()),
                base_url: Some("https://resolved.test/v1".into()),
                headers: Some(headers(&[
                    ("Authorization", "Bearer provider"),
                    ("X-Shared", "provider"),
                ])),
            },
            env: Some(env_of(&[
                ("PROVIDER_ONLY", "provider"),
                ("SHARED", "provider"),
            ])),
            source: None,
        }),
        models: vec![AnyModel::Chat(deferred_model.clone())],
        api: Some(ProviderApi::Single(streams)),
        ..CreateProviderOptions::default()
    })
    .expect("provider")
}

#[tokio::test]
async fn applies_resolved_request_options_to_deferred_fetch_and_cancellation() {
    let fetched: FetchedDeferred = Arc::default();
    let cancelled: CancelledDeferred = Arc::default();
    let mut deferred_model = mixed_model("api-a", "model-a");
    deferred_model.provider = "deferred-provider".into();
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(deferred_recording_provider(
        &deferred_model,
        &fetched,
        &cancelled,
    ));
    let handle = handle_for(&deferred_model);

    let mut fetch_options = DeferredFetchOptions {
        wait: Some(50.0),
        ..DeferredFetchOptions::default()
    };
    fetch_options.request.timeout_ms = Some(100.0);
    fetch_options.request.api_key = Some("request-key".into());
    fetch_options.request.headers = Some(headers(&[
        ("X-Request", "request"),
        ("x-shared", "request"),
    ]));
    fetch_options.request.env = Some(env_of(&[
        ("REQUEST_ONLY", "request"),
        ("SHARED", "request"),
    ]));
    models
        .fetch_deferred(
            &deferred_model,
            &handle,
            ModelsRequestOptions {
                options: fetch_options,
                transform_headers: Some(Arc::new(|mut headers: ProviderHeaders| {
                    headers.insert("X-Transformed".into(), Some("yes".into()));
                    Box::pin(async move { Ok(headers) })
                })),
            },
        )
        .await;
    let cancel_options = DeferredCancelOptions {
        timeout_ms: Some(200.0),
        ..DeferredCancelOptions::default()
    };
    models
        .cancel_deferred(
            &deferred_model,
            &handle,
            ModelsRequestOptions {
                options: cancel_options,
                transform_headers: Some(Arc::new(|mut headers: ProviderHeaders| {
                    headers.insert("X-Cancel".into(), Some("yes".into()));
                    Box::pin(async move { Ok(headers) })
                })),
            },
        )
        .await
        .expect("cancel");
    assert_deferred_request_options(&fetched, &cancelled);
}

/// Checks the options the deferred fetch and cancel implementations received.
fn assert_deferred_request_options(fetched: &FetchedDeferred, cancelled: &CancelledDeferred) {
    let (fetched_model, fetched_options) = fetched
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("fetched");
    assert_eq!(fetched_model.base_url, "https://resolved.test/v1");
    assert_eq!(fetched_options.wait, Some(50.0));
    assert_eq!(fetched_options.request.timeout_ms, Some(100.0));
    assert_eq!(
        fetched_options.request.api_key.as_deref(),
        Some("request-key")
    );
    assert_eq!(
        fetched_options.request.headers,
        Some(headers(&[
            ("Authorization", "Bearer provider"),
            ("X-Request", "request"),
            ("x-shared", "request"),
            ("X-Transformed", "yes"),
        ]))
    );
    assert_eq!(
        fetched_options.request.env,
        Some(env_of(&[
            ("PROVIDER_ONLY", "provider"),
            ("SHARED", "request"),
            ("REQUEST_ONLY", "request")
        ]))
    );
    let cancelled_options = cancelled
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("cancelled");
    assert_eq!(cancelled_options.timeout_ms, Some(200.0));
    assert_eq!(cancelled_options.api_key.as_deref(), Some("provider-key"));
    assert_eq!(
        cancelled_options.headers,
        Some(headers(&[
            ("Authorization", "Bearer provider"),
            ("X-Shared", "provider"),
            ("X-Cancel", "yes")
        ]))
    );
    assert_eq!(
        cancelled_options.env,
        Some(env_of(&[
            ("PROVIDER_ONLY", "provider"),
            ("SHARED", "provider")
        ]))
    );
}

#[tokio::test]
async fn produces_a_stream_error_for_a_model_whose_api_has_no_implementation() {
    let provider = create_provider(CreateProviderOptions {
        id: "mixed".into(),
        auth: keyless_auth(),
        models: vec![AnyModel::Chat(mixed_model("api-a", "model-a"))],
        api: Some(ProviderApi::ByApi(IndexMap::from([(
            "api-a".to_owned(),
            recording_streams("a", Arc::default()),
        )]))),
        ..CreateProviderOptions::default()
    })
    .expect("provider");
    let result = (provider.stream_simple)(
        &mixed_model("api-ghost", "model-x"),
        &normalize_context(context()),
        SimpleStreamOptions::default(),
    )
    .result()
    .await;
    assert_eq!(result.stop_reason, StopReason::Error);
    assert!(result
        .error_message
        .expect("message")
        .contains("no API implementation"));
}

#[tokio::test]
async fn lets_a_newer_dynamic_refresh_bypass_and_supersede_older_network_work() {
    let fetches = Arc::new(AtomicUsize::new(0));
    let first_started = Arc::new(Notify::new());
    let finish_first = Arc::new(Notify::new());
    let (count, started, finish) = (
        Arc::clone(&fetches),
        Arc::clone(&first_started),
        Arc::clone(&finish_first),
    );
    let provider = create_provider(CreateProviderOptions {
        id: "dynamic".into(),
        auth: keyless_auth(),
        fetch_models: Some(Arc::new(move |_context| {
            let (count, started, finish) = (
                Arc::clone(&count),
                Arc::clone(&started),
                Arc::clone(&finish),
            );
            Box::pin(async move {
                let current = count.fetch_add(1, Ordering::SeqCst) + 1;
                if current == 1 {
                    started.notify_one();
                    finish.notified().await;
                }
                Ok(vec![AnyModel::Chat(mixed_model(
                    "api-a",
                    &format!("listed-{current}"),
                ))])
            })
        })),
        api: Some(ProviderApi::Single(recording_streams("a", Arc::default()))),
        ..CreateProviderOptions::default()
    })
    .expect("provider");
    let get_models = Arc::clone(&provider.get_models);
    let listed = move || -> Vec<String> {
        get_models()
            .expect("models")
            .into_iter()
            .map(|model| model.id)
            .collect()
    };

    let store = Arc::new(InMemoryModelsStore::new());
    let models = create_models(CreateModelsOptions {
        models_store: Some(store.clone()),
        ..CreateModelsOptions::default()
    });
    models.set_provider(provider);
    assert!(listed().is_empty());

    let first_models = models.clone();
    let first = tokio::spawn(async move {
        first_models
            .refresh(ModelsRefreshOptions {
                providers: Some(vec!["dynamic".into()]),
                ..ModelsRefreshOptions::default()
            })
            .await
    });
    first_started.notified().await;
    let second = models
        .refresh(ModelsRefreshOptions {
            providers: Some(vec!["dynamic".into()]),
            ..ModelsRefreshOptions::default()
        })
        .await;
    assert!(!second.aborted);
    assert!(!first.await.expect("join").aborted);
    assert_eq!(fetches.load(Ordering::SeqCst), 2);
    assert_eq!(listed(), ["listed-2"]);
    let stored_ids = |store: Arc<InMemoryModelsStore>| async move {
        store
            .read("dynamic", ModelsStoreOperationOptions::default())
            .await
            .expect("read")
            .expect("entry")
            .models
            .iter()
            .map(|model| model.id().to_owned())
            .collect::<Vec<_>>()
    };
    assert_eq!(stored_ids(store.clone()).await, ["listed-2"]);

    finish_first.notify_one();
    for _ in 0..100 {
        tokio::task::yield_now().await;
    }
    assert_eq!(listed(), ["listed-2"]);
    assert_eq!(stored_ids(store).await, ["listed-2"]);
}

#[tokio::test]
async fn streams_queued_responses_through_a_models_collection() {
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(vec![faux_assistant_message(
        "hello from faux",
        FauxAssistantMessageOptions::default(),
    )
    .into()]);

    let model = models.get_models(Some(&faux.provider.id)).remove(0);
    let result = models
        .complete_simple(&model, context(), SimpleStreamOptions::default().into())
        .await;
    assert_eq!(result.stop_reason, StopReason::Stop);
    assert_eq!(
        result.content,
        vec![AssistantContentBlock::Text(TextContent::new(
            "hello from faux"
        ))]
    );
    assert_eq!(faux.state().call_count, 1);
}

fn deferred_options(request: DeferredRequest) -> SimpleStreamOptions {
    SimpleStreamOptions {
        deferred: Some(request),
        ..SimpleStreamOptions::default()
    }
}

#[tokio::test]
async fn submits_polls_and_redeems_deferred_responses() {
    let faux = faux_provider(RegisterFauxProviderOptions {
        deferred: Some(FauxDeferredOptions {
            pending_fetches: Some(1.0),
            poll_after_ms: Some(25.0),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(vec![faux_assistant_message(
        "ready",
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let model = faux.get_model();

    let submission = models.stream_simple(
        &model,
        context(),
        deferred_options(DeferredRequest::Window(Some(DeferredWindow::Hours1))).into(),
    );
    let event_types: Vec<&'static str> = submission
        .events()
        .map(|event| event.type_name())
        .collect()
        .await;
    let deferred = submission.result().await;
    assert_eq!(event_types, ["start", "done"]);
    assert_eq!(deferred.stop_reason, StopReason::Deferred);
    assert!(deferred.content.is_empty());
    let handle = deferred
        .deferred
        .clone()
        .expect("Faux response did not include a deferred handle");
    assert_eq!(
        (
            handle.provider.as_str(),
            handle.model_id.as_str(),
            handle.api.as_str(),
            handle.poll_after_ms
        ),
        (
            model.provider.as_str(),
            model.id.as_str(),
            model.api.as_str(),
            Some(25.0)
        )
    );
    assert!(!handle.id.is_empty());
    assert_eq!((handle.expires_at, handle.data.clone()), (None, None));

    let pending = models
        .fetch_deferred(&model, &handle, DeferredFetchOptions::default().into())
        .await;
    assert_eq!(pending.stop_reason, StopReason::Deferred);
    assert_eq!(pending.deferred.as_ref(), Some(&handle));

    let ready = models
        .fetch_deferred(
            &model,
            &handle,
            DeferredFetchOptions {
                wait: Some(0.0),
                ..DeferredFetchOptions::default()
            }
            .into(),
        )
        .await;
    assert_eq!(ready.stop_reason, StopReason::Stop);
    assert_eq!(
        ready.content,
        vec![AssistantContentBlock::Text(TextContent::new("ready"))]
    );
    assert!(ready.usage.total_tokens > 0);
    let state = faux.state();
    assert_eq!((state.call_count, state.deferred_fetch_count), (1, 2));
}

#[tokio::test]
async fn records_cancellation_and_returns_deferred_fetch_failures_in_band() {
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(vec![
        FauxResponseStep::Factory(Arc::new(|_, _, _, _| {
            Box::pin(async { Err(common::error("deferred failed")) })
        })),
        faux_assistant_message("cancelled", FauxAssistantMessageOptions::default()).into(),
    ]);
    let model = faux.get_model();

    let failed_submission = models
        .complete_simple(
            &model,
            context(),
            deferred_options(DeferredRequest::Flag(true)).into(),
        )
        .await;
    let failed_handle = failed_submission
        .deferred
        .expect("Faux response did not include a deferred handle");
    let failed = models
        .fetch_deferred(
            &model,
            &failed_handle,
            DeferredFetchOptions::default().into(),
        )
        .await;
    assert_eq!(failed.stop_reason, StopReason::Error);
    assert_eq!(failed.error_message.as_deref(), Some("deferred failed"));

    let cancelled_submission = models
        .complete_simple(
            &model,
            context(),
            deferred_options(DeferredRequest::Flag(true)).into(),
        )
        .await;
    let cancelled_handle = cancelled_submission
        .deferred
        .expect("Faux response did not include a deferred handle");
    models
        .cancel_deferred(
            &model,
            &cancelled_handle,
            DeferredCancelOptions::default().into(),
        )
        .await
        .expect("cancel");
    assert_eq!(
        faux.state().cancelled_deferred,
        vec![cancelled_handle.clone()]
    );
    let cancelled = models
        .fetch_deferred(
            &model,
            &cancelled_handle,
            DeferredFetchOptions::default().into(),
        )
        .await;
    assert_eq!(cancelled.stop_reason, StopReason::Error);
    assert!(cancelled
        .error_message
        .expect("message")
        .contains("was cancelled"));
}

/// Every API id a built-in model names has a built-in registry entry (the
/// Rust counterpart of each `src/api/*.lazy.ts` import resolving).
#[test]
fn every_builtin_model_api_has_a_registered_implementation() {
    for provider in builtin_providers() {
        for model in get_all_builtin_models(&provider.id) {
            let (api, loaded) = match &model {
                AnyModel::Chat(model) => (&model.api, load_stream_api(&model.api).is_ok()),
                AnyModel::Image(model) => (&model.api, load_image_api(&model.api).is_ok()),
                AnyModel::Classifier(model) => {
                    (&model.api, load_classifier_api(&model.api).is_ok())
                }
            };
            assert!(
                loaded,
                "{}: no registered API module for {api}",
                provider.id
            );
        }
    }
}
