//! The `prime-inference` provider (eukhe addition; ported from
//! `crates/eukhe-ai` and `crates/eukhe-models`).
//!
//! An `openai-completions` provider with a live, credentialed catalog: the
//! compiled offline entries serve until the first refresh fetches
//! `GET /models` with `Authorization: Bearer <key>` and `X-Prime-Team-ID`
//! when a team is configured. The live list replaces the offline one;
//! entries without a compiled template are accepted only with full specs,
//! and a coverage gate (at least half of the compiled entries) keeps a
//! partial fetch from replacing a good catalog. The live routes'
//! `supported_parameters` / `reasoning` declarations drive their reasoning
//! request controls. Catalogs persist through the `ModelsStore`; refreshes
//! run at most hourly unless forced; 401/403 clears the persisted catalog.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::{
    AnyModel, CacheControlFormat, JsonValue, MaxTokensField, Modality, Model, ModelCompat,
    ModelCost, ModelThinkingLevel, OpenAICompletionsCompat, ProviderHeaders, ThinkingFormat,
    ThinkingLevelMap,
};
use futures::future::BoxFuture;

use super::prime_inference_models::PRIME_INFERENCE_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthPrompt, AuthPromptKind, AuthResult,
    Credential, ModelAuth, ProviderAuth, ProviderAuthInteraction,
};
use crate::models::{
    date_now, ModelsPersistence, ModelsPublication, Provider, RefreshModelsContext,
};
use crate::models_store::ModelsStoreEntry;
use crate::types::ProviderEnv;
use crate::utils::diagnostics::{ErrorObject, Thrown};

/// The provider id.
pub const PRIME_INFERENCE_PROVIDER_ID: &str = "prime-inference";

/// The Prime Inference API base URL (models at `/models`).
pub const PRIME_INFERENCE_BASE_URL: &str = "https://api.pinference.ai/api/v1";

/// API key environment variable.
pub const PRIME_API_KEY_ENV: &str = "PRIME_API_KEY";

/// Team environment variable / credential env key; sent as `X-Prime-Team-ID`.
pub const PRIME_TEAM_ID_ENV: &str = "PRIME_TEAM_ID";

/// Hard response cap for the credentialed fetch.
const MAX_RESPONSE_BYTES: usize = 2 * 1024 * 1024;

/// Minimum share of compiled entries a live fetch must cover.
const MIN_CATALOG_COVERAGE: f64 = 0.5;

/// Refresh cadence without `force`.
const REFRESH_INTERVAL_MS: f64 = 60.0 * 60.0 * 1000.0;

/// One sanitized entry of the `/models` response.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct PrimeInferenceEntry {
    pub id: String,
    pub name: Option<String>,
    pub input: f64,
    pub output: f64,
    pub cache_read: Option<f64>,
    pub cache_write: Option<f64>,
    pub context_window: Option<u64>,
    pub max_tokens: Option<u64>,
    pub vision: Option<bool>,
    pub reasoning: Option<bool>,
    /// Request parameter names the live route declares.
    pub supported_parameters: Option<Vec<String>>,
    /// Reasoning effort values the live route declares.
    pub reasoning_efforts: Option<Vec<String>>,
    /// Whether the live route rejects requests that disable reasoning.
    pub reasoning_mandatory: Option<bool>,
}

/// Reasoning request controls derived from a live catalog entry. The gateway
/// validates reasoning values per route and rejects undeclared efforts, so
/// only declared values are ever sent.
#[derive(Debug, Clone, PartialEq)]
pub struct PrimeInferenceReasoningControls {
    pub supports_reasoning_effort: bool,
    pub thinking_format: Option<ThinkingFormat>,
    pub thinking_level_map: Option<ThinkingLevelMap>,
}

const REASONING_EFFORT_LEVELS: [ModelThinkingLevel; 6] = [
    ModelThinkingLevel::Minimal,
    ModelThinkingLevel::Low,
    ModelThinkingLevel::Medium,
    ModelThinkingLevel::High,
    ModelThinkingLevel::Xhigh,
    ModelThinkingLevel::Max,
];

/// Derive reasoning request controls from the parameters a live route
/// declares; `None` when the route reports no parameter support.
#[must_use]
pub fn prime_inference_reasoning_controls(
    entry: &PrimeInferenceEntry,
) -> Option<PrimeInferenceReasoningControls> {
    let supported = entry.supported_parameters.as_ref()?;
    let includes = |parameter: &str| supported.iter().any(|candidate| candidate == parameter);
    let supports_reasoning_effort = includes("reasoning_effort");
    let mandatory = entry.reasoning_mandatory == Some(true);
    let mut thinking_level_map = None;
    if let (true, Some(efforts)) = (supports_reasoning_effort, &entry.reasoning_efforts) {
        // Non-mandatory effort routes accept "none" as the disable value.
        let mut map = ThinkingLevelMap::new();
        map.insert(
            ModelThinkingLevel::Off,
            (!mandatory).then(|| "none".to_owned()),
        );
        for level in REASONING_EFFORT_LEVELS {
            let name = level.as_str();
            map.insert(
                level,
                efforts
                    .iter()
                    .any(|effort| effort == name)
                    .then(|| name.to_owned()),
            );
        }
        thinking_level_map = Some(map);
    } else if includes("reasoning") {
        // The route can only toggle reasoning on or off: one generic level.
        let mut map = ThinkingLevelMap::new();
        if mandatory {
            map.insert(ModelThinkingLevel::Off, None);
        }
        for level in [
            ModelThinkingLevel::Minimal,
            ModelThinkingLevel::Low,
            ModelThinkingLevel::Medium,
            ModelThinkingLevel::Xhigh,
            ModelThinkingLevel::Max,
        ] {
            map.insert(level, None);
        }
        map.insert(ModelThinkingLevel::High, Some("high".to_owned()));
        thinking_level_map = Some(map);
    }
    let thinking_format = if includes("enable_thinking") {
        Some(ThinkingFormat::Zai)
    } else if includes("reasoning") && !supports_reasoning_effort {
        Some(ThinkingFormat::OpenRouter)
    } else {
        None
    };
    Some(PrimeInferenceReasoningControls {
        supports_reasoning_effort,
        thinking_format,
        thinking_level_map,
    })
}

/// Whether a model id is private (internal/, dev/, or alias-qualified with `:`).
#[must_use]
pub fn is_private_prime_inference_model_id(model_id: &str) -> bool {
    let normalized = model_id.to_ascii_lowercase();
    normalized.starts_with("internal/")
        || normalized.starts_with("dev/")
        || normalized.contains(':')
}

fn is_control(character: char) -> bool {
    let code = u32::from(character);
    code <= 0x1f || (0x7f..=0x9f).contains(&code)
}

/// A non-empty, de-duplicated list of non-empty strings; non-strings drop.
fn parse_string_array(value: Option<&JsonValue>) -> Option<Vec<String>> {
    let items = value?.as_array()?;
    let mut seen: HashSet<&str> = HashSet::with_capacity(items.len());
    let entries: Vec<String> = items
        .iter()
        .filter_map(JsonValue::as_str)
        .filter(|text| !text.is_empty() && seen.insert(text))
        .map(str::to_owned)
        .collect();
    (!entries.is_empty()).then_some(entries)
}

fn non_negative(value: Option<&JsonValue>) -> Option<f64> {
    value?
        .as_f64()
        .filter(|value| value.is_finite() && *value >= 0.0)
}

fn positive_integer(value: Option<&JsonValue>) -> Option<u64> {
    value?.as_u64().filter(|value| *value > 0)
}

/// Whether an empty parsed catalog is accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmptyCatalog {
    Allow,
    Reject,
}

/// Whether private model ids enter the built list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrivateModels {
    Include,
    Exclude,
}

/// Parses the `/models` payload. Entries with unusable data drop; a model
/// that declares its supported parameters without `tools` drops (a session
/// always attaches tools); duplicate ids reject the whole payload.
///
/// # Errors
///
/// A payload without a `data` array, a duplicate id, or (unless
/// [`EmptyCatalog::Allow`]) no usable entry.
#[allow(clippy::too_many_lines)] // One sanitization pass per wire entry.
pub fn parse_prime_inference_model_catalog(
    value: &JsonValue,
    empty: EmptyCatalog,
) -> Result<Vec<PrimeInferenceEntry>, String> {
    let Some(items) = value.get("data").and_then(JsonValue::as_array) else {
        return Err("Invalid Prime Inference model catalog".to_owned());
    };
    let mut entries = Vec::with_capacity(items.len());
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for item in items {
        let Some(item) = item.as_object() else {
            continue;
        };
        let Some(id) = item.get("id").and_then(JsonValue::as_str) else {
            continue;
        };
        if id.is_empty() || id.chars().count() > 1_024 || id.chars().any(is_control) {
            continue;
        }
        let pricing = item.get("pricing").and_then(JsonValue::as_object);
        let price = |key: &str| non_negative(pricing.and_then(|pricing| pricing.get(key)));
        let (Some(input), Some(output)) =
            (price("input_usd_per_mtok"), price("output_usd_per_mtok"))
        else {
            continue;
        };
        if !seen.insert(id.to_owned()) {
            return Err(format!("Duplicate Prime Inference model {id}"));
        }
        let supported_parameters = parse_string_array(item.get("supported_parameters"));
        if supported_parameters
            .as_ref()
            .is_some_and(|parameters| !parameters.iter().any(|parameter| parameter == "tools"))
        {
            continue;
        }
        let name = item
            .get("display_name")
            .and_then(JsonValue::as_str)
            .map(|name| {
                name.chars()
                    .filter(|character| !is_control(*character))
                    .collect::<String>()
            })
            .map(|name| name.trim().to_owned())
            .filter(|name| !name.is_empty());
        let specs = item.get("specs").and_then(JsonValue::as_object);
        let spec = |key: &str| specs.and_then(|specs| specs.get(key));
        let modalities = spec("modalities").and_then(JsonValue::as_object);
        let modality_list = |key: &str| -> Vec<String> {
            modalities
                .and_then(|modalities| modalities.get(key))
                .and_then(JsonValue::as_array)
                .map(|values| {
                    values
                        .iter()
                        .filter_map(JsonValue::as_str)
                        .map(str::to_owned)
                        .collect()
                })
                .unwrap_or_default()
        };
        let input_modalities = modality_list("input");
        let supports_reasoning = spec("supports_reasoning").and_then(JsonValue::as_bool);
        let has_specs = spec("context_window").and_then(JsonValue::as_u64).is_some()
            && spec("max_output_tokens")
                .and_then(JsonValue::as_u64)
                .is_some()
            && supports_reasoning.is_some()
            && !input_modalities.is_empty()
            && !modality_list("output").is_empty();
        let reasoning_spec = item.get("reasoning").and_then(JsonValue::as_object);
        let mut entry = PrimeInferenceEntry {
            id: id.to_owned(),
            name,
            input,
            output,
            cache_read: price("cache_read_usd_per_mtok"),
            cache_write: price("cache_write_usd_per_mtok"),
            supported_parameters,
            reasoning_efforts: reasoning_spec
                .and_then(|spec| parse_string_array(spec.get("supported_efforts"))),
            reasoning_mandatory: reasoning_spec
                .and_then(|spec| spec.get("mandatory"))
                .and_then(JsonValue::as_bool)
                .filter(|mandatory| *mandatory),
            ..PrimeInferenceEntry::default()
        };
        if has_specs {
            let context_window = positive_integer(spec("context_window")).unwrap_or_default();
            entry.context_window = Some(context_window);
            entry.max_tokens = Some(
                positive_integer(spec("max_output_tokens"))
                    .map(|max| max.min(context_window))
                    .unwrap_or_default(),
            );
            entry.vision = Some(input_modalities.iter().any(|modality| modality == "image"));
            entry.reasoning = supports_reasoning;
        }
        entries.push(entry);
    }
    if entries.is_empty() && empty == EmptyCatalog::Reject {
        return Err("Prime Inference model catalog is empty".to_owned());
    }
    Ok(entries)
}

/// The default compat for live entries without a compiled template.
fn default_compat() -> OpenAICompletionsCompat {
    OpenAICompletionsCompat {
        supports_store: Some(false),
        supports_developer_role: Some(false),
        supports_reasoning_effort: Some(false),
        max_tokens_field: Some(MaxTokensField::MaxTokens),
        supports_strict_mode: Some(false),
        ..OpenAICompletionsCompat::default()
    }
}

/// Builds the live model list from fetched entries against the compiled
/// templates; `None` when the coverage gate rejects the result.
#[must_use]
#[allow(clippy::too_many_lines)] // One merge pass per entry plus the coverage gate.
pub fn build_prime_inference_models(
    bundled: &[Model],
    entries: &[PrimeInferenceEntry],
    private_models: PrivateModels,
    minimum_models: Option<usize>,
) -> Option<Vec<Model>> {
    let templates: HashMap<String, &Model> = bundled
        .iter()
        .map(|model| (model.id.to_ascii_lowercase(), model))
        .collect();
    let mut models = Vec::with_capacity(entries.len());
    for entry in entries {
        if private_models == PrivateModels::Exclude
            && is_private_prime_inference_model_id(&entry.id)
        {
            continue;
        }
        let template = templates.get(&entry.id.to_ascii_lowercase()).copied();
        if template.is_none()
            && (entry.context_window.is_none()
                || entry.max_tokens.is_none()
                || entry.reasoning.is_none())
        {
            continue;
        }
        let context_window = entry
            .context_window
            .or_else(|| template.map(|template| template.context_window))
            .unwrap_or_default();
        let max_tokens = entry
            .max_tokens
            .or_else(|| template.map(|template| template.max_tokens))
            .unwrap_or_default()
            .min(context_window);
        let anthropic = entry.id.to_ascii_lowercase().starts_with("anthropic/");
        let mut compat = template
            .and_then(|template| template.compat.as_ref())
            .and_then(ModelCompat::as_openai_completions)
            .cloned()
            .unwrap_or_else(default_compat);
        if anthropic {
            compat.cache_control_format = Some(CacheControlFormat::Anthropic);
        }
        let controls = prime_inference_reasoning_controls(entry);
        if let Some(controls) = &controls {
            // The live catalog is authoritative for which reasoning
            // parameters the route accepts.
            compat.supports_reasoning_effort = Some(controls.supports_reasoning_effort);
            compat.thinking_format = controls.thinking_format;
        }
        let thinking_level_map = match &controls {
            Some(controls) => controls.thinking_level_map.clone(),
            None => template.and_then(|template| template.thinking_level_map.clone()),
        };
        let fallback_rate = |template_rate: Option<f64>, anthropic_factor: f64| {
            template_rate.unwrap_or(if anthropic {
                entry.input * anthropic_factor
            } else {
                0.0
            })
        };
        let cache_read = entry.cache_read.unwrap_or_else(|| {
            fallback_rate(template.map(|template| template.cost.cache_read), 0.1)
        });
        let cache_write = entry.cache_write.unwrap_or_else(|| {
            fallback_rate(template.map(|template| template.cost.cache_write), 1.25)
        });
        let vision = entry
            .vision
            .or_else(|| template.map(|template| template.input.contains(&Modality::Image)))
            .unwrap_or(false);
        models.push(Model {
            id: entry.id.clone(),
            name: entry
                .name
                .clone()
                .or_else(|| template.map(|template| template.name.clone()))
                .unwrap_or_else(|| entry.id.clone()),
            api: "openai-completions".to_owned(),
            provider: PRIME_INFERENCE_PROVIDER_ID.to_owned(),
            base_url: PRIME_INFERENCE_BASE_URL.to_owned(),
            input: if vision {
                vec![Modality::Text, Modality::Image]
            } else {
                vec![Modality::Text]
            },
            input_limits: template.and_then(|template| template.input_limits.clone()),
            cost: ModelCost {
                input: entry.input,
                output: entry.output,
                cache_read,
                cache_write,
                tiers: None,
            },
            headers: None,
            model_type: None,
            reasoning: entry
                .reasoning
                .or_else(|| template.map(|template| template.reasoning))
                .unwrap_or_default(),
            thinking_level_map,
            prompt_cache: None,
            context_window,
            max_tokens,
            sampling_params: None,
            sampling_params_by_thinking_level: None,
            compat: Some(ModelCompat::OpenAICompletions(compat)),
            featured: template.and_then(|template| template.featured),
        });
    }
    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_precision_loss,
        clippy::cast_sign_loss
    )]
    // `ceil` of a small non-negative product: exact and in range.
    let minimum_models = minimum_models
        .unwrap_or_else(|| ((bundled.len() as f64) * MIN_CATALOG_COVERAGE).ceil() as usize);
    let covered = models
        .iter()
        .filter(|model| templates.contains_key(&model.id.to_ascii_lowercase()))
        .count();
    (covered >= minimum_models).then_some(models)
}

/// Api-key auth: stored key or `PRIME_API_KEY`; the team (stored
/// `PRIME_TEAM_ID` env or the ambient variable) becomes the
/// `X-Prime-Team-ID` header and travels in the resolved env.
struct PrimeInferenceAuth;

impl ApiKeyAuth for PrimeInferenceAuth {
    // The trait returns a borrowed name; this one is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        "Prime Inference API key"
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
    ) -> Option<BoxFuture<'_, Result<ApiKeyCredential, Thrown>>> {
        Some(Box::pin(async move {
            interaction.signal.throw_if_aborted()?;
            let key = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Secret {
                    message: "Enter Prime Inference API key".to_owned(),
                    placeholder: None,
                }))
                .await?;
            interaction.signal.throw_if_aborted()?;
            Ok(ApiKeyCredential::with_key(key))
        }))
    }

    fn resolve(
        &self,
        input: ApiKeyResolveInput,
    ) -> BoxFuture<'_, Result<Option<AuthResult>, Thrown>> {
        Box::pin(async move {
            let ApiKeyResolveInput {
                ctx,
                credential,
                signal,
            } = input;
            signal.throw_if_aborted()?;
            let stored_key = credential
                .as_ref()
                .and_then(|credential| credential.key.clone())
                .filter(|key| !key.is_empty());
            let (key, source) = if let Some(key) = stored_key {
                (key, "stored credential")
            } else {
                let ambient = ctx
                    .env(PRIME_API_KEY_ENV)
                    .await
                    .filter(|key| !key.is_empty());
                signal.throw_if_aborted()?;
                let Some(key) = ambient else { return Ok(None) };
                (key, PRIME_API_KEY_ENV)
            };
            let mut env: Option<ProviderEnv> = credential
                .as_ref()
                .and_then(|credential| credential.env.clone());
            let stored_team = env
                .as_ref()
                .and_then(|env| env.get(PRIME_TEAM_ID_ENV))
                .filter(|team| !team.is_empty())
                .cloned();
            let team = if stored_team.is_some() {
                stored_team
            } else {
                let ambient = ctx
                    .env(PRIME_TEAM_ID_ENV)
                    .await
                    .filter(|team| !team.is_empty());
                signal.throw_if_aborted()?;
                ambient
            };
            let headers = team.map(|team| {
                env.get_or_insert_with(ProviderEnv::new)
                    .insert(PRIME_TEAM_ID_ENV.to_owned(), team.clone());
                ProviderHeaders::from([("X-Prime-Team-ID".to_owned(), Some(team))])
            });
            Ok(Some(AuthResult {
                auth: ModelAuth {
                    api_key: Some(key),
                    headers,
                    base_url: None,
                },
                env,
                source: Some(source.to_owned()),
            }))
        })
    }
}

struct PrimeCatalog {
    offline: Vec<Model>,
    live: Mutex<Option<Vec<Model>>>,
}

impl PrimeCatalog {
    fn models(&self) -> Vec<Model> {
        self.live
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
            .unwrap_or_else(|| self.offline.clone())
    }

    fn set_live(&self, models: Option<Vec<Model>>) {
        *self.live.lock().unwrap_or_else(PoisonError::into_inner) = models;
    }
}

/// HTTP outcome of the catalog fetch.
enum FetchOutcome {
    Payload(JsonValue),
    Unauthorized(u16),
}

fn error(message: String) -> Thrown {
    ErrorObject::new(message).thrown()
}

async fn fetch_catalog(
    base_url: &str,
    api_key: &str,
    team: Option<&str>,
) -> Result<FetchOutcome, Thrown> {
    let mut request = reqwest::Client::new()
        .get(format!("{base_url}/models"))
        .header("Authorization", format!("Bearer {api_key}"))
        .header("accept", "application/json");
    if let Some(team) = team {
        request = request.header("X-Prime-Team-ID", team);
    }
    let mut response = request
        .send()
        .await
        .map_err(|failure| ErrorObject::named("TypeError", failure.to_string()).thrown())?;
    let status = response.status().as_u16();
    if status == 401 || status == 403 {
        return Ok(FetchOutcome::Unauthorized(status));
    }
    if !response.status().is_success() {
        return Err(error(format!(
            "Prime Inference model catalog request failed: {status}"
        )));
    }
    let mut body: Vec<u8> = Vec::new();
    while let Some(chunk) = response
        .chunk()
        .await
        .map_err(|failure| ErrorObject::named("TypeError", failure.to_string()).thrown())?
    {
        if body.len() + chunk.len() > MAX_RESPONSE_BYTES {
            return Err(error(
                "Prime Inference model catalog exceeds the size limit".to_owned(),
            ));
        }
        body.extend_from_slice(&chunk);
    }
    serde_json::from_slice(&body)
        .map(FetchOutcome::Payload)
        .map_err(|failure| ErrorObject::named("SyntaxError", failure.to_string()).thrown())
}

async fn refresh_prime_models(
    base_url: String,
    catalog: Arc<PrimeCatalog>,
    context: RefreshModelsContext,
) -> Result<(), Thrown> {
    if let Some(stored) = &context.stored {
        let restored: Vec<Model> = stored
            .models
            .iter()
            .filter_map(|model| match model {
                AnyModel::Chat(model) if model.provider == PRIME_INFERENCE_PROVIDER_ID => {
                    Some(model.clone())
                }
                AnyModel::Chat(_) | AnyModel::Image(_) | AnyModel::Classifier(_) => None,
            })
            .collect();
        let restore_catalog = Arc::clone(&catalog);
        let published = context
            .publish(ModelsPublication {
                persist: ModelsPersistence::Keep,
                update: Some(Box::new(move || restore_catalog.set_live(Some(restored)))),
            })
            .await?;
        if !published {
            return Ok(());
        }
    }
    if !context.allow_network || context.signal.aborted() {
        return Ok(());
    }
    let fresh = context
        .stored
        .as_ref()
        .and_then(|stored| stored.checked_at)
        .is_some_and(|checked_at| date_now() - checked_at < REFRESH_INTERVAL_MS);
    if fresh && context.force != Some(true) {
        return Ok(());
    }
    let (api_key, team) = match &context.credential {
        Some(Credential::ApiKey(credential)) => (
            credential.key.clone(),
            credential
                .env
                .as_ref()
                .and_then(|env| env.get(PRIME_TEAM_ID_ENV))
                .cloned(),
        ),
        Some(Credential::OAuth(credential)) => (Some(credential.access.clone()), None),
        None => (None, None),
    };
    let Some(api_key) = api_key.filter(|key| !key.is_empty()) else {
        return Ok(());
    };
    let outcome = tokio::select! {
        outcome = fetch_catalog(&base_url, &api_key, team.as_deref().filter(|team| !team.is_empty())) => outcome?,
        reason = context.signal.cancelled() => return Err(reason),
    };
    let payload = match outcome {
        FetchOutcome::Payload(payload) => payload,
        FetchOutcome::Unauthorized(status) => {
            context
                .publish(ModelsPublication {
                    persist: ModelsPersistence::Delete,
                    update: Some(Box::new(move || catalog.set_live(None))),
                })
                .await?;
            return Err(error(format!(
                "Prime Inference model catalog request failed: {status}"
            )));
        }
    };
    let entries =
        parse_prime_inference_model_catalog(&payload, EmptyCatalog::Reject).map_err(error)?;
    let refreshed =
        build_prime_inference_models(&catalog.offline, &entries, PrivateModels::Exclude, None)
            .ok_or_else(|| error("Prime Inference catalog coverage gate failed".to_owned()))?;
    let persisted: Vec<AnyModel> = refreshed.iter().cloned().map(AnyModel::Chat).collect();
    context
        .publish(ModelsPublication {
            persist: ModelsPersistence::Write(ModelsStoreEntry {
                models: persisted,
                checked_at: Some(date_now()),
                ..ModelsStoreEntry::default()
            }),
            update: Some(Box::new(move || catalog.set_live(Some(refreshed)))),
        })
        .await?;
    Ok(())
}

/// The Prime Inference provider against `base_url` (test seam for a local
/// server); [`prime_inference_provider`] uses the production endpoint.
#[must_use]
pub fn prime_inference_provider_with_base_url(base_url: &str) -> Provider {
    let catalog = Arc::new(PrimeCatalog {
        offline: PRIME_INFERENCE_MODELS.values().cloned().collect(),
        live: Mutex::new(None),
    });
    let streams = openai_completions_api();
    let models_catalog = Arc::clone(&catalog);
    let base_url = base_url.to_owned();
    Provider {
        id: PRIME_INFERENCE_PROVIDER_ID.to_owned(),
        name: "Prime Inference".to_owned(),
        base_url: Some(PRIME_INFERENCE_BASE_URL.to_owned()),
        headers: None,
        auth: ProviderAuth {
            api_key: Some(Arc::new(PrimeInferenceAuth)),
            oauth: None,
        },
        get_models: Arc::new(move || Ok(models_catalog.models())),
        get_all_models: None,
        refresh_models: Some(Arc::new(move |context| {
            Box::pin(refresh_prime_models(
                base_url.clone(),
                Arc::clone(&catalog),
                context,
            ))
        })),
        filter_models: None,
        filter_all_models: None,
        stream: streams.stream,
        stream_simple: streams.stream_simple,
        fetch_deferred: None,
        cancel_deferred: None,
        generate_images: None,
        classify: None,
    }
}

/// The Prime Inference provider (eukhe addition).
#[must_use]
pub fn prime_inference_provider() -> Provider {
    prime_inference_provider_with_base_url(PRIME_INFERENCE_BASE_URL)
}
