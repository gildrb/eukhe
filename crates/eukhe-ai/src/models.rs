//! The runtime provider collection. Port of `models.ts`.
//!
//! A [`Provider`] is the concrete runtime unit: id, name, auth methods, model
//! listing, and the operations its models support. [`Models`] holds
//! providers, resolves auth, and delegates each request to the provider that
//! owns the model. [`create_provider`] builds a provider from parts; built-in
//! provider factories and custom providers both go through it.

mod capabilities;
mod collection;
mod create_provider;
mod ladder;
mod provider;
mod refresh;
mod requests;
mod thinking;

use eukhe_types::pi_ai::IndexMap;
use eukhe_types::pi_ai::{
    AnyModel, ClassifierModel, ImageModel, Model, ModelCost, ModelCostRates, ModelType,
    ProviderHeaders, Usage, UsageCost,
};

pub use capabilities::ModelsCapabilityOptions;
pub use collection::{create_models, CreateModelsOptions, Models};
pub(crate) use create_provider::build_provider;
pub use create_provider::{
    create_provider, CreateProviderError, CreateProviderOptions, FetchModelsFn, ProviderApi,
};
pub use ladder::{
    clamp_thinking_level, cycle_thinking_level, get_supported_thinking_levels,
    registry_clamp_thinking_level, registry_rule_ladder, registry_thinking_levels,
    thinking_level_map,
};
pub use provider::{
    chat_models, FilterAllModelsFn, FilterModelsFn, GetModelsFn, ModelsPersistence,
    ModelsPublication, Provider, PublishFn, RefreshModelsContext, RefreshModelsFn,
};
pub use refresh::{ModelsRefreshOptions, ModelsRefreshResult};
pub use requests::{
    ModelsApiStreamOptions, ModelsClassifierOptions, ModelsDeferredCancelOptions,
    ModelsDeferredFetchOptions, ModelsImagesOptions, ModelsRequestOptions,
    ModelsSimpleStreamOptions, TransformHeadersFn,
};
pub use thinking::adaptive_thinking;

pub use crate::utils::model_operations::{get_model_type, is_model_type};
pub use crate::utils::models_error::{ModelsError, ModelsErrorCode};

/// Read access shared by every catalog entry type, so auth application and
/// request dispatch work across chat, image, and classifier models (TS
/// `AnyModel` structural access).
pub trait CatalogModel: Clone + Send + Sync + 'static {
    /// The model id.
    fn model_id(&self) -> &str;
    /// The owning provider id.
    fn provider_id(&self) -> &str;
    /// The model's API id.
    fn api_id(&self) -> &str;
    /// What the entry is for.
    fn catalog_type(&self) -> ModelType;
    /// Static per-model request headers.
    fn model_headers(&self) -> Option<&IndexMap<String, String>>;
    /// The model's prices.
    fn model_cost(&self) -> &ModelCost;
    /// The request base URL.
    fn model_base_url(&self) -> &str;
    /// Replaces the base URL (auth-provided per-credential endpoints).
    fn set_base_url(&mut self, base_url: String);
}

macro_rules! impl_catalog_model {
    ($ty:ty, $model_type:expr) => {
        impl CatalogModel for $ty {
            fn model_id(&self) -> &str {
                &self.id
            }
            fn provider_id(&self) -> &str {
                &self.provider
            }
            fn api_id(&self) -> &str {
                &self.api
            }
            fn catalog_type(&self) -> ModelType {
                $model_type
            }
            fn model_headers(&self) -> Option<&IndexMap<String, String>> {
                self.headers.as_ref()
            }
            fn model_cost(&self) -> &ModelCost {
                &self.cost
            }
            fn model_base_url(&self) -> &str {
                &self.base_url
            }
            fn set_base_url(&mut self, base_url: String) {
                self.base_url = base_url;
            }
        }
    };
}

impl_catalog_model!(Model, ModelType::Chat);
impl_catalog_model!(ImageModel, ModelType::Image);
impl_catalog_model!(ClassifierModel, ModelType::Classifier);

impl CatalogModel for AnyModel {
    fn model_id(&self) -> &str {
        self.id()
    }
    fn provider_id(&self) -> &str {
        self.provider()
    }
    fn api_id(&self) -> &str {
        self.api()
    }
    fn catalog_type(&self) -> ModelType {
        self.model_type()
    }
    fn model_headers(&self) -> Option<&IndexMap<String, String>> {
        self.headers()
    }
    fn model_cost(&self) -> &ModelCost {
        self.cost()
    }
    fn model_base_url(&self) -> &str {
        self.base_url()
    }
    fn set_base_url(&mut self, base_url: String) {
        AnyModel::set_base_url(self, base_url);
    }
}

/// Merges `override_headers` over `base`: an override replaces every base
/// header whose name matches case-insensitively and lands at the end, in
/// override order. `None` when both are absent.
pub(crate) fn merge_headers(
    base: Option<&ProviderHeaders>,
    override_headers: Option<&ProviderHeaders>,
) -> Option<ProviderHeaders> {
    if base.is_none() && override_headers.is_none() {
        return None;
    }
    let mut merged = base.cloned().unwrap_or_default();
    for (name, value) in override_headers.into_iter().flatten() {
        let lower_name = name.to_lowercase();
        merged.retain(|existing, _| existing.to_lowercase() != lower_name);
        merged.insert(name.clone(), value.clone());
    }
    Some(merged)
}

/// `Date.now()` as a JS number, for comparison with OAuth expiries and
/// catalog timestamps.
#[allow(clippy::cast_precision_loss)] // Epoch milliseconds stay far below 2^53.
pub(crate) fn date_now() -> f64 {
    crate::utils::now_ms() as f64
}

/// Model headers as provider headers (every value present).
pub(crate) fn model_headers_as_provider_headers(
    headers: &IndexMap<String, String>,
) -> ProviderHeaders {
    headers
        .iter()
        .map(|(name, value)| (name.clone(), Some(value.clone())))
        .collect()
}

/// Runtime-checked narrowing for dynamically looked-up models. Non-chat
/// models never match, even when their api id equals `api`.
#[must_use]
pub fn has_api(model: &AnyModel, api: &str) -> bool {
    matches!(model, AnyModel::Chat(chat) if chat.api == api)
}

/// Computes `usage.cost` from the model's prices (request-wide tiers by
/// total input tokens), stores it in `usage`, and returns it. A 1h cache
/// write costs the input rate times the multiplier of the rulebook's
/// `cache_write_1h_prices` row of the model
/// ([`crate::quirks::cache_write_1h_multiplier`]), else the model's own
/// cache write rate.
#[allow(clippy::cast_precision_loss)] // Token counts are JS numbers: far below 2^53.
pub fn calculate_cost<M: CatalogModel>(model: &M, usage: &mut Usage) -> UsageCost {
    let cost = model.model_cost();
    let input_tokens = usage.input + usage.cache_read + usage.cache_write;
    let mut rates: ModelCostRates = cost.rates();
    // TS starts the matched threshold at -1, below every tier.
    let mut matched_threshold: Option<u64> = None;
    for tier in cost.tiers.iter().flatten() {
        if input_tokens > tier.input_tokens_above
            && matched_threshold.is_none_or(|matched| tier.input_tokens_above > matched)
        {
            rates = tier.rates();
            matched_threshold = Some(tier.input_tokens_above);
        }
    }

    let long_write_rate = match usage.cache_write_1h {
        None | Some(0) => rates.cache_write,
        Some(_) => crate::quirks::cache_write_1h_multiplier(model.model_id())
            .map_or(rates.cache_write, |multiplier| rates.input * multiplier),
    };
    let long_write = usage.cache_write_1h.unwrap_or(0) as f64;
    let short_write = usage.cache_write as f64 - long_write;
    usage.cost.input = (rates.input / 1_000_000.0) * usage.input as f64;
    usage.cost.output = (rates.output / 1_000_000.0) * usage.output as f64;
    usage.cost.cache_read = (rates.cache_read / 1_000_000.0) * usage.cache_read as f64;
    usage.cost.cache_write =
        (rates.cache_write * short_write + long_write_rate * long_write) / 1_000_000.0;
    usage.cost.total =
        usage.cost.input + usage.cost.output + usage.cost.cache_read + usage.cost.cache_write;
    usage.cost
}

/// Scales `usage.cost` by the price of the service tier `service_tier`
/// that served the request: the multiplier of the rulebook's
/// `service_tier_prices` row of `model` and the tier
/// ([`crate::quirks::service_tier_multiplier`]). With no row, the cost stays
/// as it is.
pub(crate) fn apply_service_tier_pricing(model: &Model, usage: &mut Usage, service_tier: &str) {
    let Some(multiplier) = crate::quirks::service_tier_multiplier(model.into(), service_tier)
    else {
        return;
    };
    usage.cost.input *= multiplier;
    usage.cost.output *= multiplier;
    usage.cost.cache_read *= multiplier;
    usage.cost.cache_write *= multiplier;
    usage.cost.total =
        usage.cost.input + usage.cost.output + usage.cost.cache_read + usage.cost.cache_write;
}

/// Whether two models are equal by type, id, and provider. `false` when
/// either is absent.
#[must_use]
pub fn models_are_equal(a: Option<&AnyModel>, b: Option<&AnyModel>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => {
            a.model_type() == b.model_type() && a.id() == b.id() && a.provider() == b.provider()
        }
        _ => false,
    }
}
