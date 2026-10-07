//! Catalog entries: chat, image-generation, and classifier models.

use indexmap::IndexMap;
use serde::de::Error as _;
use serde::{Deserialize, Deserializer, Serialize};

use super::compat::ModelCompat;
use super::settings::{
    ModelPromptCache, SamplingParams, SamplingParamsByThinkingLevel, ThinkingLevelMap,
};
use super::string_enum::string_enum;
use super::{Api, ClassifierApi, ImageApi, JsonValue, ProviderId};

/// Per-million-token prices of one pricing tier (TS `ModelCostRates`).
#[derive(Debug, Clone, Copy, PartialEq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelCostRates {
    /// $/million tokens.
    #[serde(serialize_with = "super::js_number::serialize")]
    pub input: f64,
    /// $/million tokens.
    #[serde(serialize_with = "super::js_number::serialize")]
    pub output: f64,
    /// $/million tokens.
    #[serde(serialize_with = "super::js_number::serialize")]
    pub cache_read: f64,
    /// $/million tokens.
    #[serde(serialize_with = "super::js_number::serialize")]
    pub cache_write: f64,
}

/// A request-wide pricing tier.
#[derive(Debug, Clone, Copy, PartialEq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelCostTier {
    #[serde(serialize_with = "super::js_number::serialize")]
    pub input: f64,
    #[serde(serialize_with = "super::js_number::serialize")]
    pub output: f64,
    #[serde(serialize_with = "super::js_number::serialize")]
    pub cache_read: f64,
    #[serde(serialize_with = "super::js_number::serialize")]
    pub cache_write: f64,
    /// Use this tier for requests whose total input usage exceeds this token count.
    pub input_tokens_above: u64,
}

impl ModelCostTier {
    /// The tier's rates.
    #[must_use]
    pub const fn rates(&self) -> ModelCostRates {
        ModelCostRates {
            input: self.input,
            output: self.output,
            cache_read: self.cache_read,
            cache_write: self.cache_write,
        }
    }
}

/// A model's prices.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelCost {
    #[serde(serialize_with = "super::js_number::serialize")]
    pub input: f64,
    #[serde(serialize_with = "super::js_number::serialize")]
    pub output: f64,
    #[serde(serialize_with = "super::js_number::serialize")]
    pub cache_read: f64,
    #[serde(serialize_with = "super::js_number::serialize")]
    pub cache_write: f64,
    /// Request-wide pricing tiers. The highest matching input threshold applies to the full request.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tiers: Option<Vec<ModelCostTier>>,
}

impl ModelCost {
    /// The base rates.
    #[must_use]
    pub const fn rates(&self) -> ModelCostRates {
        ModelCostRates {
            input: self.input,
            output: self.output,
            cache_read: self.cache_read,
            cache_write: self.cache_write,
        }
    }
}

/// Cache-safe image resize profile.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelImageResizeOptions {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_width: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_height: Option<u64>,
    /// Maximum base64-encoded payload size in bytes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_bytes: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub jpeg_quality: Option<u64>,
}

/// Image input limits.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelImageInputLimits {
    /// Cache-safe resize profile applied before a new image enters conversation history.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub resize: Option<ModelImageResizeOptions>,
    /// Maximum images accepted in one provider message.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_per_message: Option<u64>,
    /// Maximum images accepted across one provider request.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_per_request: Option<u64>,
}

/// Provider input limits.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelInputLimits {
    /// Maximum serialized provider request size in bytes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_request_bytes: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub images: Option<ModelImageInputLimits>,
}

string_enum! {
    /// An input or output modality.
    pub enum Modality {
        Text => "text",
        Image => "image",
    }
}

string_enum! {
    /// The optional `type` of a chat model.
    pub enum ChatModelType {
        Chat => "chat",
    }
}

string_enum! {
    /// What a catalog entry is for. Decides which `Models` operation accepts it.
    pub enum ModelType {
        Chat => "chat",
        Image => "image",
        Classifier => "classifier",
    }
}

/// Chat model: usable with `stream()` and friends.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", try_from = "ModelWire")]
pub struct Model {
    pub id: String,
    pub name: String,
    pub api: Api,
    pub provider: ProviderId,
    pub base_url: String,
    pub input: Vec<Modality>,
    /// Provider input limits and cache-safe preprocessing metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input_limits: Option<ModelInputLimits>,
    pub cost: ModelCost,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub headers: Option<IndexMap<String, String>>,
    /// Chat is the default model type, so models without `type` are chat models.
    #[serde(rename = "type", default, skip_serializing_if = "Option::is_none")]
    pub model_type: Option<ChatModelType>,
    pub reasoning: bool,
    /// Maps pi thinking levels to provider/model-specific values. Missing keys
    /// use provider defaults; `None` marks a level unsupported.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thinking_level_map: Option<ThinkingLevelMap>,
    /// Prompt cache lifetimes per retention tier. Unset when unknown.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub prompt_cache: Option<ModelPromptCache>,
    pub context_window: u64,
    pub max_tokens: u64,
    /// Default sampling parameters for this model; per-request keys override these.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sampling_params: Option<SamplingParams>,
    /// Sampling parameter overrides selected by the effective pi thinking level.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sampling_params_by_thinking_level: Option<SamplingParamsByThinkingLevel>,
    /// Compatibility overrides. If not set, auto-detected from `base_url`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub compat: Option<ModelCompat>,
    /// eukhe addition: the Prime Inference model picker's featured flag.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub featured: Option<bool>,
}

/// Deserialization mirror of [`Model`]: `compat` is parsed once `api` is known.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ModelWire {
    id: String,
    name: String,
    api: Api,
    provider: ProviderId,
    base_url: String,
    input: Vec<Modality>,
    #[serde(default)]
    input_limits: Option<ModelInputLimits>,
    cost: ModelCost,
    #[serde(default)]
    headers: Option<IndexMap<String, String>>,
    #[serde(rename = "type", default)]
    model_type: Option<ChatModelType>,
    reasoning: bool,
    #[serde(default)]
    thinking_level_map: Option<ThinkingLevelMap>,
    #[serde(default)]
    prompt_cache: Option<ModelPromptCache>,
    context_window: u64,
    max_tokens: u64,
    #[serde(default)]
    sampling_params: Option<SamplingParams>,
    #[serde(default)]
    sampling_params_by_thinking_level: Option<SamplingParamsByThinkingLevel>,
    #[serde(default)]
    compat: Option<JsonValue>,
    #[serde(default)]
    featured: Option<bool>,
}

impl TryFrom<ModelWire> for Model {
    type Error = serde_json::Error;

    fn try_from(wire: ModelWire) -> Result<Self, Self::Error> {
        let compat = wire
            .compat
            .map(|value| ModelCompat::from_json(&wire.api, value))
            .transpose()?;
        Ok(Self {
            id: wire.id,
            name: wire.name,
            api: wire.api,
            provider: wire.provider,
            base_url: wire.base_url,
            input: wire.input,
            input_limits: wire.input_limits,
            cost: wire.cost,
            headers: wire.headers,
            model_type: wire.model_type,
            reasoning: wire.reasoning,
            thinking_level_map: wire.thinking_level_map,
            prompt_cache: wire.prompt_cache,
            context_window: wire.context_window,
            max_tokens: wire.max_tokens,
            sampling_params: wire.sampling_params,
            sampling_params_by_thinking_level: wire.sampling_params_by_thinking_level,
            compat,
            featured: wire.featured,
        })
    }
}

/// Image-generation model (`type: "image"`): usable with `generateImages()` only.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type", rename = "image", rename_all = "camelCase")]
pub struct ImageModel {
    pub id: String,
    pub name: String,
    pub api: ImageApi,
    pub provider: ProviderId,
    pub base_url: String,
    pub input: Vec<Modality>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input_limits: Option<ModelInputLimits>,
    pub cost: ModelCost,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub headers: Option<IndexMap<String, String>>,
    /// Output modalities. Always includes `image`; `text` means the model can also return text blocks.
    pub output: Vec<Modality>,
}

/// Structured classifier model (`type: "classifier"`): usable with `classify()` only.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type", rename = "classifier", rename_all = "camelCase")]
pub struct ClassifierModel {
    pub id: String,
    pub name: String,
    pub api: ClassifierApi,
    pub provider: ProviderId,
    pub base_url: String,
    pub input: Vec<Modality>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input_limits: Option<ModelInputLimits>,
    pub cost: ModelCost,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub headers: Option<IndexMap<String, String>>,
    pub context_window: u64,
}

/// Anything a provider can list (TS `AnyModel`). Narrow with `isModelType()`.
///
/// Serialized untagged (each model carries its `type`); deserialized by
/// `type`, where an absent or `null` type is a chat model.
// Mirrors the TS `AnyModel` union by value; chat models dominate catalogs.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(untagged)]
pub enum AnyModel {
    Chat(Model),
    Image(ImageModel),
    Classifier(ClassifierModel),
}

impl<'de> Deserialize<'de> for AnyModel {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = JsonValue::deserialize(deserializer)?;
        let model_type = match value.get("type") {
            None | Some(JsonValue::Null) => ModelType::Chat,
            Some(JsonValue::String(name)) => ModelType::parse(name)
                .ok_or_else(|| D::Error::custom(format!("unknown model type {name:?}")))?,
            Some(other) => return Err(D::Error::custom(format!("invalid model type {other}"))),
        };
        match model_type {
            ModelType::Chat => serde_json::from_value(value).map(Self::Chat),
            ModelType::Image => serde_json::from_value(value).map(Self::Image),
            ModelType::Classifier => serde_json::from_value(value).map(Self::Classifier),
        }
        .map_err(D::Error::custom)
    }
}

impl AnyModel {
    /// The model's [`ModelType`].
    #[must_use]
    pub const fn model_type(&self) -> ModelType {
        match self {
            Self::Chat(_) => ModelType::Chat,
            Self::Image(_) => ModelType::Image,
            Self::Classifier(_) => ModelType::Classifier,
        }
    }

    #[must_use]
    pub fn id(&self) -> &str {
        match self {
            Self::Chat(model) => &model.id,
            Self::Image(model) => &model.id,
            Self::Classifier(model) => &model.id,
        }
    }

    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::Chat(model) => &model.name,
            Self::Image(model) => &model.name,
            Self::Classifier(model) => &model.name,
        }
    }

    #[must_use]
    pub fn api(&self) -> &str {
        match self {
            Self::Chat(model) => &model.api,
            Self::Image(model) => &model.api,
            Self::Classifier(model) => &model.api,
        }
    }

    #[must_use]
    pub fn provider(&self) -> &str {
        match self {
            Self::Chat(model) => &model.provider,
            Self::Image(model) => &model.provider,
            Self::Classifier(model) => &model.provider,
        }
    }

    #[must_use]
    pub fn base_url(&self) -> &str {
        match self {
            Self::Chat(model) => &model.base_url,
            Self::Image(model) => &model.base_url,
            Self::Classifier(model) => &model.base_url,
        }
    }

    /// Replace the base URL.
    pub fn set_base_url(&mut self, base_url: String) {
        match self {
            Self::Chat(model) => model.base_url = base_url,
            Self::Image(model) => model.base_url = base_url,
            Self::Classifier(model) => model.base_url = base_url,
        }
    }

    #[must_use]
    pub fn input(&self) -> &[Modality] {
        match self {
            Self::Chat(model) => &model.input,
            Self::Image(model) => &model.input,
            Self::Classifier(model) => &model.input,
        }
    }

    #[must_use]
    pub const fn input_limits(&self) -> Option<&ModelInputLimits> {
        match self {
            Self::Chat(model) => model.input_limits.as_ref(),
            Self::Image(model) => model.input_limits.as_ref(),
            Self::Classifier(model) => model.input_limits.as_ref(),
        }
    }

    #[must_use]
    pub const fn cost(&self) -> &ModelCost {
        match self {
            Self::Chat(model) => &model.cost,
            Self::Image(model) => &model.cost,
            Self::Classifier(model) => &model.cost,
        }
    }

    #[must_use]
    pub const fn headers(&self) -> Option<&IndexMap<String, String>> {
        match self {
            Self::Chat(model) => model.headers.as_ref(),
            Self::Image(model) => model.headers.as_ref(),
            Self::Classifier(model) => model.headers.as_ref(),
        }
    }
}

impl From<Model> for AnyModel {
    fn from(model: Model) -> Self {
        Self::Chat(model)
    }
}

impl From<ImageModel> for AnyModel {
    fn from(model: ImageModel) -> Self {
        Self::Image(model)
    }
}

impl From<ClassifierModel> for AnyModel {
    fn from(model: ClassifierModel) -> Self {
        Self::Classifier(model)
    }
}
