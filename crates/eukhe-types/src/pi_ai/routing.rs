//! Gateway routing preferences: `OpenRouter` provider routing and Vercel AI
//! Gateway routing. Field names are the upstream API's `snake_case` keys.

use serde::{Deserialize, Serialize};

use super::string_enum::string_enum;

string_enum! {
    /// `OpenRouter` data collection setting.
    pub enum DataCollection {
        Deny => "deny",
        Allow => "allow",
    }
}

/// Object form of [`OpenRouterSort`].
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct OpenRouterSortOptions {
    /// The sorting metric: "price", "throughput", "latency".
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub by: Option<String>,
    /// Partitioning strategy: "model" (default) or "none"; `Some(None)` is an explicit `null`.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        with = "super::nullable"
    )]
    pub partition: Option<Option<String>>,
}

/// `OpenRouter` sorting strategy: a metric name or an object with `by` and `partition`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum OpenRouterSort {
    Metric(String),
    Options(OpenRouterSortOptions),
}

/// TS `number | string` price.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum PriceValue {
    Number(#[serde(serialize_with = "super::js_number::serialize")] f64),
    String(String),
}

/// Maximum price per million tokens (USD).
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct OpenRouterMaxPrice {
    /// Price per million prompt tokens.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub prompt: Option<PriceValue>,
    /// Price per million completion tokens.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub completion: Option<PriceValue>,
    /// Price per image.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub image: Option<PriceValue>,
    /// Price per audio unit.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub audio: Option<PriceValue>,
    /// Price per request.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub request: Option<PriceValue>,
}

/// Percentile-specific cutoffs.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct OpenRouterPercentiles {
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "super::js_number::option::serialize"
    )]
    pub p50: Option<f64>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "super::js_number::option::serialize"
    )]
    pub p75: Option<f64>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "super::js_number::option::serialize"
    )]
    pub p90: Option<f64>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "super::js_number::option::serialize"
    )]
    pub p99: Option<f64>,
}

/// A number (applies to p50) or percentile-specific cutoffs.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum OpenRouterThreshold {
    Number(#[serde(serialize_with = "super::js_number::serialize")] f64),
    Percentiles(OpenRouterPercentiles),
}

/// `OpenRouter` provider routing preferences, sent as the `provider` request field.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct OpenRouterRouting {
    /// Whether to allow backup providers to serve requests. Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allow_fallbacks: Option<bool>,
    /// Whether to filter providers to those that support all request parameters. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub require_parameters: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub data_collection: Option<DataCollection>,
    /// Whether to restrict routing to ZDR (Zero Data Retention) endpoints.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub zdr: Option<bool>,
    /// Whether to restrict routing to models that allow text distillation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub enforce_distillable_text: Option<bool>,
    /// Provider slugs to try in sequence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub order: Option<Vec<String>>,
    /// Provider slugs to exclusively allow.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub only: Option<Vec<String>>,
    /// Provider slugs to skip.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ignore: Option<Vec<String>>,
    /// Quantization levels to filter providers by.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub quantizations: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sort: Option<OpenRouterSort>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_price: Option<OpenRouterMaxPrice>,
    /// Preferred minimum throughput (tokens/second).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub preferred_min_throughput: Option<OpenRouterThreshold>,
    /// Preferred maximum latency (seconds).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub preferred_max_latency: Option<OpenRouterThreshold>,
}

/// Vercel AI Gateway routing preferences.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct VercelGatewayRouting {
    /// Provider slugs to exclusively use.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub only: Option<Vec<String>>,
    /// Provider slugs to try in order.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub order: Option<Vec<String>>,
}
