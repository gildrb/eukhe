//! Port of pi-ai `src/providers/model-schema.ts`: model metadata `TypeBox` schemas.

use crate::typebox::{Options, TSchema, Type};

pub const THINKING_LEVELS: &[&str] = &["minimal", "low", "medium", "high", "xhigh", "max"];
pub const MODEL_THINKING_LEVELS: &[&str] =
    &["off", "minimal", "low", "medium", "high", "xhigh", "max"];
pub const MODEL_INPUT_MODALITIES: &[&str] = &["text", "image"];
pub const CACHE_RETENTIONS: &[&str] = &["none", "short", "long"];
pub const MODEL_PROMPT_CACHE_RETENTIONS: &[&str] = &["short", "long"];

fn description(text: &str) -> Options {
    Options::new().set("description", text)
}

/// `ThinkingLevelSchema`.
#[must_use]
pub fn thinking_level_schema() -> TSchema {
    Type::enum_(THINKING_LEVELS.iter().copied())
}

/// `ModelThinkingLevelSchema`.
#[must_use]
pub fn model_thinking_level_schema() -> TSchema {
    Type::enum_(MODEL_THINKING_LEVELS.iter().copied())
}

/// `ModelInputModalitySchema`.
#[must_use]
pub fn model_input_modality_schema() -> TSchema {
    Type::enum_(MODEL_INPUT_MODALITIES.iter().copied())
}

/// `CacheRetentionSchema`.
#[must_use]
pub fn cache_retention_schema() -> TSchema {
    Type::enum_(CACHE_RETENTIONS.iter().copied())
}

/// `ThinkingLevelMapValueSchema`.
fn thinking_level_map_value_schema() -> TSchema {
    Type::union([Type::string(), Type::null()])
}

/// `ThinkingLevelMapSchema`.
#[must_use]
pub fn thinking_level_map_schema() -> TSchema {
    Type::partial(Type::record(
        model_thinking_level_schema(),
        thinking_level_map_value_schema(),
    ))
}

/// `ModelPromptCacheSchema`.
#[must_use]
pub fn model_prompt_cache_schema() -> TSchema {
    Type::partial_with(
        Type::record(
            Type::enum_(MODEL_PROMPT_CACHE_RETENTIONS.iter().copied()),
            Type::number_with(Options::new().set("exclusiveMinimum", 0)),
        ),
        description(
            "Best-effort prompt cache lifetime in seconds for each retention tier. A missing tier means the lifetime is unknown, so Pi does not warm it.",
        ),
    )
}

/// `ModelCostRatesProperties`.
fn model_cost_rates_properties() -> Vec<(&'static str, TSchema)> {
    vec![
        (
            "input",
            Type::number_with(description("Input cost in USD per million tokens.")),
        ),
        (
            "output",
            Type::number_with(description("Output cost in USD per million tokens.")),
        ),
        (
            "cacheRead",
            Type::number_with(description("Cache-read cost in USD per million tokens.")),
        ),
        (
            "cacheWrite",
            Type::number_with(description("Cache-write cost in USD per million tokens.")),
        ),
    ]
}

/// `ModelCostRatesSchema`.
#[must_use]
pub fn model_cost_rates_schema() -> TSchema {
    Type::object(model_cost_rates_properties())
}

/// `ModelCostTierSchema`.
#[must_use]
pub fn model_cost_tier_schema() -> TSchema {
    let mut properties = vec![(
        "inputTokensAbove",
        Type::number_with(description(
            "Use this tier when total request input exceeds this token count.",
        )),
    )];
    properties.extend(model_cost_rates_properties());
    Type::object(properties)
}

/// `ModelCostSchema`.
#[must_use]
pub fn model_cost_schema() -> TSchema {
    let mut properties = model_cost_rates_properties();
    properties.push((
        "tiers",
        Type::optional(Type::array_with(
            model_cost_tier_schema(),
            description(
                "Request-wide pricing tiers. The highest matching input threshold applies to the full request.",
            ),
        )),
    ));
    Type::object(properties)
}

/// `modelImageResizeOptions(options)`.
fn model_image_resize_options(options: Options) -> TSchema {
    Type::object_with(
        [
            (
                "maxWidth",
                Type::optional(Type::integer_with(Options::new().set("minimum", 1))),
            ),
            (
                "maxHeight",
                Type::optional(Type::integer_with(Options::new().set("minimum", 1))),
            ),
            (
                "maxBytes",
                Type::optional(Type::integer_with(Options::new().set("minimum", 1).set(
                    "description",
                    "Maximum base64-encoded payload size in bytes.",
                ))),
            ),
            (
                "jpegQuality",
                Type::optional(Type::integer_with(
                    Options::new().set("minimum", 1).set("maximum", 100),
                )),
            ),
        ],
        options,
    )
}

/// `ModelImageResizeOptionsSchema`.
#[must_use]
pub fn model_image_resize_options_schema() -> TSchema {
    model_image_resize_options(Options::new())
}

/// `ModelImageInputLimitsSchema`.
#[must_use]
pub fn model_image_input_limits_schema() -> TSchema {
    Type::object([
        (
            "resize",
            Type::optional(model_image_resize_options(description(
                "Cache-safe resize profile applied before a new image enters conversation history.",
            ))),
        ),
        (
            "maxPerMessage",
            Type::optional(Type::integer_with(Options::new().set("minimum", 1).set(
                "description",
                "Maximum images accepted in one provider message.",
            ))),
        ),
        (
            "maxPerRequest",
            Type::optional(Type::integer_with(Options::new().set("minimum", 1).set(
                "description",
                "Maximum images accepted across one provider request.",
            ))),
        ),
    ])
}

/// `ModelInputLimitsSchema`.
#[must_use]
pub fn model_input_limits_schema() -> TSchema {
    Type::object([
        (
            "maxRequestBytes",
            Type::optional(Type::integer_with(Options::new().set("minimum", 1).set(
                "description",
                "Maximum serialized provider request size in bytes.",
            ))),
        ),
        ("images", Type::optional(model_image_input_limits_schema())),
    ])
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn thinking_level_map_has_no_required_levels() {
        let schema = thinking_level_map_schema();
        assert!(schema.json().get("required").is_none());
        assert_eq!(
            schema.json()["properties"]["off"],
            json!({ "anyOf": [{ "type": "string" }, { "type": "null" }] })
        );
    }

    #[test]
    fn model_cost_tier_puts_threshold_first() {
        let schema = model_cost_tier_schema();
        assert_eq!(
            schema.json()["required"],
            json!([
                "inputTokensAbove",
                "input",
                "output",
                "cacheRead",
                "cacheWrite"
            ])
        );
    }
}
