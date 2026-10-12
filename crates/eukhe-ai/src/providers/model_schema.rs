//! Port of pi-ai `src/providers/model-schema.ts`: model metadata `TypeBox` schemas.

use crate::typebox::{Options, TSchema, Type};

pub const THINKING_LEVELS: &[&str] = &["minimal", "low", "medium", "high", "xhigh", "max"];
pub const MODEL_THINKING_LEVELS: &[&str] =
    &["off", "minimal", "low", "medium", "high", "xhigh", "max"];

fn description(text: &str) -> Options {
    Options::new().set("description", text)
}

/// `ModelThinkingLevelSchema`.
#[must_use]
pub fn model_thinking_level_schema() -> TSchema {
    Type::enum_(MODEL_THINKING_LEVELS.iter().copied())
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
