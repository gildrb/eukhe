//! The conversion of a pi-ai catalog model ([`eukhe_types::pi_ai::Model`],
//! the `eukhe-ai` compiled catalog's entry) into the registry's
//! [`Model`] (`eukhe_types::ai::Model`).
//!
//! Every field the registry model has carries over unchanged. The pi-ai
//! fields the registry model has no slot for drop: the request-wide
//! pricing tiers (`cost.tiers`), the input limits, the prompt-cache
//! lifetimes, the chat `type` tag, and the sampling parameters (the pi-ai
//! request path reads them from its own catalog). The registry-only
//! `maxTokensExplicit` flag stays unset: a compiled entry is catalog data,
//! never explicit configuration.

use std::collections::BTreeMap;

use eukhe_types::ai::{ModelCompat, ModelCost, ModelInput, ModelThinkingLevel, ThinkingLevelMap};
use eukhe_types::pi_ai;

use crate::Model;

/// Why a pi-ai model has no registry form.
#[derive(Debug)]
pub enum ConversionError {
    /// The compatibility block did not serialize to a JSON object.
    Compat { model: String, detail: String },
}

impl std::fmt::Display for ConversionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConversionError::Compat { model, detail } => write!(
                formatter,
                "the compat block of {model} has no registry form: {detail}"
            ),
        }
    }
}

impl std::error::Error for ConversionError {}

/// The registry form of one pi-ai catalog model.
///
/// # Errors
///
/// Returns [`ConversionError::Compat`] when the compatibility block does
/// not serialize to a JSON object (the registry keeps it as the raw map).
pub fn registry_model(model: &pi_ai::Model) -> Result<Model, ConversionError> {
    Ok(Model {
        id: model.id.clone(),
        name: model.name.clone(),
        api: model.api.clone(),
        provider: model.provider.clone(),
        base_url: model.base_url.clone(),
        reasoning: model.reasoning,
        thinking_level_map: model.thinking_level_map.as_ref().map(thinking_level_map),
        input: model
            .input
            .iter()
            .map(|modality| model_input(*modality))
            .collect(),
        cost: ModelCost {
            input: model.cost.input.into(),
            output: model.cost.output.into(),
            cache_read: model.cost.cache_read.into(),
            cache_write: model.cost.cache_write.into(),
        },
        context_window: model.context_window,
        max_tokens: model.max_tokens,
        max_tokens_explicit: false,
        featured: model.featured,
        headers: model.headers.as_ref().map(|headers| {
            headers
                .iter()
                .map(|(name, value)| (name.clone(), value.clone()))
                .collect::<BTreeMap<_, _>>()
        }),
        compat: model
            .compat
            .as_ref()
            .map(|compat| registry_compat(&model.id, compat))
            .transpose()?,
    })
}

fn model_input(modality: pi_ai::Modality) -> ModelInput {
    match modality {
        pi_ai::Modality::Text => ModelInput::Text,
        pi_ai::Modality::Image => ModelInput::Image,
    }
}

fn thinking_level(level: pi_ai::ModelThinkingLevel) -> ModelThinkingLevel {
    match level {
        pi_ai::ModelThinkingLevel::Off => ModelThinkingLevel::Off,
        pi_ai::ModelThinkingLevel::Minimal => ModelThinkingLevel::Minimal,
        pi_ai::ModelThinkingLevel::Low => ModelThinkingLevel::Low,
        pi_ai::ModelThinkingLevel::Medium => ModelThinkingLevel::Medium,
        pi_ai::ModelThinkingLevel::High => ModelThinkingLevel::High,
        pi_ai::ModelThinkingLevel::Xhigh => ModelThinkingLevel::Xhigh,
        pi_ai::ModelThinkingLevel::Max => ModelThinkingLevel::Max,
    }
}

fn thinking_level_map(map: &pi_ai::ThinkingLevelMap) -> ThinkingLevelMap {
    map.iter()
        .map(|(level, value)| (thinking_level(*level), value.clone()))
        .collect()
}

/// The registry keeps the compat block as its raw JSON map (both forms
/// share the TS wire shape).
fn registry_compat(id: &str, compat: &pi_ai::ModelCompat) -> Result<ModelCompat, ConversionError> {
    match serde_json::to_value(compat) {
        Ok(serde_json::Value::Object(raw)) => Ok(ModelCompat { raw }),
        Ok(other) => Err(ConversionError::Compat {
            model: id.to_string(),
            detail: format!("expected an object, got {other}"),
        }),
        Err(error) => Err(ConversionError::Compat {
            model: id.to_string(),
            detail: error.to_string(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pi_model(value: serde_json::Value) -> pi_ai::Model {
        serde_json::from_value(value).expect("a pi-ai model")
    }

    #[test]
    fn every_shared_field_carries_over() {
        let source = pi_model(serde_json::json!({
            "id": "m-1",
            "name": "Model One",
            "api": "openai-completions",
            "provider": "prov",
            "baseUrl": "https://prov.example/v1",
            "reasoning": true,
            "thinkingLevelMap": {"off": null, "high": "high", "minimal": "low"},
            "input": ["text", "image"],
            "cost": {
                "input": 1.25,
                "output": 10,
                "cacheRead": 0.125,
                "cacheWrite": 0,
                "tiers": [{"input": 2.5, "output": 15, "cacheRead": 0.25, "cacheWrite": 0, "inputTokensAbove": 200_000}]
            },
            "contextWindow": 400_000,
            "maxTokens": 128_000,
            "featured": true,
            "headers": {"X-Title": "eukhe", "A-First": "1"},
            "compat": {"supportsDeveloperRole": false, "maxTokensField": "max_tokens"},
            "promptCache": {"short": 300}
        }));
        let converted = registry_model(&source).expect("converts");
        let expected: Model = serde_json::from_value(serde_json::json!({
            "id": "m-1",
            "name": "Model One",
            "api": "openai-completions",
            "provider": "prov",
            "baseUrl": "https://prov.example/v1",
            "reasoning": true,
            "thinkingLevelMap": {"off": null, "minimal": "low", "high": "high"},
            "input": ["text", "image"],
            "cost": {"input": 1.25, "output": 10, "cacheRead": 0.125, "cacheWrite": 0},
            "contextWindow": 400_000,
            "maxTokens": 128_000,
            "featured": true,
            "headers": {"A-First": "1", "X-Title": "eukhe"},
            "compat": {"supportsDeveloperRole": false, "maxTokensField": "max_tokens"}
        }))
        .expect("a registry model");
        assert_eq!(converted, expected);
        assert!(!converted.max_tokens_explicit);
    }

    #[test]
    fn absent_optional_fields_stay_absent() {
        let source = pi_model(serde_json::json!({
            "id": "bare",
            "name": "Bare",
            "api": "anthropic-messages",
            "provider": "anthropic",
            "baseUrl": "https://api.anthropic.com",
            "reasoning": false,
            "input": ["text"],
            "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0},
            "contextWindow": 1,
            "maxTokens": 1
        }));
        let converted = registry_model(&source).expect("converts");
        assert_eq!(converted.thinking_level_map, None);
        assert_eq!(converted.headers, None);
        assert_eq!(converted.compat, None);
        assert_eq!(converted.featured, None);
        assert_eq!(converted.input, vec![ModelInput::Text]);
    }
}
