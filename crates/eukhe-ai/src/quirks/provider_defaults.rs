//! The default model of each provider, as the rulebook's `provider_defaults`
//! table (provider id → model id): the model that the startup chain picks
//! for a provider when the settings name no model of it, and the template of
//! a fallback model. A provider that the table does not name has no default.

use std::collections::BTreeMap;

use super::Rulebook;

/// The `provider_defaults` table: one model id per provider id.
pub(super) type ProviderDefaults = BTreeMap<String, String>;

/// The default model id of `provider` in the shipped rulebook; `None` when
/// the table does not name the provider.
#[must_use]
pub fn provider_default_model(provider: &str) -> Option<&'static str> {
    Rulebook::shipped()
        .provider_defaults
        .get(provider)
        .map(String::as_str)
}

/// Every `(provider id, model id)` pair of the shipped table, in provider
/// id order.
pub fn provider_defaults() -> impl Iterator<Item = (&'static str, &'static str)> {
    Rulebook::shipped()
        .provider_defaults
        .iter()
        .map(|(provider, model)| (provider.as_str(), model.as_str()))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{provider_default_model, provider_defaults};
    use crate::providers::prime_inference::PRIME_INFERENCE_PROVIDER_ID;

    /// The table that the rulebook replaced (a match over provider ids),
    /// kept here only as the oracle of
    /// [`the_table_keeps_every_answer_of_the_former_function`].
    fn former(provider: &str) -> Option<&'static str> {
        Some(match provider {
            "amazon-bedrock" => "us.anthropic.claude-opus-4-6-v1",
            "anthropic" => "claude-opus-4-7",
            "openai" | "azure-openai-responses" | "github-copilot" => "gpt-5.4",
            "openai-codex" => "gpt-5.5",
            "prime-inference" => "z-ai/glm-5.3",
            "deepseek" => "deepseek-v4-pro",
            "google" | "google-vertex" => "gemini-3.1-pro-preview",
            "openrouter" => "moonshotai/kimi-k2.6",
            "vercel-ai-gateway" => "zai/glm-5.1",
            "xai" => "grok-4.20-0309-reasoning",
            "groq" => "openai/gpt-oss-120b",
            "cerebras" => "gpt-oss-120b",
            "zai" => "glm-5.3",
            "mistral" => "devstral-medium-latest",
            "minimax" | "minimax-cn" => "MiniMax-M2.7",
            "moonshotai" | "moonshotai-cn" | "opencode" | "opencode-go" => "kimi-k2.6",
            "huggingface" => "moonshotai/Kimi-K2.6",
            "fireworks" => "accounts/fireworks/models/kimi-k2p6",
            "kimi-coding" => "kimi-for-coding",
            "cloudflare-workers-ai" => "@cf/moonshotai/kimi-k2.6",
            "cloudflare-ai-gateway" => "claude-sonnet-4.5",
            "xiaomi"
            | "xiaomi-token-plan-cn"
            | "xiaomi-token-plan-ams"
            | "xiaomi-token-plan-sgp" => "mimo-v2.5-pro",
            _ => return None,
        })
    }

    /// Every provider of the compiled catalog, Prime Inference and every
    /// provider of the table: the table answers as the former function
    /// did.
    #[test]
    fn the_table_keeps_every_answer_of_the_former_function() {
        let providers: BTreeSet<&str> = crate::models_generated::MODELS
            .keys()
            .copied()
            .chain([PRIME_INFERENCE_PROVIDER_ID])
            .chain(provider_defaults().map(|(provider, _)| provider))
            .collect();
        let differences: Vec<(&str, Option<&str>, Option<&str>)> = providers
            .into_iter()
            .map(|provider| (provider, former(provider), provider_default_model(provider)))
            .filter(|(_, former, table)| former != table)
            .collect();
        assert_eq!(differences, Vec::new());
    }
}
