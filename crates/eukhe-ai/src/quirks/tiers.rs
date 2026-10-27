//! The service tiers: the tiers that a provider
//! honors for a model, as the rulebook's `service_tiers` table.

use eukhe_types::ai::ServiceTier;
use serde::Deserialize;

use super::{shipped_family, ModelKey, Rulebook};

/// One entry of the table: the tiers that `provider` honors over the wire
/// API `api`, for every model, or only for the models of `family`.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct TierEntry {
    provider: String,
    api: String,
    #[serde(default)]
    pub(super) family: Option<String>,
    tiers: Vec<ServiceTier>,
}

/// The service tiers that the provider of `model` honors, in
/// [`ServiceTier::ALL`] order: `default` always, and each tier of each
/// entry of the shipped table whose provider and wire API are the model's
/// and whose family, when the entry names one, is the model's family. A
/// model that two families match names no family (the overlap is logged).
#[must_use]
pub fn service_tiers(model: ModelKey<'_>) -> Vec<ServiceTier> {
    let family = shipped_family(model.id, model.name);
    let entries: Vec<&TierEntry> = Rulebook::shipped()
        .service_tiers
        .iter()
        .filter(|entry| {
            entry.provider == model.provider
                && entry.api == model.api
                && entry
                    .family
                    .as_deref()
                    .is_none_or(|target| Some(target) == family)
        })
        .collect();
    ServiceTier::ALL
        .into_iter()
        .filter(|tier| {
            *tier == ServiceTier::Default || entries.iter().any(|entry| entry.tiers.contains(tier))
        })
        .collect()
}

/// Whether the provider of `model` honors `tier` ([`service_tiers`]).
#[must_use]
pub fn supports_service_tier(model: ModelKey<'_>, tier: ServiceTier) -> bool {
    service_tiers(model).contains(&tier)
}

#[cfg(test)]
mod tests {
    use eukhe_types::ai::ServiceTier::{self, Auto, Default, Flex, Priority, Scale};

    use super::{service_tiers, supports_service_tier};
    use crate::quirks::ModelKey;

    fn key<'a>(provider: &'a str, api: &'a str, id: &'a str) -> ModelKey<'a> {
        ModelKey {
            id,
            name: id,
            api,
            provider,
            base_url: "https://example.invalid/v1",
        }
    }

    /// The predicate that the rulebook's table replaced (a hardcoded list
    /// of model ids), kept here only as the oracle of
    /// [`the_table_keeps_every_answer_of_the_former_predicate`].
    fn former(provider: &str, api: &str, model_id: &str, tier: ServiceTier) -> bool {
        if tier == Default {
            return true;
        }
        if provider == "openrouter" && api == "openai-completions" {
            return matches!(tier, Flex | Priority);
        }
        let openai_responses = provider == "openai" && api == "openai-responses";
        let codex_responses = provider == "openai-codex" && api == "openai-codex-responses";
        if !openai_responses && !codex_responses {
            return false;
        }
        if matches!(tier, Auto | Scale) {
            return true;
        }
        let eligible_id = model_id == "gpt-5.4"
            || model_id == "gpt-5.5"
            || model_id == "gpt-5.6"
            || model_id == "gpt-6-astra"
            || model_id.starts_with("gpt-5.6-");
        if tier == Priority {
            return eligible_id;
        }
        tier == Flex && eligible_id && openai_responses
    }

    /// Every model of the compiled catalog and every tier: the rulebook's
    /// table answers as the former predicate did.
    #[test]
    fn the_table_keeps_every_answer_of_the_former_predicate() {
        let differences: Vec<(String, String, ServiceTier)> = crate::models_generated::MODELS
            .values()
            .flat_map(|models| models.values())
            .flat_map(|model| ServiceTier::ALL.map(|tier| (model, tier)))
            .filter(|(model, tier)| {
                former(&model.provider, &model.api, &model.id, *tier)
                    != supports_service_tier((*model).into(), *tier)
            })
            .map(|(model, tier)| (model.provider.clone(), model.id.clone(), tier))
            .collect();
        assert_eq!(differences, Vec::new());
    }

    /// The tiers of each kind of entry: provider and API; provider, API
    /// and family (flex only on the API-key backend); no entry.
    #[test]
    fn a_model_honors_the_tiers_of_its_provider_api_and_family() {
        assert_eq!(
            [
                key("openai", "openai-responses", "gpt-5.5"),
                key("openai", "openai-responses", "gpt-5.1"),
                key("openai-codex", "openai-codex-responses", "gpt-5.6-mini"),
                key("openai-codex", "openai-codex-responses", "gpt-6-astra"),
                key("openrouter", "openai-completions", "openai/qwen-4.9"),
                key(
                    "openrouter",
                    "anthropic-messages",
                    "anthropic/claude-fable-5"
                ),
                key("openai", "openai-completions", "gpt-5.5"),
                key("elpis-fast", "openai-completions", "qwen3.8-27b"),
            ]
            .map(service_tiers),
            [
                vec![Auto, Default, Flex, Scale, Priority],
                vec![Auto, Default, Scale],
                vec![Auto, Default, Scale, Priority],
                vec![Auto, Default, Scale, Priority],
                vec![Default, Flex, Priority],
                vec![Default],
                vec![Default],
                vec![Default],
            ]
        );
    }
}
