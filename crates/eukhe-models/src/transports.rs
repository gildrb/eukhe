//! The compiled transport table.
//!
//! The compiled model catalog (`eukhe_ai::models_generated::MODELS`, the
//! pi-ai port of the TS `models.generated.ts`, plus the
//! `eukhe_ai::providers::prime_inference_models` entries) is the
//! hand-maintained table of transports the client implements: the
//! `(provider, api, baseUrl)` tuples of the public providers, plus the
//! offline Prime Inference entries (one transport tuple of their own). It
//! only changes with a client release — the catalog can select among these
//! transports but never introduce one.

use std::collections::HashSet;
use std::sync::LazyLock;

use eukhe_ai::models_generated::MODELS;
use eukhe_ai::providers::prime_inference_models::PRIME_INFERENCE_MODELS;

use crate::pi_ai_model::registry_model;
use crate::Model;

/// The compiled catalog, shared as one immutable list (the TS
/// `installedModels`): every built-in provider's pi-ai models in provider
/// order, then the Prime Inference entries, in the registry's model form.
///
/// # Panics
///
/// Panics when a compiled pi-ai entry has no registry form (a compat
/// block that is not a JSON object); the compiled table is static data
/// and this crate's tests convert every entry.
#[must_use]
pub fn compiled_models() -> &'static [Model] {
    static COMPILED: LazyLock<Vec<Model>> = LazyLock::new(|| {
        let mut models: Vec<Model> = MODELS
            .values()
            .flat_map(|catalog| catalog.values())
            .chain(PRIME_INFERENCE_MODELS.values())
            .map(|model| {
                registry_model(model)
                    .unwrap_or_else(|error| panic!("the compiled pi-ai catalog converts: {error}"))
            })
            .collect();
        models.shrink_to_fit();
        models
    });
    &COMPILED
}

/// The transports the client implements that the pi-ai compiled catalog
/// carries no entry for: the `(provider, api, baseUrl)` tuples the eukhe
/// model catalog (`catalog.v1.json`) selects outside pi-ai's own provider
/// tables. Template-less (no request headers): pinning keeps the catalog's
/// entries on these transports, and the catalog still cannot introduce
/// any other.
pub const SUPPLEMENTAL_TRANSPORTS: [(&str, &str, &str); 8] = [
    (
        "amazon-bedrock",
        "bedrock-converse-stream",
        "https://bedrock-runtime.ap-northeast-1.amazonaws.com",
    ),
    (
        "amazon-bedrock",
        "bedrock-converse-stream",
        "https://bedrock-runtime.ap-southeast-2.amazonaws.com",
    ),
    ("azure-openai-responses", "azure-openai-responses", ""),
    ("xai", "openai-completions", "https://api.x.ai/v1"),
    (
        "xiaomi",
        "anthropic-messages",
        "https://api.xiaomimimo.com/anthropic",
    ),
    (
        "xiaomi-token-plan-ams",
        "anthropic-messages",
        "https://token-plan-ams.xiaomimimo.com/anthropic",
    ),
    (
        "xiaomi-token-plan-cn",
        "anthropic-messages",
        "https://token-plan-cn.xiaomimimo.com/anthropic",
    ),
    (
        "xiaomi-token-plan-sgp",
        "anthropic-messages",
        "https://token-plan-sgp.xiaomimimo.com/anthropic",
    ),
];

/// Distinct compiled `(provider, api, baseUrl)` tuples: the compiled
/// catalog's, then [`SUPPLEMENTAL_TRANSPORTS`] (Prime Inference excluded —
/// its entries ship as their own compiled section).
#[must_use]
pub fn compiled_transport_tuples() -> Vec<(&'static str, &'static str, &'static str)> {
    let mut tuples: Vec<(&'static str, &'static str, &'static str)> = Vec::new();
    let mut seen: HashSet<(&str, &str, &str)> = HashSet::new();
    let compiled = compiled_models()
        .iter()
        .filter(|model| model.provider != "prime-inference")
        .map(|model| {
            (
                model.provider.as_str(),
                model.api.as_str(),
                model.base_url.as_str(),
            )
        });
    for tuple in compiled.chain(SUPPLEMENTAL_TRANSPORTS) {
        if seen.insert(tuple) {
            tuples.push(tuple);
        }
    }
    tuples
}

/// The provider ids the client compiles in: every compiled catalog
/// provider (Prime Inference included) and the supplemental transports'
/// providers.
#[must_use]
pub fn compiled_provider_ids() -> std::collections::BTreeSet<&'static str> {
    compiled_models()
        .iter()
        .map(|model| model.provider.as_str())
        .chain(
            SUPPLEMENTAL_TRANSPORTS
                .iter()
                .map(|(provider, _, _)| *provider),
        )
        .collect()
}

/// The compiled Prime Inference entries (joined into every resolved
/// catalog). Private ids (internal/, dev/, ids containing `:`) never ship
/// compiled.
#[must_use]
pub fn prime_inference_offline_entries() -> Vec<Model> {
    compiled_models()
        .iter()
        .filter(|model| {
            model.provider == "prime-inference"
                && !eukhe_ai::providers::prime_inference::is_private_prime_inference_model_id(
                    &model.id,
                )
        })
        .cloned()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_compiled_catalog_converts_every_pi_ai_entry() {
        let pi_ai_entries: usize = MODELS.values().map(|catalog| catalog.len()).sum::<usize>()
            + PRIME_INFERENCE_MODELS.len();
        assert_eq!(compiled_models().len(), pi_ai_entries);
        assert!(compiled_models()
            .iter()
            .any(|model| model.provider == "prime-inference"));
        assert_eq!(
            prime_inference_offline_entries().len(),
            PRIME_INFERENCE_MODELS
                .keys()
                .filter(|id| {
                    !eukhe_ai::providers::prime_inference::is_private_prime_inference_model_id(id)
                })
                .count()
        );
    }

    /// The supplement carries only transports the pi-ai table lacks: a
    /// tuple pi-ai gains drops from the supplement.
    #[test]
    fn the_supplement_only_adds_missing_transports() {
        let compiled: HashSet<(&str, &str, &str)> = compiled_models()
            .iter()
            .map(|model| {
                (
                    model.provider.as_str(),
                    model.api.as_str(),
                    model.base_url.as_str(),
                )
            })
            .collect();
        for tuple in SUPPLEMENTAL_TRANSPORTS {
            assert!(!compiled.contains(&tuple), "{tuple:?} is compiled already");
        }
        let tuples = compiled_transport_tuples();
        let providers = compiled_provider_ids();
        for tuple in SUPPLEMENTAL_TRANSPORTS {
            assert!(tuples.contains(&tuple), "{tuple:?}");
            assert!(providers.contains(tuple.0), "{tuple:?}");
        }
        assert!(providers.contains("prime-inference"));
    }

    /// The tier eligibility the compat facts give every compiled row: the
    /// hosts that offer tiers for every model take those, a Responses host
    /// adds the tiers the row prices, and every other host takes only
    /// `default`.
    #[test]
    fn compiled_rows_keep_their_service_tier_eligibility() {
        use eukhe_types::ai::{supports_service_tier, ServiceTier};
        let eligible = |model: &Model| -> Vec<ServiceTier> {
            [
                ServiceTier::Auto,
                ServiceTier::Flex,
                ServiceTier::Scale,
                ServiceTier::Priority,
            ]
            .into_iter()
            .filter(|tier| supports_service_tier(model, *tier))
            .collect()
        };
        let priced = |model: &Model| {
            let offered = model.cost.service_tier_multipliers;
            let mut tiers = vec![ServiceTier::Auto];
            if offered.is_some_and(|offered| offered.flex.is_some()) {
                tiers.push(ServiceTier::Flex);
            }
            tiers.push(ServiceTier::Scale);
            if offered.is_some_and(|offered| offered.priority.is_some()) {
                tiers.push(ServiceTier::Priority);
            }
            tiers
        };
        let priority_only = [ServiceTier::Auto, ServiceTier::Scale, ServiceTier::Priority];
        let (mut openrouter, mut priced_flex, mut unpriced, mut codex_priority_only) = (0, 0, 0, 0);
        for model in compiled_models() {
            assert!(supports_service_tier(model, ServiceTier::Default));
            let tiers = eligible(model);
            match (model.provider.as_str(), model.api.as_str()) {
                ("openrouter", "openai-completions") => {
                    openrouter += 1;
                    assert_eq!(
                        tiers,
                        [ServiceTier::Flex, ServiceTier::Priority],
                        "{}",
                        model.id
                    );
                }
                ("openai", "openai-responses") | ("openai-codex", "openai-codex-responses") => {
                    let expected = priced(model);
                    priced_flex += usize::from(expected.contains(&ServiceTier::Flex));
                    unpriced += usize::from(expected.len() == 2);
                    codex_priority_only +=
                        usize::from(model.provider == "openai-codex" && expected == priority_only);
                    assert_eq!(tiers, expected, "{}/{}", model.provider, model.id);
                }
                (provider, api) => {
                    assert!(tiers.is_empty(), "{provider}/{api}/{}: {tiers:?}", model.id);
                }
            }
        }
        // The catalog still exercises every case.
        assert!(openrouter > 0);
        assert!(priced_flex > 0);
        assert!(unpriced > 0);
        assert!(codex_priority_only > 0);
    }
}
