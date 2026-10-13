//! Transport pinning — the security invariant of the catalog.
//!
//! Ported from `parseProviderModelCatalog` in
//! `provider-model-catalog.ts`: every catalog model must match a compiled
//! `(provider, api, baseUrl)` tuple. Non-matching entries drop silently;
//! request headers come from the compiled transport templates
//! (`template?.headers ?? transport.headers`), never from catalog data;
//! prime-inference entries are skipped (that domain ships compiled). A
//! catalog entry that states no service tiers takes its compiled row's.
//! Each pinned entry's compat lies over its provider's compat defaults on
//! its API, the same layering compiled rows get.

use std::collections::{BTreeMap, HashMap};

use eukhe_ai::model_catalog::with_provider_compat_defaults;
use eukhe_types::ai::ModelCompat;
use eukhe_types::pi_ai::ServiceTierMultipliers;

use crate::schema::{parse_model_catalog, InvalidEntries};
use crate::Model;

/// A template's request headers.
type TemplateHeaders = Option<BTreeMap<String, String>>;

/// What the compiled row of one `(provider, id)` lends its catalog entry.
#[derive(Clone, Default)]
struct ExactTemplate {
    headers: TemplateHeaders,
    service_tier_multipliers: Option<ServiceTierMultipliers>,
}

/// The compiled `(provider, api, baseUrl)` template tables for pinning.
#[derive(Clone, Default)]
pub struct PinnedTemplates {
    /// `(provider, api, baseUrl)` -> transport template headers.
    transports: HashMap<(String, String, String), TemplateHeaders>,
    /// `(provider, id)` -> exact model template.
    exact: HashMap<(String, String), ExactTemplate>,
}

impl PinnedTemplates {
    /// Index the compiled catalog plus the header-less
    /// [`SUPPLEMENTAL_TRANSPORTS`](crate::transports::SUPPLEMENTAL_TRANSPORTS)
    /// (production use).
    #[must_use]
    pub fn from_compiled() -> Self {
        let mut pinned = Self::from_models(crate::transports::compiled_models().iter().cloned());
        for (provider, api, base_url) in crate::transports::SUPPLEMENTAL_TRANSPORTS {
            pinned
                .transports
                .entry((provider.to_string(), api.to_string(), base_url.to_string()))
                .or_insert(None);
        }
        pinned
    }

    /// Index an arbitrary template list (tests).
    pub fn from_models<I: IntoIterator<Item = Model>>(models: I) -> Self {
        let mut pinned = PinnedTemplates::default();
        for model in models {
            pinned.exact.insert(
                (model.provider.clone(), model.id.clone()),
                ExactTemplate {
                    headers: model.headers.clone(),
                    service_tier_multipliers: model.cost.service_tier_multipliers,
                },
            );
            pinned
                .transports
                .insert((model.provider, model.api, model.base_url), model.headers);
        }
        pinned
    }
}

/// Catalog data can select installed transports, but cannot change where
/// credentials are sent: parse the payload with skip-invalid semantics and
/// keep only entries whose `(provider, api, baseUrl)` matches a compiled
/// tuple. `Err` means the catalog carried nothing this client supports.
///
/// # Errors
///
/// Fails when the payload fails schema parsing (unsupported schema version,
/// invalid model count, duplicates) or when no entry pins to a compiled
/// transport.
pub fn parse_provider_model_catalog(
    payload: &serde_json::Value,
    templates: &PinnedTemplates,
) -> Result<Vec<Model>, String> {
    let catalog = parse_model_catalog(payload, InvalidEntries::SkipInvalid)?;
    pin_catalog_models(catalog.models, templates)
}

/// Pin an already-parsed catalog's models to compiled transports.
///
/// # Errors
///
/// Fails when no entry pins to a compiled transport: the catalog carried
/// nothing this client supports.
pub fn pin_catalog_models(
    catalog_models: Vec<Model>,
    templates: &PinnedTemplates,
) -> Result<Vec<Model>, String> {
    let mut models = Vec::with_capacity(catalog_models.len());
    for model in catalog_models {
        // Prime Inference ships compiled; the provider catalog never
        // carries it.
        if model.provider == "prime-inference" {
            continue;
        }
        let key = (
            model.provider.clone(),
            model.api.clone(),
            model.base_url.clone(),
        );
        let Some(transport) = templates.transports.get(&key) else {
            // Non-matching tuples drop silently: the catalog can never
            // introduce a transport.
            continue;
        };
        let exact = templates
            .exact
            .get(&(model.provider.clone(), model.id.clone()));
        let mut pinned = model;
        pinned.headers = exact
            .and_then(|exact| exact.headers.clone())
            .or_else(|| transport.clone());
        if pinned.cost.service_tier_multipliers.is_none() {
            pinned.cost.service_tier_multipliers =
                exact.and_then(|exact| exact.service_tier_multipliers);
        }
        pinned.compat = with_provider_compat_defaults(
            &pinned.provider,
            &pinned.api,
            pinned.compat.as_ref().map(|compat| &compat.raw),
        )
        .map(|raw| ModelCompat { raw });
        models.push(pinned);
    }
    if models.is_empty() {
        return Err("Catalog has no models supported by this client".into());
    }
    Ok(models)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::collections::BTreeMap;

    fn compiled_fixture() -> PinnedTemplates {
        let mut headers = BTreeMap::new();
        headers.insert("User-Agent".to_string(), "cli/1".to_string());
        let mut exact_headers = BTreeMap::new();
        exact_headers.insert("User-Agent".to_string(), "special/2".to_string());
        let entry = |id: &str,
                     api: &str,
                     provider: &str,
                     base_url: &str,
                     headers: Option<BTreeMap<String, String>>| {
            Model {
                id: id.into(),
                name: id.into(),
                api: api.into(),
                provider: provider.into(),
                base_url: base_url.into(),
                reasoning: false,
                thinking_level_map: None,
                input: vec![],
                cost: eukhe_types::ai::ModelCost {
                    input: 0.0.into(),
                    output: 0.0.into(),
                    cache_read: 0.0.into(),
                    cache_write: 0.0.into(),
                    service_tier_multipliers: None,
                },
                context_window: 1,
                max_tokens: 1,
                max_tokens_explicit: false,
                featured: None,
                headers,
                compat: None,
            }
        };
        PinnedTemplates::from_models(vec![
            entry(
                "known",
                "openai-completions",
                "prov",
                "https://prov.example",
                Some(headers),
            ),
            entry(
                "exact",
                "openai-completions",
                "prov",
                "https://prov.example",
                Some(exact_headers),
            ),
        ])
    }

    fn catalog_entry(id: &str, api: &str, provider: &str, base_url: &str) -> serde_json::Value {
        json!({
            "id": id,
            "name": id,
            "api": api,
            "provider": provider,
            "baseUrl": base_url,
            "reasoning": false,
            "input": ["text"],
            "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0},
            "contextWindow": 128_000,
            "maxTokens": 4_096,
        })
    }

    #[test]
    fn keeps_only_compiled_tuples() {
        let templates = compiled_fixture();
        let payload = json!({"schemaVersion": 1, "models": [
            catalog_entry("known", "openai-completions", "prov", "https://prov.example"),
            catalog_entry("unknown", "openai-completions", "prov", "https://elsewhere.example"),
            catalog_entry("prime", "openai-completions", "prime-inference", "https://api.pinference.ai/api/v1"),
        ]});
        let models = parse_provider_model_catalog(&payload, &templates).expect("pinned");
        assert_eq!(models.len(), 1);
        assert_eq!(models[0].id, "known");
        assert_eq!(
            models[0]
                .headers
                .as_ref()
                .unwrap()
                .get("User-Agent")
                .unwrap(),
            "cli/1"
        );
    }

    #[test]
    fn exact_template_headers_win_over_transport_headers() {
        let templates = compiled_fixture();
        let payload = json!({"schemaVersion": 1, "models": [
            catalog_entry("exact", "openai-completions", "prov", "https://prov.example"),
        ]});
        let models = parse_provider_model_catalog(&payload, &templates).expect("pinned");
        assert_eq!(
            models[0]
                .headers
                .as_ref()
                .unwrap()
                .get("User-Agent")
                .unwrap(),
            "special/2"
        );
    }

    #[test]
    fn an_entry_without_service_tiers_takes_its_compiled_rows() {
        let mut templates = compiled_fixture();
        let compiled = ServiceTierMultipliers {
            flex: None,
            priority: Some(2.0),
        };
        templates
            .exact
            .get_mut(&("prov".to_string(), "exact".to_string()))
            .expect("exact template")
            .service_tier_multipliers = Some(compiled);
        let silent = catalog_entry(
            "exact",
            "openai-completions",
            "prov",
            "https://prov.example",
        );
        let mut stated = silent.clone();
        stated["cost"]["serviceTierMultipliers"] = json!({"priority": 3});
        for (entry, expected) in [
            (silent, compiled),
            (
                stated,
                ServiceTierMultipliers {
                    flex: None,
                    priority: Some(3.0),
                },
            ),
        ] {
            let payload = json!({"schemaVersion": 1, "models": [entry]});
            let models = parse_provider_model_catalog(&payload, &templates).expect("pinned");
            assert_eq!(models[0].cost.service_tier_multipliers, Some(expected));
        }
    }

    #[test]
    fn empty_result_is_an_error() {
        let templates = compiled_fixture();
        let payload = json!({"schemaVersion": 1, "models": [
            catalog_entry("unknown", "openai-completions", "prov", "https://elsewhere.example"),
        ]});
        assert!(parse_provider_model_catalog(&payload, &templates).is_err());
    }

    #[test]
    fn catalog_never_carries_headers() {
        let templates = compiled_fixture();
        let mut evil = catalog_entry(
            "known",
            "openai-completions",
            "prov",
            "https://prov.example",
        );
        evil.as_object_mut()
            .unwrap()
            .insert("headers".into(), json!({"X-Evil": "1"}));
        let payload = json!({"schemaVersion": 1, "models": [
            evil,
            catalog_entry("exact", "openai-completions", "prov", "https://prov.example"),
        ]});
        let models = parse_provider_model_catalog(&payload, &templates).expect("pinned");
        assert_eq!(models.len(), 1, "the headers-carrying entry is dropped");
        assert_eq!(models[0].id, "exact");
        assert!(!models[0]
            .headers
            .as_ref()
            .is_some_and(|headers| headers.contains_key("X-Evil")));
    }

    #[test]
    fn supplemental_transports_pin_without_headers() {
        let payload = json!({"schemaVersion": 1, "models": [
            catalog_entry("grok-x", "openai-completions", "xai", "https://api.x.ai/v1"),
            catalog_entry("mimo-x", "anthropic-messages", "xiaomi", "https://api.xiaomimimo.com/anthropic"),
            catalog_entry("grok-y", "openai-completions", "xai", "https://elsewhere.example"),
        ]});
        let models = parse_provider_model_catalog(&payload, &PinnedTemplates::from_compiled())
            .expect("pinned");
        let ids: Vec<&str> = models.iter().map(|model| model.id.as_str()).collect();
        assert_eq!(ids, vec!["grok-x", "mimo-x"]);
        assert!(models.iter().all(|model| model.headers.is_none()));
    }

    #[test]
    fn pinned_entries_lie_over_their_provider_compat_defaults() {
        let base_url = crate::transports::compiled_models()
            .iter()
            .find(|model| model.provider == "openrouter" && model.api == "openai-completions")
            .expect("a compiled OpenRouter completions row")
            .base_url
            .clone();
        let mut stated = catalog_entry("stated", "openai-completions", "openrouter", &base_url);
        stated["compat"] = json!({"supportsStore": false});
        let silent = catalog_entry("silent", "openai-completions", "openrouter", &base_url);
        let payload = json!({"schemaVersion": 1, "models": [stated, silent]});
        let models = parse_provider_model_catalog(&payload, &PinnedTemplates::from_compiled())
            .expect("pinned");
        let compat = |index: usize| &models[index].compat.as_ref().expect("compat").raw;

        let defaults = with_provider_compat_defaults("openrouter", "openai-completions", None)
            .expect("OpenRouter completions defaults");
        assert_eq!(compat(1), &defaults);
        // The row's key wins over the provider default of the same key.
        assert_eq!(compat(0)["supportsStore"], json!(false));
        assert_eq!(compat(0)["serviceTiers"], json!(["flex", "priority"]));
        // The host facts reach the tier eligibility of a bundled entry.
        assert!(eukhe_types::ai::supports_service_tier(
            &models[1],
            eukhe_types::ai::ServiceTier::Flex
        ));
    }
}
