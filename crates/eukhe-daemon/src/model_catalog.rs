//! The `/model` picker's catalog surface (TS daemon-mode
//! `get_model_catalog`): the full local catalog — the union of the bundled
//! snapshot and the compiled catalog, plus the user's models.json — and the providers with
//! configured auth. Each model object also carries the thinking levels and
//! service tiers it offers, read from the eukhe-ai quirks rulebook
//! (`eukhe_types::ai::CatalogModel`), so clients compute no ladder or tier
//! of their own. The catalog is fully local, so the answer is computed on
//! the request path with no network access.

use eukhe_types::ai::AccountOffer;
use serde_json::{json, Value};

use crate::protocol::{response_success, DaemonResponse};
use crate::worker::Worker;

impl Worker {
    /// `get_model_catalog`: the full catalog and the providers with
    /// configured auth.
    pub(crate) fn handle_get_model_catalog(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("get_model_catalog") {
            return response;
        }
        let served = catalog_snapshot(&self.config.agent_dir);
        response_success(None, "get_model_catalog", Some(served))
    }
}

/// The catalog payload of `agent_dir` as it reads now (registry, models.json
/// and the refreshed-models overlay).
pub(crate) fn catalog_snapshot(agent_dir: &std::path::Path) -> Value {
    let registry = eukhe_core::models::ModelRegistry::create(
        eukhe_core::auth::AuthStorage::create(agent_dir),
        agent_dir.join("models.json"),
    );
    let available = registry
        .get_available()
        .into_iter()
        .cloned()
        .collect::<Vec<_>>();
    let overlay = eukhe_core::models::refresh::load_overlay(agent_dir);
    catalog_payload(&registry, &available, |provider, id| {
        overlay.account_offer(provider, id)
    })
}

/// The wire payload of one catalog snapshot (TS `refreshModelCatalog`'s
/// `{models, configuredProviders}`): the full catalog plus the sorted
/// providers with configured auth. Each model object carries its
/// `thinkingLevels`, `serviceTiers` and, once a refresh recorded its
/// provider's list (`offer`), its `account` offer (the `CatalogModel`
/// shape). `modelsJsonErrors` names each bad models.json entry (the
/// catalog drops that provider), or the file when it cannot be read or
/// parsed; it is empty when the file is good or absent.
fn catalog_payload(
    registry: &eukhe_core::models::ModelRegistry,
    available: &[eukhe_types::ai::Model],
    offer: impl Fn(&str, &str) -> AccountOffer,
) -> Value {
    let mut providers: Vec<String> = available
        .iter()
        .map(|model| model.provider.clone())
        .collect();
    providers.sort();
    providers.dedup();
    // The full catalog, in a canonical (provider, id) order so an open
    // picker's rows never reorder between identical answers.
    let mut entries: Vec<&eukhe_types::ai::Model> = registry.get_all().collect();
    entries.sort_by(|a, b| (&a.provider, &a.id).cmp(&(&b.provider, &b.id)));
    let models: Vec<Value> = entries
        .into_iter()
        .map(|model| {
            let mut value = serde_json::to_value(model).unwrap_or(Value::Null);
            if let Value::Object(object) = &mut value {
                object.insert(
                    "thinkingLevels".to_owned(),
                    json!(eukhe_ai::models::registry_thinking_levels(model)),
                );
                object.insert(
                    "serviceTiers".to_owned(),
                    json!(eukhe_ai::quirks::service_tiers(model.into())),
                );
                let account = offer(&model.provider, &model.id);
                if !account.is_not_refreshed() {
                    object.insert("account".to_owned(), json!(account));
                }
            }
            value
        })
        .collect();
    json!({
        "models": models,
        "configuredProviders": providers,
        "modelsJsonErrors": registry.diagnostics(),
    })
}

#[cfg(test)]
mod tests {
    use eukhe_types::ai::AccountOffer;
    use serde_json::json;

    /// Regression (audit M1): the catalog reply dropped the models.json
    /// errors. Now it names each bad `providers.<id>` entry.
    #[test]
    fn the_catalog_reply_names_a_bad_models_json_entry() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("models.json"),
            r#"{ "providers": { "custom": { "models": [{ "id": "x" }] } } }"#,
        )
        .unwrap();
        let registry = eukhe_core::models::ModelRegistry::create(
            eukhe_core::auth::AuthStorage::create(dir.path()),
            dir.path().join("models.json"),
        );
        assert_eq!(
            super::catalog_payload(&registry, &[], |_, _| AccountOffer::NotRefreshed)
                ["modelsJsonErrors"],
            json!([
                "models.json providers.custom: \"baseUrl\" is required when defining custom models."
            ])
        );
    }

    /// A model its provider's list left out at the last refresh reads
    /// `notOffered`; a listed one `offered`; a provider never refreshed
    /// sends no `account` (what an older daemon sends).
    #[test]
    fn the_catalog_reply_carries_the_account_offer_of_the_last_refresh() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(
            dir.path().join("models-refresh.json"),
            json!({
                "refreshedAt": "2026-11-16T01:39:12.547Z",
                "providers": {},
                "offered": { "openai-codex": ["gpt-6-luna"] },
            })
            .to_string(),
        )
        .unwrap();
        let served = super::catalog_snapshot(dir.path());
        let account = |provider: &str, id: &str| {
            served["models"]
                .as_array()
                .into_iter()
                .flatten()
                .find(|model| model["provider"] == json!(provider) && model["id"] == json!(id))
                .map(|model| model.get("account").cloned())
        };
        assert_eq!(
            [
                account("openai-codex", "gpt-6-luna"),
                account("openai-codex", "gpt-6-sol"),
                account("anthropic", "claude-haiku-5-5"),
            ],
            [
                Some(Some(json!("offered"))),
                Some(Some(json!("notOffered"))),
                Some(None),
            ]
        );
    }
}
