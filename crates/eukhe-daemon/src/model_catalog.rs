//! The `/model` picker's catalog surface (TS daemon-mode
//! `get_model_catalog`): the full local catalog — bundled snapshot or
//! compiled fallback, plus the user's models.json — and the providers with
//! configured auth. The catalog is fully local, so the answer is computed
//! on the request path with no network access.

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
        let agent_dir = &self.config.agent_dir;
        let registry = eukhe_core::models::ModelRegistry::create(
            eukhe_core::auth::AuthStorage::create(agent_dir),
            agent_dir.join("models.json"),
        );
        let available = registry
            .get_available()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        let served = catalog_payload(&registry, &available);
        response_success(None, "get_model_catalog", Some(served))
    }
}

/// The wire payload of one catalog snapshot (TS `refreshModelCatalog`'s
/// `{models, configuredProviders}`): the full catalog minus private Prime
/// Inference models models.json does not declare, plus the sorted providers
/// with configured auth.
fn catalog_payload(
    registry: &eukhe_core::models::ModelRegistry,
    available: &[eukhe_types::ai::Model],
) -> Value {
    let mut providers: Vec<String> = available
        .iter()
        .map(|model| model.provider.clone())
        .collect();
    providers.sort();
    providers.dedup();
    let available_keys: std::collections::HashSet<String> = available
        .iter()
        .map(|model| format!("{}/{}", model.provider, model.id))
        .collect();
    // The catalog keeps every model except private Prime Inference models
    // models.json does not declare, in a canonical (provider, id) order so
    // an open picker's rows never reorder between identical answers.
    let mut entries: Vec<&eukhe_types::ai::Model> = registry
        .get_all()
        .filter(|model| {
            !eukhe_core::models::is_private_prime_inference_model(model)
                || available_keys.contains(&format!("{}/{}", model.provider, model.id))
        })
        .collect();
    entries.sort_by(|a, b| (&a.provider, &a.id).cmp(&(&b.provider, &b.id)));
    let models: Vec<Value> = entries
        .into_iter()
        .map(|model| serde_json::to_value(model).unwrap_or(Value::Null))
        .collect();
    json!({
        "models": models,
        "configuredProviders": providers,
    })
}
