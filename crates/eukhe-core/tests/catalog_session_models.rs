//! Every model `eukhe model list` lists resolves as `--provider <p>
//! --model <id>` in a session, the bundled snapshot's models the compiled
//! catalog lacks included: omp's one model registry serves both its model
//! list and `--model` resolution.
//!
//! Its own test binary: the process-wide built-in catalog reads the
//! install's package directory (`EUKHE_PACKAGE_DIR`) once, so the variable
//! is set before anything reads the catalog.

use std::collections::HashSet;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::auth::AuthStorage;
use eukhe_core::durable::{create_models, resolve_session_model, ModelRequest};
use eukhe_core::models::{resolve_cli_model, ModelRegistry};
use eukhe_core::settings::{Settings, SettingsManager};

/// A model of each kind the compiled catalog lacks: a route the provider
/// does not implement (Xiaomi token plan over `anthropic-messages`), the
/// provider's own route (Codex, Cloudflare's dotted Claude ids, xAI), ids
/// with slashes and colons (Fireworks, `OpenRouter`, Bedrock), an id
/// another model's id extends (`OpenRouter`'s `anthropic/claude-opus-4` beside
/// `anthropic/claude-opus-4.8:batch`), and a provider only the snapshot
/// has (`azure-openai-responses`).
const SNAPSHOT_ONLY: [(&str, &str); 9] = [
    ("xiaomi-token-plan-ams", "mimo-v2-flash"),
    ("openai-codex", "gpt-5.1"),
    ("cloudflare-ai-gateway", "claude-opus-4.6"),
    ("xai", "grok-4.20-0309-reasoning"),
    ("fireworks", "accounts/fireworks/models/kimi-k2p6"),
    ("openrouter", "inclusionai/ling-3.0-flash-fin:free"),
    ("openrouter", "anthropic/claude-opus-4"),
    ("amazon-bedrock", "deepseek.r1-v1:0"),
    ("azure-openai-responses", "gpt-5"),
];

/// Every model `eukhe model list` lists in `agent` with a stored key for
/// every provider, with the pinned catalog snapshot (the eukhe-models
/// parity fixture) as the install's bundled catalog in `package`.
fn listed_models(package: &std::path::Path, agent: &std::path::Path) -> Vec<(String, String)> {
    std::fs::write(
        package.join("models.bundled.json"),
        include_str!("../../eukhe-models/tests/fixtures/catalog.v1.json"),
    )
    .expect("write the bundled catalog");
    std::env::set_var("EUKHE_PACKAGE_DIR", package);
    let all = ModelRegistry::create(AuthStorage::create(agent), agent.join("models.json"));
    let keys: serde_json::Map<String, serde_json::Value> = all
        .get_all()
        .map(|model| {
            let key = serde_json::json!({ "type": "api_key", "key": "catalog-key" });
            (model.provider.clone(), key)
        })
        .collect();
    std::fs::write(
        agent.join("auth.json"),
        serde_json::Value::Object(keys).to_string(),
    )
    .expect("write auth.json");
    ModelRegistry::create(AuthStorage::create(agent), agent.join("models.json"))
        .get_available()
        .into_iter()
        .map(|model| (model.provider.clone(), model.id.clone()))
        .collect()
}

#[tokio::test]
async fn every_listed_model_resolves_in_a_session() {
    let package = tempfile::tempdir().expect("package dir");
    let agent = tempfile::tempdir().expect("agent dir");
    let listed = listed_models(package.path(), agent.path());
    for (provider, id) in SNAPSHOT_ONLY {
        assert!(
            listed.iter().any(|(p, i)| p == provider && i == id),
            "model list lists {provider}/{id}"
        );
    }

    // Every listed model is a model of the session: `--model` resolves
    // against the session's whole catalog (`resolve_session_model`), and
    // whether a provider runs with the stored key is its own auth's call
    // (Cloudflare needs its account, Codex a ChatGPT token).
    let session = create_models(agent.path());
    let catalog: HashSet<(String, String)> = session
        .models
        .get_models(None)
        .into_iter()
        .map(|model| (model.provider, model.id))
        .collect();
    let missing: Vec<String> = listed
        .iter()
        .filter(|key| !catalog.contains(*key))
        .map(|(provider, id)| format!("{provider}/{id}"))
        .collect();
    assert!(
        missing.is_empty(),
        "{} of the {} listed models are not in the session:\n{}",
        missing.len(),
        listed.len(),
        missing.join("\n")
    );

    // Every listed model resolves to itself as `--provider <p> --model
    // <id>`, but an id that starts with its own provider (`openrouter/auto`):
    // like omp (model-resolver.ts `resolveCliModelInScope`), an explicit
    // provider's prefix is stripped from the selector.
    let session_models: Vec<eukhe_types::ai::Model> = session
        .models
        .get_models(None)
        .iter()
        .map(|model| eukhe_models::pi_ai_model::registry_model(model).expect("converts"))
        .collect();
    let unresolved: Vec<String> = listed
        .iter()
        .filter(|(provider, id)| !id.starts_with(&format!("{provider}/")))
        .filter_map(|(provider, id)| {
            let resolved = resolve_cli_model(Some(provider), id, &session_models);
            match resolved.model {
                Some(model) if model.provider == *provider && model.id == *id => None,
                Some(model) => Some(format!(
                    "{provider}/{id}: resolves to {}/{}",
                    model.provider, model.id
                )),
                None => Some(format!("{provider}/{id}: {:?}", resolved.error)),
            }
        })
        .collect();
    assert!(
        unresolved.is_empty(),
        "{} of the {} listed models do not resolve to themselves:\n{}",
        unresolved.len(),
        listed.len(),
        unresolved.join("\n")
    );

    // The session's model resolution end to end, for each kind.
    let settings = SettingsManager::in_memory(&Settings::default());
    for (provider, id) in SNAPSHOT_ONLY {
        let request = ModelRequest {
            provider: Some(provider.to_owned()),
            pattern: id.to_owned(),
        };
        let resolved = resolve_session_model(
            &session.models,
            &settings,
            Some(&request),
            None,
            &BACKGROUND_CONTEXT,
        )
        .await
        .unwrap_or_else(|error| panic!("{provider}/{id} resolves: {error}"))
        .unwrap_or_else(|| panic!("{provider}/{id} resolves to a model"));
        assert_eq!(
            (
                resolved.model.provider.as_str(),
                resolved.model.model_id.as_str()
            ),
            (provider, id)
        );
    }
}
