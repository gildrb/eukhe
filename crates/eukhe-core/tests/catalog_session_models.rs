//! Every model `eukhe model list` lists resolves as `--provider <p>
//! --model <id>` in a session, the bundled snapshot's models the compiled
//! catalog lacks included: one model registry serves both the model
//! list and `--model` resolution.
//!
//! Its own test binary: the process-wide built-in catalog reads the
//! install's package directory (`EUKHE_PACKAGE_DIR`) once, so the variable
//! is set before anything reads the catalog.

use std::collections::HashSet;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::auth::AuthStorage;
use eukhe_core::durable::{create_models, resolve_session_model, ModelRequest, ModelsError};
use eukhe_core::models::{resolve_cli_model, ModelRegistry};
use eukhe_core::settings::{Settings, SettingsManager};

/// A model of each kind the compiled catalog lacks: the provider's own
/// routes (Cloudflare's Claude route and its compat route for `vendor/model`
/// ids, xAI Responses), ids with slashes and colons (Fireworks,
/// `OpenRouter`, Bedrock), an id that extends a compiled model's id
/// (`OpenRouter`'s `anthropic/claude-fable-5.2` beside the compiled
/// `anthropic/claude-fable-5`), and a provider only the bundled catalog has
/// (`azure-openai-responses`).
const SNAPSHOT_ONLY: [(&str, &str); 9] = [
    ("cloudflare-ai-gateway", "claude-haiku-5-5"),
    ("cloudflare-ai-gateway", "alibaba/qwen3-max"),
    ("xai", "grok-4.20-0309-reasoning"),
    ("fireworks", "accounts/fireworks/models/kimi-k3p1-pro"),
    ("openrouter", "baidu/ernie-5.5-flash-preview:free"),
    ("openrouter", "anthropic/claude-fable-5.2"),
    ("amazon-bedrock", "us.moonshotai.kimi-k3.1"),
    ("opencode-go", "kimi-k3.1-pro"),
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
    // an explicit provider's prefix is stripped from the selector.
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

/// A requested model resolves exactly in a session or is not found: ids
/// the catalog lacks never run as another model of the provider (an id
/// that other ids extend) or under the provider's template, and
/// Cloudflare's dotted Claude ids, which the catalog no longer lists, run
/// as the dashed models their aliases name.
#[tokio::test]
async fn requested_models_resolve_exactly_or_are_not_found() {
    let package = tempfile::tempdir().expect("package dir");
    let agent = tempfile::tempdir().expect("agent dir");
    listed_models(package.path(), agent.path());
    let session = create_models(agent.path());
    let catalog: HashSet<(String, String)> = session
        .models
        .get_models(None)
        .into_iter()
        .map(|model| (model.provider, model.id))
        .collect();
    let settings = SettingsManager::in_memory(&Settings::default());
    let resolve = |provider: &str, id: &str| {
        let request = ModelRequest {
            provider: Some(provider.to_owned()),
            pattern: id.to_owned(),
        };
        let models = &session.models;
        let settings = &settings;
        async move {
            resolve_session_model(models, settings, Some(&request), None, &BACKGROUND_CONTEXT)
                .await
                .map(|resolved| {
                    resolved.map(|resolved| (resolved.model.provider, resolved.model.model_id))
                })
        }
    };

    for (provider, id, extended) in [
        (
            "openrouter",
            "anthropic/claude-opus-4",
            "anthropic/claude-opus-4.8:batch",
        ),
        (
            "openrouter",
            "qwen/qwen3-235b-a22b",
            "qwen/qwen3-235b-a22b-thinking-2507",
        ),
        ("openai-codex", "gpt-5.3-codex", "gpt-5.3-codex-spark"),
    ] {
        let key = |id: &str| (provider.to_owned(), id.to_owned());
        assert!(
            !catalog.contains(&key(id)),
            "{provider}/{id} is no catalog model"
        );
        assert!(catalog.contains(&key(extended)), "{provider}/{extended} is");
        match resolve(provider, id).await {
            Err(ModelsError::Requested(error)) => assert_eq!(
                error,
                format!(
                    "Model \"{provider}/{id}\" not found. Use \"eukhe model list\" to see available models."
                )
            ),
            other => panic!("{provider}/{id}: {other:?}"),
        }
    }

    for (dotted, dashed) in [
        ("claude-fable-5.1", "claude-fable-5-1"),
        ("claude-haiku-4.5", "claude-haiku-4-5"),
        ("claude-opus-4.5", "claude-opus-4-5"),
        ("claude-opus-4.6", "claude-opus-4-6"),
        ("claude-opus-4.7", "claude-opus-4-7"),
        ("claude-opus-4.8", "claude-opus-4-8"),
        ("claude-sonnet-4.5", "claude-sonnet-4-5"),
        ("claude-sonnet-4.6", "claude-sonnet-4-6"),
    ] {
        let provider = "cloudflare-ai-gateway";
        assert!(!catalog.contains(&(provider.to_owned(), dotted.to_owned())));
        assert_eq!(
            resolve(provider, dotted)
                .await
                .unwrap_or_else(|error| panic!("{provider}/{dotted}: {error}")),
            Some((provider.to_owned(), dashed.to_owned())),
            "{provider}/{dotted}"
        );
    }
}
