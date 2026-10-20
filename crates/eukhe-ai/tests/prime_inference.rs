//! Tests of the eukhe `prime-inference` provider: the compiled static
//! catalog and the api-key auth.

mod common;

use std::sync::Arc;

use eukhe_ai::auth::{AuthResolutionOverrides, InMemoryCredentialStore};
use eukhe_ai::models::{create_models, CreateModelsOptions};
use eukhe_ai::providers::prime_inference::prime_inference_provider;
use eukhe_ai::providers::prime_inference_models::PRIME_INFERENCE_MODELS;
use eukhe_types::pi_ai::{AnyModel, Model};

#[test]
fn ships_the_compiled_offline_catalog() {
    let models: Vec<Model> = PRIME_INFERENCE_MODELS.values().cloned().collect();
    assert_eq!(models.len(), 110);
    assert_eq!(
        models
            .iter()
            .filter(|model| model.featured == Some(true))
            .count(),
        31
    );
    // Private routes: `internal/`, `dev/`, or an alias with `:`.
    assert!(models.iter().all(|model| {
        let id = model.id.to_ascii_lowercase();
        model.provider == "prime-inference"
            && model.api == "openai-completions"
            && !id.starts_with("internal/")
            && !id.starts_with("dev/")
            && !id.contains(':')
    }));
}

#[test]
fn lists_the_compiled_catalog_without_a_refresh() {
    let provider = prime_inference_provider();
    assert!(provider.refresh_models.is_none());
    let listed = (provider.get_models)().expect("models");
    let expected: Vec<AnyModel> = PRIME_INFERENCE_MODELS
        .values()
        .cloned()
        .map(AnyModel::Chat)
        .collect();
    assert_eq!(listed.to_vec(), expected);
}

#[tokio::test]
async fn resolves_the_team_header_from_the_stored_credential_env() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    common::store(
        credentials.as_ref(),
        "prime-inference",
        eukhe_ai::auth::Credential::ApiKey(eukhe_ai::auth::ApiKeyCredential {
            key: Some("pk".into()),
            env: Some(
                [("PRIME_TEAM_ID".to_owned(), "team-1".to_owned())]
                    .into_iter()
                    .collect(),
            ),
            ..eukhe_ai::auth::ApiKeyCredential::default()
        }),
    )
    .await;
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials),
        ..CreateModelsOptions::default()
    });
    models.set_provider(prime_inference_provider());
    let auth = models
        .get_auth("prime-inference", AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(auth.auth.api_key.as_deref(), Some("pk"));
    assert_eq!(
        auth.auth
            .headers
            .and_then(|headers| headers.get("X-Prime-Team-ID").cloned().flatten())
            .as_deref(),
        Some("team-1")
    );
    assert_eq!(auth.source.as_deref(), Some("stored credential"));
}
