//! Port of the provider/`Models` cases of `test/oauth-auth.test.ts` (the
//! `OpenAI` `ChatGPT` OAuth exposure case and the "OAuth through
//! `Models.getAuth`" cases) and of `test/openrouter-oauth.test.ts` ("is
//! exposed alongside API-key auth", "resolves the same stored OAuth key for
//! chat and image models").

mod common;

use std::sync::Arc;

use common::{now_f64, oauth, store};
use eukhe_pi_ai::auth::{AuthResolutionOverrides, CredentialStore, InMemoryCredentialStore};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::anthropic::anthropic_provider;
use eukhe_pi_ai::providers::github_copilot::github_copilot_provider;
use eukhe_pi_ai::providers::openai::openai_provider;
use eukhe_pi_ai::providers::openrouter::openrouter_provider;
use eukhe_types::pi_ai::ModelType;

/// JS `Number.MAX_SAFE_INTEGER`.
const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

#[test]
fn openai_exposes_chatgpt_oauth_alongside_api_key_auth() {
    let provider = openai_provider();
    assert!(provider.auth.api_key.is_some());
    let oauth = provider.auth.oauth.as_ref().expect("oauth");
    assert_eq!(oauth.name(), "OpenAI (ChatGPT subscription)");
    assert_eq!(oauth.is_subscription(), Some(true));
    assert_eq!(oauth.login_label(), Some("Sign in with ChatGPT"));
}

#[tokio::test]
async fn resolves_stored_anthropic_oauth_credentials_via_the_lazy_flow_import() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    store(
        credentials.as_ref(),
        "anthropic",
        // Keep this beyond get_auth()'s refresh window.
        oauth("oauth-access-token", "r", now_f64() + 10.0 * 60_000.0),
    )
    .await;
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials as Arc<dyn CredentialStore>),
        ..CreateModelsOptions::default()
    });
    models.set_provider(anthropic_provider());

    let model = models.get_models(Some("anthropic")).remove(0);
    let result = models
        .get_auth(&model.provider, AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(result.auth.api_key.as_deref(), Some("oauth-access-token"));
    assert_eq!(result.source.as_deref(), Some("OAuth"));
}

#[tokio::test]
async fn resolves_stored_github_copilot_oauth_credentials_including_per_credential_base_url() {
    let access = "tid=abc;exp=123;proxy-ep=proxy.business.githubcopilot.com;rest";
    let credentials = Arc::new(InMemoryCredentialStore::new());
    store(
        credentials.as_ref(),
        "github-copilot",
        // Keep this beyond get_auth()'s refresh window.
        oauth(access, "r", now_f64() + 10.0 * 60_000.0),
    )
    .await;
    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials as Arc<dyn CredentialStore>),
        ..CreateModelsOptions::default()
    });
    models.set_provider(github_copilot_provider());

    let model = models.get_models(Some("github-copilot")).remove(0);
    let result = models
        .get_auth(&model.provider, AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(result.auth.api_key.as_deref(), Some(access));
    assert_eq!(
        result.auth.base_url.as_deref(),
        Some("https://api.business.githubcopilot.com")
    );
}

#[test]
fn is_exposed_alongside_api_key_auth() {
    let provider = openrouter_provider();
    assert!(provider.auth.api_key.is_some());
    let oauth = provider.auth.oauth.as_ref().expect("oauth");
    assert_eq!(oauth.login_label(), Some("Sign in with OpenRouter"));
}

#[tokio::test]
async fn resolves_the_same_stored_oauth_key_for_chat_and_image_models() {
    let credentials = Arc::new(InMemoryCredentialStore::new());
    store(
        credentials.as_ref(),
        "openrouter",
        oauth("sk-or-stored", "", MAX_SAFE_INTEGER),
    )
    .await;

    let models = create_models(CreateModelsOptions {
        credentials: Some(credentials as Arc<dyn CredentialStore>),
        ..CreateModelsOptions::default()
    });
    models.set_provider(openrouter_provider());
    let chat_model = models
        .get_models(Some("openrouter"))
        .into_iter()
        .next()
        .expect("chat model");
    let image_model = models
        .get_models_of_type(ModelType::Image, Some("openrouter"))
        .into_iter()
        .next()
        .expect("image model");

    let chat_auth = models
        .get_auth_for_model(&chat_model, AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(chat_auth.auth.api_key.as_deref(), Some("sk-or-stored"));
    let image_auth = models
        .get_auth_for_model(&image_model, AuthResolutionOverrides::default())
        .await
        .expect("auth")
        .expect("configured");
    assert_eq!(image_auth.auth.api_key.as_deref(), Some("sk-or-stored"));
}
