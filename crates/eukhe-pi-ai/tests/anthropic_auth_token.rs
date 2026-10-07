//! Port of `test/anthropic-auth-token.test.ts`: the provider auth cases.
//!
//! The cases that stream through the mocked Anthropic SDK (request headers,
//! `authToken`, betas, system blocks, User-Agent) assert on what the
//! `anthropic-messages` module builds and are deferred to that module's
//! port.

use std::collections::HashMap;
use std::sync::Arc;

use eukhe_chord::context::AbortController;
use eukhe_pi_ai::auth::{ApiKeyResolveInput, AuthContext};
use eukhe_pi_ai::env_api_keys::{ANTHROPIC_AUTH_TOKEN_ENV, ANTHROPIC_OAUTH_TOKEN_ENV};
use eukhe_pi_ai::providers::anthropic::anthropic_provider;
use futures::future::BoxFuture;
use serde_json::json;

/// `{ env: async (name) => table[name], fileExists: async () => false }`.
struct TableAuthContext {
    env: HashMap<String, String>,
}

impl AuthContext for TableAuthContext {
    fn env<'a>(&'a self, name: &'a str) -> BoxFuture<'a, Option<String>> {
        let value = self.env.get(name).cloned();
        Box::pin(async move { value })
    }
    fn file_exists<'a>(&'a self, _path: &'a str) -> BoxFuture<'a, bool> {
        Box::pin(async { false })
    }
}

async fn resolve(env: &[(&str, &str)]) -> serde_json::Value {
    let provider = anthropic_provider();
    let auth = provider
        .auth
        .api_key
        .as_ref()
        .expect("api-key auth")
        .resolve(ApiKeyResolveInput {
            ctx: Arc::new(TableAuthContext {
                env: env
                    .iter()
                    .map(|(name, value)| ((*name).to_owned(), (*value).to_owned()))
                    .collect(),
            }),
            credential: None,
            signal: AbortController::new().signal(),
        })
        .await
        .expect("resolve");
    serde_json::to_value(auth).expect("json")
}

#[tokio::test]
async fn resolves_anthropic_auth_token_as_a_bearer_authorization_header() {
    let auth = resolve(&[
        ("ANTHROPIC_AUTH_TOKEN", "auth-token"),
        ("ANTHROPIC_OAUTH_TOKEN", "oauth-token"),
        ("ANTHROPIC_API_KEY", "api-key"),
    ])
    .await;

    assert_eq!(
        auth,
        json!({
            "auth": { "headers": { "Authorization": "Bearer auth-token" } },
            "source": ANTHROPIC_AUTH_TOKEN_ENV,
        })
    );
}

#[tokio::test]
async fn preserves_anthropic_oauth_token_as_oauth_shaped_api_auth() {
    let auth = resolve(&[
        ("ANTHROPIC_OAUTH_TOKEN", "oauth-token"),
        ("ANTHROPIC_API_KEY", "api-key"),
    ])
    .await;

    assert_eq!(
        auth,
        json!({
            "auth": { "apiKey": "oauth-token" },
            "source": ANTHROPIC_OAUTH_TOKEN_ENV,
        })
    );
}
