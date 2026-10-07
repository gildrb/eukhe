//! Test helper for resolving API keys from `~/.pi/agent/auth.json`. Port of
//! `test/oauth.ts`, shared by the real-endpoint tests.
//!
//! Supports both API key and OAuth credentials. OAuth tokens are refreshed
//! when expired and saved back to auth.json.

use std::os::unix::fs::{DirBuilderExt as _, PermissionsExt as _};
use std::path::PathBuf;

use serde_json::{Map, Value};

use super::errors::date_now;
use super::types::{Credential, OAuthCredential};
use crate::providers::all::builtin_providers;

fn auth_path() -> Option<PathBuf> {
    std::env::home_dir().map(|home| home.join(".pi").join("agent").join("auth.json"))
}

fn load_auth_storage() -> Map<String, Value> {
    let Some(path) = auth_path() else {
        return Map::new();
    };
    std::fs::read_to_string(path)
        .ok()
        .and_then(|content| serde_json::from_str(&content).ok())
        .unwrap_or_default()
}

fn save_auth_storage(storage: &Map<String, Value>) -> std::io::Result<()> {
    let Some(path) = auth_path() else {
        return Ok(());
    };
    if let Some(config_dir) = path.parent() {
        if !config_dir.exists() {
            std::fs::DirBuilder::new()
                .recursive(true)
                .mode(0o700)
                .create(config_dir)?;
        }
    }
    let content = serde_json::to_string_pretty(storage).map_err(std::io::Error::other)?;
    std::fs::write(&path, content)?;
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600))
}

/// Resolve the API key for `provider` from `~/.pi/agent/auth.json`: the key
/// of an api-key credential, or the (refreshed if expired) OAuth access token.
pub(crate) async fn resolve_api_key(provider: &str) -> Option<String> {
    let mut storage = load_auth_storage();
    let entry: Credential = serde_json::from_value(storage.get(provider)?.clone()).ok()?;

    let credential: OAuthCredential = match entry {
        Credential::ApiKey(credential) => return credential.key,
        Credential::OAuth(credential) => credential,
    };
    let oauth = builtin_providers()
        .into_iter()
        .find(|candidate| candidate.id == provider)?
        .auth
        .oauth?;
    let credential = if date_now() >= credential.expires {
        match oauth
            .refresh(
                credential,
                eukhe_chord::context::AbortController::new().signal(),
            )
            .await
        {
            Ok(credential) => credential,
            Err(error) => {
                println!("{}", Value::String(error.to_string()));
                return None;
            }
        }
    } else {
        credential
    };
    storage.insert(provider.to_owned(), serde_json::to_value(&credential).ok()?);
    save_auth_storage(&storage).ok()?;
    oauth.to_auth(&credential).await.ok()?.api_key
}

#[tokio::test]
#[ignore = "needs ~/.pi/agent/auth.json with an anthropic credential; run with --ignored"]
async fn resolves_an_api_key_from_the_pi_auth_file() {
    assert!(resolve_api_key("anthropic").await.is_some());
}
