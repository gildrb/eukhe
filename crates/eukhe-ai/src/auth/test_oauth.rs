//! Test helper for resolving API keys from an explicit credential file. Port
//! of `test/oauth.ts`, shared by the real-endpoint tests.
//!
//! The env var [`AUTH_FILE_ENV`] names the file. The helper never reads or
//! writes a file at a fixed path, so it never touches the credentials of
//! another product. It supports API key and OAuth credentials. It refreshes
//! an expired OAuth token and writes it back under a lock, through a 0600
//! temp file and an atomic rename.

use std::io::Write as _;
use std::os::unix::fs::OpenOptionsExt as _;
use std::path::Path;

use serde_json::{Map, Value};

use super::errors::date_now;
use super::types::{Credential, OAuthCredential};
use crate::providers::all::builtin_providers;

/// The env var that names the credential file of the live tests.
pub(crate) const AUTH_FILE_ENV: &str = "EUKHE_TEST_OAUTH_AUTH_FILE";

/// Read and parse the credential file as a JSON object.
fn read_document(auth_file: &Path) -> Result<Map<String, Value>, String> {
    let content = std::fs::read_to_string(auth_file)
        .map_err(|error| format!("Failed to read {}: {error}", auth_file.display()))?;
    serde_json::from_str(&content)
        .map_err(|error| format!("Failed to parse {}: {error}", auth_file.display()))
}

/// Resolve the API key for `provider` from `auth_file`: the key of an
/// api-key credential, or the OAuth access token. An expired OAuth token is
/// refreshed and written back. `Ok(None)` when the file has no credential
/// for `provider`.
///
/// # Errors
///
/// Returns an error when the file cannot be read or parsed, when the
/// credential is not valid, when the refresh fails, or when the write back
/// fails. A failed write changes nothing in the file.
pub(crate) async fn resolve_api_key(
    auth_file: &Path,
    provider: &str,
) -> Result<Option<String>, String> {
    let Some(entry) = read_document(auth_file)?.remove(provider) else {
        return Ok(None);
    };
    let entry: Credential = serde_json::from_value(entry)
        .map_err(|error| format!("Invalid credential for {provider}: {error}"))?;
    let credential: OAuthCredential = match entry {
        Credential::ApiKey(credential) => return Ok(credential.key),
        Credential::OAuth(credential) => credential,
    };
    let oauth = builtin_providers()
        .into_iter()
        .find(|candidate| candidate.id == provider)
        .and_then(|candidate| candidate.auth.oauth)
        .ok_or_else(|| format!("{provider} has no OAuth flow"))?;
    let credential = if date_now() >= credential.expires {
        let credential = oauth
            .refresh(
                credential,
                eukhe_chord::context::AbortController::new().signal(),
            )
            .await
            .map_err(|error| format!("Failed to refresh {provider}: {error}"))?;
        let value = serde_json::to_value(&credential)
            .map_err(|error| format!("Failed to encode the {provider} credential: {error}"))?;
        // The lock file serializes writers. The write re-reads the file
        // under the lock and changes only this provider's entry.
        let mut lock_path = auth_file.as_os_str().to_os_string();
        lock_path.push(".lock");
        let lock_path = std::path::PathBuf::from(lock_path);
        let lock_error =
            |error: std::io::Error| format!("Failed to lock {}: {error}", lock_path.display());
        let lock = std::fs::OpenOptions::new()
            .create(true)
            .truncate(false)
            .write(true)
            .mode(0o600)
            .open(&lock_path)
            .map_err(lock_error)?;
        lock.lock().map_err(lock_error)?;
        let mut document = read_document(auth_file)?;
        document.insert(provider.to_owned(), value);
        let write_error = |error: &dyn std::fmt::Display| {
            format!("Failed to write {}: {error}", auth_file.display())
        };
        let content =
            serde_json::to_string_pretty(&document).map_err(|error| write_error(&error))?;
        let dir = auth_file
            .parent()
            .filter(|dir| !dir.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        // `tempfile` creates the temp file with mode 0600, so the
        // credentials are never readable by others, not even for a moment.
        let mut temp = tempfile::Builder::new()
            .prefix(".auth.json.")
            .tempfile_in(dir)
            .map_err(|error| write_error(&error))?;
        temp.write_all(content.as_bytes())
            .and_then(|()| temp.as_file().sync_all())
            .map_err(|error| write_error(&error))?;
        temp.persist(auth_file)
            .map_err(|error| write_error(&error.error))?;
        drop(lock);
        credential
    } else {
        credential
    };
    oauth
        .to_auth(&credential)
        .await
        .map(|auth| auth.api_key)
        .map_err(|error| format!("Failed to derive the {provider} auth: {error}"))
}

#[tokio::test]
#[ignore = "needs EUKHE_TEST_OAUTH_AUTH_FILE naming an auth file with an anthropic credential; run with --ignored"]
async fn resolves_an_api_key_from_the_named_auth_file() {
    let Some(auth_file) = std::env::var_os(AUTH_FILE_ENV) else {
        eprintln!("skipped: set {AUTH_FILE_ENV} to the path of a test auth file");
        return;
    };
    let api_key = resolve_api_key(Path::new(&auth_file), "anthropic").await;
    assert!(matches!(api_key, Ok(Some(_))), "{api_key:?}");
}
