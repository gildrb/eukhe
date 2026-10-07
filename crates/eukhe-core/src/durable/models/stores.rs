//! The persistent stores of the durable model collection: the pi-ai
//! [`CredentialStore`] over eukhe's `auth.json` and the [`ModelsStore`] over
//! `models-store.json`, both through eukhe's locked file backend. The
//! `auth.json` format mapping is documented on the parent module.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::auth::{
    ApiKeyCredential, ApiKeyType, AuthOperationOptions, AuthType, Credential, CredentialInfo,
    CredentialStore, ModifyFn, OAuthCredential,
};
use eukhe_pi_ai::models_store::{ModelsStore, ModelsStoreEntry, ModelsStoreOperationOptions};
use eukhe_pi_ai::providers::prime_inference::{
    PRIME_API_KEY_ENV, PRIME_INFERENCE_PROVIDER_ID, PRIME_TEAM_ID_ENV,
};
use eukhe_pi_ai::utils::abort::{operation_signal, race_with_abort_signal};
use eukhe_pi_ai::utils::diagnostics::{ErrorObject, Thrown};
use eukhe_types::pi_ai::ProviderEnv;
use futures::future::BoxFuture;
use serde_json::{Map, Value};

use crate::auth::resolve_config_value::resolve_config_value;
use crate::auth::{
    parse_storage_data, AuthStorageBackend, FileAuthStorageBackend, PrimeTeamCredential,
};

pub(super) fn thrown(message: String) -> Thrown {
    ErrorObject::new(message).thrown()
}

/// Runs eukhe's synchronous file protocol (and `!command` key resolution)
/// off the async workers.
pub(super) async fn blocking<T, F>(task: F) -> Result<T, Thrown>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, String> + Send + 'static,
{
    match tokio::task::spawn_blocking(task).await {
        Ok(result) => result.map_err(thrown),
        Err(error) if error.is_panic() => std::panic::resume_unwind(error.into_panic()),
        Err(error) => Err(thrown(format!("file access task stopped: {error}"))),
    }
}

/// The parsed JSON object document behind `backend` (`{}` when empty).
fn read_document(backend: &FileAuthStorageBackend) -> Result<Map<String, Value>, String> {
    let content = backend
        .read()
        .map_err(|error| format!("Failed to read {error:#}"))?;
    parse_storage_data(content.as_deref())
        .map(|data| data.0)
        .map_err(|error| format!("Failed to parse the document: {error:#}"))
}

/// Locked read-modify-write of the document. `update` sees the parsed
/// document and returns whether to write it back.
fn update_document<T>(
    backend: &FileAuthStorageBackend,
    mut update: impl FnMut(&mut Map<String, Value>) -> Result<(bool, T), String>,
) -> Result<T, String> {
    let mut outcome = None;
    backend
        .with_lock(&mut |current| {
            let mut document = parse_storage_data(current.as_deref())?.0;
            let (write, value) = update(&mut document).map_err(anyhow::Error::msg)?;
            outcome = Some(value);
            if !write {
                return Ok(((), None));
            }
            Ok(((), Some(serde_json::to_string_pretty(&document)?)))
        })
        .map_err(|error| format!("{error:#}"))?;
    outcome.ok_or_else(|| "the locked update did not run".to_owned())
}

/// pi-ai [`CredentialStore`] over eukhe's `auth.json`. Writes are
/// serialized per provider in-process; the file protocol serializes them
/// across processes.
pub(super) struct AuthJsonCredentialStore {
    backend: Arc<FileAuthStorageBackend>,
    chains: Mutex<HashMap<String, Arc<tokio::sync::Mutex<()>>>>,
}

impl AuthJsonCredentialStore {
    pub(super) fn new(path: impl Into<std::path::PathBuf>) -> Self {
        Self {
            backend: Arc::new(FileAuthStorageBackend::new(path)),
            chains: Mutex::new(HashMap::new()),
        }
    }

    fn chain(&self, provider_id: &str) -> Arc<tokio::sync::Mutex<()>> {
        Arc::clone(
            self.chains
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .entry(provider_id.to_owned())
                .or_default(),
        )
    }

    async fn document(&self) -> Result<Map<String, Value>, Thrown> {
        let backend = Arc::clone(&self.backend);
        blocking(move || read_document(&backend).map_err(|error| format!("auth.json: {error}")))
            .await
    }
}

fn invalid_credential(provider_id: &str) -> String {
    format!("Invalid auth.json credential for provider \"{provider_id}\"")
}

fn non_empty_env(name: &str) -> bool {
    std::env::var(name).is_ok_and(|value| !value.trim().is_empty())
}

/// An auth.json entry as a pi-ai credential (format mapping only). `None`
/// for eukhe-only credential types.
fn stored_credential(provider_id: &str, value: &Value) -> Result<Option<Credential>, String> {
    let Some(object) = value.as_object() else {
        return Err(invalid_credential(provider_id));
    };
    match object.get("type").and_then(Value::as_str) {
        Some("api_key") => {
            let key = match object.get("key") {
                None => None,
                Some(Value::String(key)) => Some(key.clone()),
                Some(_) => return Err(invalid_credential(provider_id)),
            };
            let mut env: Option<ProviderEnv> = match object.get("env") {
                None => None,
                Some(Value::Object(entries)) => Some(
                    entries
                        .iter()
                        .map(|(name, value)| {
                            value
                                .as_str()
                                .map(|value| (name.clone(), value.to_owned()))
                                .ok_or_else(|| invalid_credential(provider_id))
                        })
                        .collect::<Result<_, _>>()?,
                ),
                Some(_) => return Err(invalid_credential(provider_id)),
            };
            match object.get("primeTeam") {
                None | Some(Value::Null) => {}
                Some(team) => {
                    let team: PrimeTeamCredential = serde_json::from_value(team.clone())
                        .map_err(|error| format!("{}: {error}", invalid_credential(provider_id)))?;
                    env.get_or_insert_with(ProviderEnv::new)
                        .insert(PRIME_TEAM_ID_ENV.to_owned(), team.team_id);
                }
            }
            Ok(Some(Credential::ApiKey(ApiKeyCredential {
                kind: ApiKeyType::ApiKey,
                key,
                env,
            })))
        }
        Some("oauth") => serde_json::from_value::<OAuthCredential>(value.clone())
            .map(|credential| Some(Credential::OAuth(credential)))
            .map_err(|error| format!("{}: {error}", invalid_credential(provider_id))),
        _ => Ok(None),
    }
}

/// eukhe's read-time resolution of a stored credential: the Prime
/// environment precedence, then the configured-value resolution of the key.
fn resolve_stored_credential(provider_id: &str, credential: Credential) -> Credential {
    let Credential::ApiKey(mut credential) = credential else {
        return credential;
    };
    if provider_id == PRIME_INFERENCE_PROVIDER_ID {
        if non_empty_env(PRIME_API_KEY_ENV) {
            credential.key = None;
        }
        if non_empty_env(PRIME_TEAM_ID_ENV) {
            if let Some(env) = &mut credential.env {
                env.shift_remove(PRIME_TEAM_ID_ENV);
            }
            if credential.env.as_ref().is_some_and(ProviderEnv::is_empty) {
                credential.env = None;
            }
        }
    }
    credential.key = credential.key.as_deref().and_then(resolve_config_value);
    Credential::ApiKey(credential)
}

/// A pi-ai credential as the auth.json entry replacing `previous`.
fn credential_entry(credential: &Credential, previous: Option<&Value>) -> Result<Value, String> {
    match credential {
        Credential::OAuth(credential) => {
            serde_json::to_value(credential).map_err(|error| error.to_string())
        }
        Credential::ApiKey(credential) => {
            let mut entry = Map::new();
            entry.insert("type".to_owned(), Value::String("api_key".to_owned()));
            if let Some(key) = &credential.key {
                entry.insert("key".to_owned(), Value::String(key.clone()));
            }
            let kept_team = previous
                .and_then(Value::as_object)
                .filter(|previous| {
                    previous.get("type").and_then(Value::as_str) == Some("api_key")
                        && previous.get("key").and_then(Value::as_str) == credential.key.as_deref()
                })
                .and_then(|previous| previous.get("primeTeam"))
                .filter(|team| !team.is_null());
            let mut env = credential.env.clone().unwrap_or_default();
            if let Some(team) = kept_team {
                let team_id = team.get("teamId").and_then(Value::as_str);
                if env.get(PRIME_TEAM_ID_ENV).map(String::as_str) == team_id {
                    env.shift_remove(PRIME_TEAM_ID_ENV);
                }
                entry.insert("primeTeam".to_owned(), team.clone());
            }
            if !env.is_empty() {
                entry.insert(
                    "env".to_owned(),
                    serde_json::to_value(&env).map_err(|error| error.to_string())?,
                );
            }
            Ok(Value::Object(entry))
        }
    }
}

impl CredentialStore for AuthJsonCredentialStore {
    fn read<'a>(
        &'a self,
        provider_id: &'a str,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<Option<Credential>, Thrown>> {
        Box::pin(async move {
            if let Some(signal) = &options.signal {
                signal.throw_if_aborted()?;
            }
            let document = self.document().await?;
            if let Some(signal) = &options.signal {
                signal.throw_if_aborted()?;
            }
            let Some(entry) = document.get(provider_id) else {
                return Ok(None);
            };
            let Some(credential) = stored_credential(provider_id, entry).map_err(thrown)? else {
                return Ok(None);
            };
            let provider_id = provider_id.to_owned();
            // A `!command` key runs a process: off the async workers.
            blocking(move || Ok(Some(resolve_stored_credential(&provider_id, credential)))).await
        })
    }

    fn list(
        &self,
        options: AuthOperationOptions,
    ) -> BoxFuture<'_, Result<Vec<CredentialInfo>, Thrown>> {
        Box::pin(async move {
            if let Some(signal) = &options.signal {
                signal.throw_if_aborted()?;
            }
            let document = self.document().await?;
            if let Some(signal) = &options.signal {
                signal.throw_if_aborted()?;
            }
            Ok(document
                .iter()
                .filter_map(|(provider_id, entry)| {
                    let kind = match entry.get("type").and_then(Value::as_str) {
                        Some("api_key") => AuthType::ApiKey,
                        Some("oauth") => AuthType::OAuth,
                        _ => return None,
                    };
                    Some(CredentialInfo {
                        provider_id: provider_id.clone(),
                        kind,
                    })
                })
                .collect())
        })
    }

    fn modify<'a>(
        &'a self,
        provider_id: &'a str,
        f: ModifyFn,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<Option<Credential>, Thrown>> {
        let signal = operation_signal(options.signal);
        let chain = self.chain(provider_id);
        let backend = Arc::clone(&self.backend);
        let id = provider_id.to_owned();
        let task_signal = signal.clone();
        let task = async move {
            let _turn = chain.lock_owned().await;
            task_signal.throw_if_aborted()?;
            let read_backend = Arc::clone(&backend);
            let document = blocking(move || {
                read_document(&read_backend).map_err(|error| format!("auth.json: {error}"))
            })
            .await?;
            let previous = document.get(&id).cloned();
            let current = match &previous {
                Some(entry) => stored_credential(&id, entry).map_err(thrown)?,
                None => None,
            };
            // `f` (an OAuth refresh: a network round trip) runs outside the
            // document lock, like eukhe's load-then-lock refresh.
            let Some(next) = f(current.clone()).await? else {
                return Ok(current);
            };
            task_signal.throw_if_aborted()?;
            let entry = credential_entry(&next, previous.as_ref()).map_err(thrown)?;
            let write_id = id.clone();
            let concurrent = blocking(move || {
                update_document(&backend, |document| {
                    if document.get(&write_id) != previous.as_ref() {
                        // Another writer changed the entry while `f` ran
                        // (a peer's refresh): its newer credential stands.
                        return Ok((false, Some(document.get(&write_id).cloned())));
                    }
                    document.insert(write_id.clone(), entry.clone());
                    Ok((true, None))
                })
                .map_err(|error| format!("auth.json: {error}"))
            })
            .await?;
            match concurrent {
                None => Ok(Some(next)),
                Some(None) => Ok(None),
                Some(Some(entry)) => stored_credential(&id, &entry).map_err(thrown),
            }
        };
        Box::pin(async move { race_with_abort_signal(task, &signal).await })
    }

    fn delete<'a>(
        &'a self,
        provider_id: &'a str,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<(), Thrown>> {
        let signal = operation_signal(options.signal);
        let chain = self.chain(provider_id);
        let backend = Arc::clone(&self.backend);
        let id = provider_id.to_owned();
        let task_signal = signal.clone();
        let task = async move {
            let _turn = chain.lock_owned().await;
            task_signal.throw_if_aborted()?;
            blocking(move || {
                update_document(&backend, |document| {
                    Ok((document.shift_remove(&id).is_some(), ()))
                })
                .map_err(|error| format!("auth.json: {error}"))
            })
            .await
        };
        Box::pin(async move { race_with_abort_signal(task, &signal).await })
    }
}

/// Locked JSON-backed storage for dynamically refreshed provider catalogs:
/// the pi coding-agent `FileModelsStore`, over eukhe's locked file backend.
pub(super) struct FileModelsStore {
    backend: Arc<FileAuthStorageBackend>,
}

impl FileModelsStore {
    pub(super) fn new(path: impl Into<std::path::PathBuf>) -> Self {
        Self {
            backend: Arc::new(FileAuthStorageBackend::new(path)),
        }
    }
}

fn store_error(error: &str) -> String {
    format!("models-store.json: {error}")
}

fn throw_if_store_aborted(options: &ModelsStoreOperationOptions) -> Result<(), Thrown> {
    match &options.signal {
        Some(signal) => signal.throw_if_aborted(),
        None => Ok(()),
    }
}

impl ModelsStore for FileModelsStore {
    fn read(
        &self,
        provider_id: &str,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<Option<ModelsStoreEntry>, Thrown>> {
        let id = provider_id.to_owned();
        let backend = Arc::clone(&self.backend);
        Box::pin(async move {
            throw_if_store_aborted(&options)?;
            let entry = blocking(move || {
                let document = read_document(&backend).map_err(|error| store_error(&error))?;
                document
                    .get(&id)
                    .map(|entry| {
                        serde_json::from_value::<ModelsStoreEntry>(entry.clone())
                            .map_err(|error| store_error(&format!("entry {id}: {error}")))
                    })
                    .transpose()
            })
            .await?;
            throw_if_store_aborted(&options)?;
            Ok(entry)
        })
    }

    fn write(
        &self,
        provider_id: &str,
        entry: ModelsStoreEntry,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<(), Thrown>> {
        let id = provider_id.to_owned();
        let backend = Arc::clone(&self.backend);
        Box::pin(async move {
            throw_if_store_aborted(&options)?;
            let value = serde_json::to_value(&entry).map_err(|error| thrown(error.to_string()))?;
            blocking(move || {
                update_document(&backend, |document| {
                    document.insert(id.clone(), value.clone());
                    Ok((true, ()))
                })
                .map_err(|error| store_error(&error))
            })
            .await
        })
    }

    fn delete(
        &self,
        provider_id: &str,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<(), Thrown>> {
        let id = provider_id.to_owned();
        let backend = Arc::clone(&self.backend);
        Box::pin(async move {
            throw_if_store_aborted(&options)?;
            blocking(move || {
                update_document(&backend, |document| {
                    document.shift_remove(&id);
                    Ok((true, ()))
                })
                .map_err(|error| store_error(&error))
            })
            .await
        })
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use eukhe_pi_ai::models_store::ModelsStoreEntry;
    use serde_json::json;

    use super::*;
    use crate::auth::{AuthCredential, AuthStorageData};

    fn todays_auth_json() -> Value {
        json!({
            "anthropic": {
                "type": "oauth", "access": "sk-ant-oat-old", "refresh": "rt-old",
                "expires": 1_700_000_000_000_u64
            },
            "github-copilot": {
                "type": "oauth", "access": "tid=1", "refresh": "gh-token",
                "expires": 4_102_444_800_000_u64, "enterpriseUrl": "company.ghe.com"
            },
            "openai-codex": {
                "type": "oauth", "access": "codex-access", "refresh": "codex-refresh",
                "expires": 4_102_444_800_000_u64, "accountId": "acct-1"
            },
            "openai": { "type": "api_key", "key": "sk-openai" },
            "prime-inference": {
                "type": "api_key", "key": "pit-key",
                "primeTeam": {
                    "teamId": "team-1", "name": "Team One", "slug": "team-one",
                    "role": "admin", "createdAt": null
                }
            },
            "mcp:linear": {
                "type": "mcp_static_token", "bearer": "lin-token",
                "endpoint": "https://mcp.linear.app"
            },
            "serper": { "type": "api_key", "key": "serper-key" }
        })
    }

    fn write_json(path: &Path, value: &Value) {
        std::fs::write(path, serde_json::to_string_pretty(value).unwrap()).unwrap();
    }

    fn read_json(path: &Path) -> Map<String, Value> {
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
    }

    fn options() -> AuthOperationOptions {
        AuthOperationOptions::default()
    }

    fn replace_with(next: Option<Credential>) -> ModifyFn {
        Box::new(move |_current| Box::pin(async move { Ok(next) }))
    }

    #[tokio::test]
    async fn credential_store_round_trips_todays_auth_json() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("auth.json");
        let fixture = todays_auth_json();
        write_json(&path, &fixture);
        let store = AuthJsonCredentialStore::new(&path);

        let read = |id: &'static str| store.read(id, options());
        assert_eq!(
            read("anthropic").await.unwrap(),
            Some(Credential::OAuth(OAuthCredential::new(
                "rt-old",
                "sk-ant-oat-old",
                1_700_000_000_000.0
            )))
        );
        assert_eq!(
            read("github-copilot").await.unwrap(),
            Some(Credential::OAuth(
                OAuthCredential::new("gh-token", "tid=1", 4_102_444_800_000.0)
                    .with_extra("enterpriseUrl", json!("company.ghe.com"))
            ))
        );
        assert_eq!(
            read("openai-codex").await.unwrap(),
            Some(Credential::OAuth(
                OAuthCredential::new("codex-refresh", "codex-access", 4_102_444_800_000.0)
                    .with_extra("accountId", json!("acct-1"))
            ))
        );
        assert_eq!(
            read("openai").await.unwrap(),
            Some(Credential::ApiKey(ApiKeyCredential::with_key("sk-openai")))
        );
        assert_eq!(
            read("prime-inference").await.unwrap(),
            Some(Credential::ApiKey(ApiKeyCredential {
                env: Some(ProviderEnv::from([(
                    PRIME_TEAM_ID_ENV.to_owned(),
                    "team-1".to_owned()
                )])),
                ..ApiKeyCredential::with_key("pit-key")
            }))
        );
        assert_eq!(read("mcp:linear").await.unwrap(), None);
        assert_eq!(read("missing").await.unwrap(), None);
        assert_eq!(
            store.list(options()).await.unwrap(),
            [
                ("anthropic", AuthType::OAuth),
                ("github-copilot", AuthType::OAuth),
                ("openai-codex", AuthType::OAuth),
                ("openai", AuthType::ApiKey),
                ("prime-inference", AuthType::ApiKey),
                ("serper", AuthType::ApiKey),
            ]
            .map(|(provider_id, kind)| CredentialInfo {
                provider_id: provider_id.to_owned(),
                kind,
            })
        );

        // An OAuth refresh rewrites only its entry, in a shape the old engine reads.
        let refreshed = OAuthCredential::new("rt-new", "sk-ant-oat-new", 1_800_000_000_000.0);
        assert_eq!(
            store
                .modify(
                    "anthropic",
                    replace_with(Some(Credential::OAuth(refreshed.clone()))),
                    options()
                )
                .await
                .unwrap(),
            Some(Credential::OAuth(refreshed))
        );
        let written = read_json(&path);
        let mut expected = fixture.as_object().unwrap().clone();
        expected.insert(
            "anthropic".to_owned(),
            json!({
                "type": "oauth", "refresh": "rt-new", "access": "sk-ant-oat-new",
                "expires": 1_800_000_000_000_u64
            }),
        );
        assert_eq!(written, expected);
        assert_eq!(
            AuthStorageData(written).credential("anthropic"),
            Some(AuthCredential::Oauth {
                access: "sk-ant-oat-new".to_owned(),
                refresh: Some("rt-new".to_owned()),
                expires: 1_800_000_000_000,
                account_id: None,
                enterprise_url: None,
                endpoint: None,
                token_endpoint: None,
                client_id: None,
                resource: None,
                issuer: None,
            })
        );

        // Re-saving the Prime key keeps the stored team in eukhe's field.
        let prime = store.read("prime-inference", options()).await.unwrap();
        store
            .modify("prime-inference", replace_with(prime), options())
            .await
            .unwrap();
        assert_eq!(
            read_json(&path)["prime-inference"],
            fixture["prime-inference"]
        );

        // `None` leaves the entry and resolves the current credential.
        assert_eq!(
            store
                .modify("openai", replace_with(None), options())
                .await
                .unwrap(),
            Some(Credential::ApiKey(ApiKeyCredential::with_key("sk-openai")))
        );

        store.delete("openai", options()).await.unwrap();
        let written = read_json(&path);
        assert!(!written.contains_key("openai"));
        assert_eq!(written["mcp:linear"], fixture["mcp:linear"]);
    }

    #[tokio::test]
    async fn credential_store_keeps_a_concurrent_writers_newer_credential() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("auth.json");
        write_json(&path, &todays_auth_json());
        let store = AuthJsonCredentialStore::new(&path);
        let peer_path = path.clone();
        let modify: ModifyFn = Box::new(move |_current| {
            Box::pin(async move {
                // A peer process refreshes while this refresh runs.
                update_document(&FileAuthStorageBackend::new(&peer_path), |document| {
                    document.insert(
                        "anthropic".to_owned(),
                        json!({
                            "type": "oauth", "access": "peer-access", "refresh": "peer-refresh",
                            "expires": 1_900_000_000_000_u64
                        }),
                    );
                    Ok((true, ()))
                })
                .unwrap();
                Ok(Some(Credential::OAuth(OAuthCredential::new(
                    "mine-refresh",
                    "mine-access",
                    1_800_000_000_000.0,
                ))))
            })
        });
        let peer = OAuthCredential::new("peer-refresh", "peer-access", 1_900_000_000_000.0);
        assert_eq!(
            store.modify("anthropic", modify, options()).await.unwrap(),
            Some(Credential::OAuth(peer.clone()))
        );
        assert_eq!(
            store.read("anthropic", options()).await.unwrap(),
            Some(Credential::OAuth(peer))
        );
    }

    #[tokio::test]
    async fn an_oauth_entry_without_a_refresh_token_is_invalid() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("auth.json");
        write_json(
            &path,
            &json!({ "xai": { "type": "oauth", "access": "a", "refresh": null, "expires": 1 } }),
        );
        let error = AuthJsonCredentialStore::new(&path)
            .read("xai", options())
            .await
            .unwrap_err();
        assert!(
            error
                .to_string()
                .starts_with("Invalid auth.json credential for provider \"xai\""),
            "{error}"
        );
    }

    #[tokio::test]
    async fn models_store_round_trips_entries() {
        let dir = tempfile::tempdir().unwrap();
        let store = FileModelsStore::new(dir.path().join("models-store.json"));
        let entry = ModelsStoreEntry {
            checked_at: Some(1_700_000_000_000.0),
            ..ModelsStoreEntry::default()
        };
        let store_options = ModelsStoreOperationOptions::default;
        assert_eq!(store.read("p", store_options()).await.unwrap(), None);
        store
            .write("p", entry.clone(), store_options())
            .await
            .unwrap();
        assert_eq!(store.read("p", store_options()).await.unwrap(), Some(entry));
        store.delete("p", store_options()).await.unwrap();
        assert_eq!(store.read("p", store_options()).await.unwrap(), None);
    }
}
