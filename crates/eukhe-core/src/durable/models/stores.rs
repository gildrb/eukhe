//! The persistent credential store of the durable model collection: the
//! pi-ai [`CredentialStore`] over eukhe's `auth.json`, through eukhe's locked
//! file backend. The `auth.json` format mapping is documented on the parent
//! module.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::auth::{
    ApiKeyCredential, ApiKeyType, AuthOperationOptions, AuthType, Credential, CredentialInfo,
    CredentialStore, ModifyFn, OAuthCredential,
};
use eukhe_ai::utils::abort::{operation_signal, race_with_abort_signal};
use eukhe_ai::utils::diagnostics::{ErrorObject, Thrown};
use eukhe_bend::rules::config;
use eukhe_types::pi_ai::ProviderEnv;
use futures::future::BoxFuture;
use serde::Deserialize;
use serde_json::{Map, Value};

use super::accounts::{read_credential, AccountBook};
use crate::auth::accounts::{
    accounts_of, entry_of, keeps_accounts, with_account, with_credential, Account,
};
use crate::auth::resolve_config_value::resolve_config_value;
use crate::auth::{
    edit_storage_data, parse_storage_data, AuthStorageBackend, FileAuthStorageBackend,
};

pub(super) fn thrown(message: String) -> Thrown {
    ErrorObject::new(message).thrown()
}

/// Why the `auth.json` document could not be read or updated.
#[derive(Debug, thiserror::Error)]
pub(super) enum AuthDocumentError {
    /// The document could not be read (the whole cause chain renders).
    #[error("Failed to read {0:#}")]
    Read(#[source] anyhow::Error),
    /// The document is not a JSON object document.
    #[error("Failed to parse the document: {0:#}")]
    Parse(#[source] anyhow::Error),
    /// The locked read-modify-write failed.
    #[error("{0:#}")]
    Update(#[source] anyhow::Error),
    /// The lock ran without running the update.
    #[error("the locked update did not run")]
    UpdateNotRun,
}

/// Why the `auth.json` credential store failed. pi-ai's store contract
/// throws a JS-shaped error: the [`Thrown`] conversion renders this text
/// once, as the error object's message.
#[derive(Debug, thiserror::Error)]
pub(super) enum AuthJsonError {
    #[error("auth.json: {0}")]
    Document(#[from] AuthDocumentError),
    /// A stored entry does not have the credential shape.
    #[error("Invalid auth.json credential for provider \"{provider}\"")]
    InvalidCredential { provider: String },
    /// A stored entry's field does not decode.
    #[error("Invalid auth.json credential for provider \"{provider}\": {source}")]
    InvalidCredentialField {
        provider: String,
        #[source]
        source: serde_json::Error,
    },
    /// A credential did not serialize into its entry.
    #[error("{0}")]
    Serialize(#[source] serde_json::Error),
    /// The blocking file task was cancelled.
    #[error("file access task stopped: {0}")]
    TaskStopped(#[source] tokio::task::JoinError),
}

impl From<AuthJsonError> for Thrown {
    fn from(error: AuthJsonError) -> Self {
        thrown(error.to_string())
    }
}

/// Runs eukhe's synchronous file protocol (and `!command` key resolution)
/// off the async workers.
pub(super) async fn blocking<T, F>(task: F) -> Result<T, Thrown>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, AuthJsonError> + Send + 'static,
{
    match tokio::task::spawn_blocking(task).await {
        Ok(result) => result.map_err(Thrown::from),
        Err(error) if error.is_panic() => std::panic::resume_unwind(error.into_panic()),
        Err(error) => Err(AuthJsonError::TaskStopped(error).into()),
    }
}

/// The parsed JSON object document behind `backend` (`{}` when empty).
fn read_document(
    backend: &FileAuthStorageBackend,
) -> Result<Map<String, Value>, AuthDocumentError> {
    let content = backend.read().map_err(AuthDocumentError::Read)?;
    parse_storage_data(content.as_deref())
        .map(|data| data.0)
        .map_err(AuthDocumentError::Parse)
}

/// Locked read-modify-write of the document. `update` sees the parsed
/// document (an empty one when the file is missing or does not parse) and
/// returns the edit of one entry it makes, if any; the compiled core
/// decides what to write ([`edit_storage_data`]).
fn update_document<T>(
    backend: &FileAuthStorageBackend,
    mut update: impl FnMut(&Map<String, Value>) -> (Option<config::Edit<String, Value>>, T),
) -> Result<T, AuthDocumentError> {
    let mut outcome = None;
    backend
        .with_lock(&mut |current| {
            let data = edit_storage_data(current.as_deref(), |data| {
                let (edit, value) = update(&data.0);
                outcome = Some(value);
                edit
            })?;
            let content = data
                .map(|data| serde_json::to_string_pretty(&data.0))
                .transpose()?;
            Ok(((), content))
        })
        .map_err(AuthDocumentError::Update)?;
    outcome.ok_or(AuthDocumentError::UpdateNotRun)
}

/// pi-ai [`CredentialStore`] over eukhe's `auth.json`, for one session: a
/// provider's credential is the account the session sticks to
/// ([`AccountBook`]), else its first. Writes are serialized per provider
/// in-process; the file protocol serializes them across processes.
pub(super) struct AuthJsonCredentialStore {
    book: Arc<AccountBook>,
    chains: Mutex<HashMap<String, Arc<tokio::sync::Mutex<()>>>>,
}

impl AuthJsonCredentialStore {
    pub(super) fn new(book: Arc<AccountBook>) -> Self {
        Self {
            book,
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
        let backend = Arc::clone(self.book.backend());
        blocking(move || Ok(read_document(&backend)?)).await
    }
}

/// The credential this session reads for `provider_id` from its entry
/// (the pinned account's, else the first account's; an MCP server's own),
/// with the account's identity.
fn session_credential(
    book: &AccountBook,
    provider_id: &str,
    entry: Option<&Value>,
) -> Option<(String, Value)> {
    read_credential(book, provider_id, entry?)
        .map(|(identity, credential)| (identity, Value::Object(credential)))
}

/// The provider's entry with the credential of the account `identity`
/// replaced by `next` (the entry itself for an MCP server; a new account
/// when the provider has none).
fn entry_with(provider_id: &str, entry: Option<&Value>, identity: &str, next: Value) -> Value {
    let object = match next {
        Value::Object(object) if keeps_accounts(provider_id) => object,
        other => return other,
    };
    let accounts = entry
        .map(|entry| accounts_of(provider_id, entry))
        .unwrap_or_default();
    if accounts.iter().any(|account| account.identity == identity) {
        entry_of(&with_credential(accounts, identity, object))
    } else {
        entry_of(&with_account(accounts, Account::new(provider_id, object)))
    }
}

fn invalid_credential(provider_id: &str) -> AuthJsonError {
    AuthJsonError::InvalidCredential {
        provider: provider_id.to_owned(),
    }
}

/// An auth.json entry as a pi-ai credential (format mapping only). `None`
/// for eukhe-only credential types.
fn stored_credential(
    provider_id: &str,
    value: &Value,
) -> Result<Option<Credential>, AuthJsonError> {
    let Some(object) = value.as_object() else {
        return Err(invalid_credential(provider_id));
    };
    match stored_type(value) {
        Some(StoredType::ApiKey) => {
            let key = match object.get("key") {
                None => None,
                Some(Value::String(key)) => Some(key.clone()),
                Some(_) => return Err(invalid_credential(provider_id)),
            };
            let env: Option<ProviderEnv> = match object.get("env") {
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
            Ok(Some(Credential::ApiKey(ApiKeyCredential {
                kind: ApiKeyType::ApiKey,
                key,
                env,
            })))
        }
        Some(StoredType::OAuth) => OAuthCredential::deserialize(value)
            .map(|credential| Some(Credential::OAuth(credential)))
            .map_err(|source| AuthJsonError::InvalidCredentialField {
                provider: provider_id.to_owned(),
                source,
            }),
        None => Ok(None),
    }
}

/// The credential type an auth.json entry stores; `None` for eukhe-only
/// types (`mcp_static_token`, ...) and entries without one.
#[derive(Clone, Copy)]
enum StoredType {
    ApiKey,
    OAuth,
}

fn stored_type(entry: &Value) -> Option<StoredType> {
    match entry.get("type")?.as_str()? {
        "api_key" => Some(StoredType::ApiKey),
        "oauth" => Some(StoredType::OAuth),
        _ => None,
    }
}

/// eukhe's read-time resolution of a stored credential: the
/// configured-value resolution of the key.
fn resolve_stored_credential(credential: Credential) -> Credential {
    let Credential::ApiKey(mut credential) = credential else {
        return credential;
    };
    credential.key = credential.key.as_deref().and_then(resolve_config_value);
    Credential::ApiKey(credential)
}

/// A pi-ai credential as its auth.json entry.
fn credential_entry(credential: &Credential) -> Result<Value, AuthJsonError> {
    match credential {
        Credential::OAuth(credential) => {
            serde_json::to_value(credential).map_err(AuthJsonError::Serialize)
        }
        Credential::ApiKey(credential) => {
            let mut entry = Map::new();
            entry.insert("type".to_owned(), Value::String("api_key".to_owned()));
            if let Some(key) = &credential.key {
                entry.insert("key".to_owned(), Value::String(key.clone()));
            }
            if let Some(env) = credential.env.as_ref().filter(|env| !env.is_empty()) {
                entry.insert(
                    "env".to_owned(),
                    serde_json::to_value(env).map_err(AuthJsonError::Serialize)?,
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
            let Some((_, entry)) =
                session_credential(&self.book, provider_id, document.get(provider_id))
            else {
                return Ok(None);
            };
            let Some(credential) = stored_credential(provider_id, &entry)? else {
                return Ok(None);
            };
            // A `!command` key runs a process: off the async workers.
            blocking(move || Ok(Some(resolve_stored_credential(credential)))).await
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
                    let (_, entry) = session_credential(&self.book, provider_id, Some(entry))?;
                    let kind = match stored_type(&entry)? {
                        StoredType::ApiKey => AuthType::ApiKey,
                        StoredType::OAuth => AuthType::OAuth,
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
        let book = Arc::clone(&self.book);
        let id = provider_id.to_owned();
        let task_signal = signal.clone();
        let task = async move {
            let _turn = chain.lock_owned().await;
            task_signal.throw_if_aborted()?;
            // The document's refresh lock, held until the change is stored:
            // a peer process changing this document's credentials (an OAuth
            // refresh) is waited for, and the read below sees what it
            // stored, so `f` refreshes only a credential still expired.
            let lock_backend = Arc::clone(book.backend());
            let _refresh = blocking(move || {
                lock_backend
                    .refresh_lock()
                    .map_err(|error| AuthJsonError::Document(AuthDocumentError::Update(error)))
            })
            .await?;
            task_signal.throw_if_aborted()?;
            let read_backend = Arc::clone(book.backend());
            let document = blocking(move || Ok(read_document(&read_backend)?)).await?;
            // The account this session reads: a refresh rewrites only it.
            let previous = session_credential(&book, &id, document.get(&id));
            let current = match &previous {
                Some((_, entry)) => stored_credential(&id, entry)?,
                None => None,
            };
            // `f` (an OAuth refresh: a network round trip) runs outside the
            // document lock, like eukhe's load-then-lock refresh.
            let Some(next) = f(current.clone()).await? else {
                return Ok(current);
            };
            task_signal.throw_if_aborted()?;
            let entry = credential_entry(&next)?;
            // An entry that stays as stored (a failed refresh that keeps
            // the stored login) is not written back.
            if previous
                .as_ref()
                .is_some_and(|(_, stored)| *stored == entry)
            {
                return Ok(Some(next));
            }
            let write_id = id.clone();
            let write_book = Arc::clone(&book);
            let concurrent = blocking(move || {
                Ok(update_document(write_book.backend(), |document| {
                    let now = session_credential(&write_book, &write_id, document.get(&write_id));
                    let identity = previous
                        .as_ref()
                        .map(|(identity, _)| identity.clone())
                        .unwrap_or_default();
                    let unchanged = match (&now, &previous) {
                        (Some((_, now)), Some((_, previous))) => now == previous,
                        (None, None) => true,
                        (Some(_), None) | (None, Some(_)) => false,
                    };
                    if !unchanged {
                        // Another writer changed the account while `f` ran
                        // (a peer's refresh): its newer credential stands.
                        return (None, Some(now.map(|(_, entry)| entry)));
                    }
                    let written =
                        entry_with(&write_id, document.get(&write_id), &identity, entry.clone());
                    (Some(config::Edit::Set(write_id.clone(), written)), None)
                })?)
            })
            .await?;
            match concurrent {
                None => Ok(Some(next)),
                Some(None) => Ok(None),
                Some(Some(entry)) => Ok(stored_credential(&id, &entry)?),
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
        let book = Arc::clone(&self.book);
        let id = provider_id.to_owned();
        let task_signal = signal.clone();
        let task = async move {
            let _turn = chain.lock_owned().await;
            task_signal.throw_if_aborted()?;
            blocking(move || {
                Ok(update_document(book.backend(), |document| {
                    // The session's account goes; the entry goes with its
                    // last account.
                    let Some(entry) = document.get(&id) else {
                        return (None, ());
                    };
                    let Some((identity, _)) = session_credential(&book, &id, Some(entry)) else {
                        return (Some(config::Edit::Delete(id.clone())), ());
                    };
                    let rest: Vec<Account> = accounts_of(&id, entry)
                        .into_iter()
                        .filter(|account| account.identity != identity)
                        .collect();
                    let edit = if keeps_accounts(&id) && !rest.is_empty() {
                        config::Edit::Set(id.clone(), entry_of(&rest))
                    } else {
                        config::Edit::Delete(id.clone())
                    };
                    (Some(edit), ())
                })?)
            })
            .await
        };
        Box::pin(async move { race_with_abort_signal(task, &signal).await })
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use serde_json::json;

    use super::*;
    use crate::auth::{AuthCredential, AuthStorageData};

    fn store_at(path: &Path) -> AuthJsonCredentialStore {
        AuthJsonCredentialStore::new(Arc::new(AccountBook::new(path)))
    }

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
            // An earlier release's entry with a field this build does not
            // read.
            "retired": {
                "type": "api_key", "key": "pit-key",
                "team": { "teamId": "team-1", "name": "Team One" }
            },
            "mcp:linear": {
                "type": "mcp_static_token", "bearer": "lin-token",
                "endpoint": "https://mcp.linear.app"
            },
            "zai": { "type": "api_key", "key": "zai-key" }
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
        let store = store_at(&path);

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
            read("retired").await.unwrap(),
            Some(Credential::ApiKey(ApiKeyCredential::with_key("pit-key")))
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
                ("retired", AuthType::ApiKey),
                ("zai", AuthType::ApiKey),
            ]
            .map(|(provider_id, kind)| CredentialInfo {
                provider_id: provider_id.to_owned(),
                kind,
            })
        );

        // An OAuth refresh rewrites only its entry, as its one account.
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
            json!({ "accounts": [{
                "type": "oauth", "refresh": "rt-new", "access": "sk-ant-oat-new",
                "expires": 1_800_000_000_000_u64
            }] }),
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

        // Re-saving that key drops the field this build does not read.
        let retired = store.read("retired", options()).await.unwrap();
        store
            .modify("retired", replace_with(retired), options())
            .await
            .unwrap();
        assert_eq!(
            read_json(&path)["retired"],
            json!({ "accounts": [{ "type": "api_key", "key": "pit-key", "identity": "key" }] })
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
        let store = store_at(&path);
        let peer_path = path.clone();
        let modify: ModifyFn = Box::new(move |_current| {
            Box::pin(async move {
                // A peer process refreshes while this refresh runs.
                update_document(&FileAuthStorageBackend::new(&peer_path), |_| {
                    let peer = json!({
                        "type": "oauth", "access": "peer-access", "refresh": "peer-refresh",
                        "expires": 1_900_000_000_000_u64
                    });
                    (Some(config::Edit::Set("anthropic".to_owned(), peer)), ())
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

    /// Regression (`AttentionMeasure` re-measure, six processes on one
    /// auth.json): stores over one document, one per process, that find
    /// its OAuth credential expired at once refresh it once. Each other
    /// store waits for the refresh lock, re-reads the document, finds the
    /// fresh token and serves it.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn concurrent_refreshers_of_one_document_refresh_once() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("auth.json");
        write_json(&path, &todays_auth_json());
        let refreshes = Arc::new(AtomicUsize::new(0));
        let fresh = OAuthCredential::new("rt-new", "sk-ant-oat-new", 4_102_444_800_000.0);
        let processes: Vec<_> = (0..6)
            .map(|_| {
                let store = store_at(&path);
                let refreshes = Arc::clone(&refreshes);
                let fresh = fresh.clone();
                tokio::spawn(async move {
                    let refresh: ModifyFn = Box::new(move |current| {
                        Box::pin(async move {
                            let Some(Credential::OAuth(current)) = current else {
                                return Ok(None);
                            };
                            if current.expires > 1_800_000_000_000.0 {
                                return Ok(None);
                            }
                            refreshes.fetch_add(1, Ordering::SeqCst);
                            // The token fetch's network round trip.
                            tokio::time::sleep(std::time::Duration::from_millis(100)).await;
                            Ok(Some(Credential::OAuth(fresh)))
                        })
                    });
                    store.modify("anthropic", refresh, options()).await
                })
            })
            .collect();
        for process in processes {
            assert_eq!(
                process.await.unwrap().unwrap(),
                Some(Credential::OAuth(fresh.clone()))
            );
        }
        assert_eq!(refreshes.load(Ordering::SeqCst), 1);
    }

    /// A refresh that failed keeps the stored login (the provider
    /// runtime's login watch answers the stored credential): nothing is
    /// written, so a shared document is not rewritten by every request of
    /// a run whose login expired.
    #[tokio::test]
    async fn an_unchanged_credential_is_not_written_back() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("auth.json");
        write_json(&path, &todays_auth_json());
        let before = std::fs::read_to_string(&path).unwrap();
        let keep: ModifyFn = Box::new(|current| Box::pin(async move { Ok(current) }));
        let kept = store_at(&path)
            .modify("anthropic", keep, options())
            .await
            .unwrap();
        assert_eq!(
            (kept.is_some(), std::fs::read_to_string(&path).unwrap()),
            (true, before)
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
        let error = store_at(&path).read("xai", options()).await.unwrap_err();
        assert!(
            error
                .to_string()
                .starts_with("Invalid auth.json credential for provider \"xai\""),
            "{error}"
        );
    }

    #[test]
    fn update_document_refuses_an_unreadable_or_invalid_document() {
        use std::os::unix::fs::PermissionsExt;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("auth.json");
        let backend = FileAuthStorageBackend::new(&path);
        let add_b = |_: &Map<String, Value>| {
            let entry = json!({ "type": "api_key", "key": "kb" });
            (Some(config::Edit::Set("b".to_owned(), entry)), ())
        };
        // Invalid JSON: refused, the file is unchanged.
        let broken = r#"{ "a": { "type": "api_key", "key": "ka" },"#;
        std::fs::write(&path, broken).unwrap();
        assert_eq!(
            (
                update_document(&backend, add_b).is_err(),
                std::fs::read_to_string(&path).unwrap()
            ),
            (true, broken.to_owned())
        );
        // An unreadable file: refused with the read error, the file is
        // unchanged.
        let document = r#"{ "a": { "type": "api_key", "key": "ka" } }"#;
        std::fs::write(&path, document).unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o000)).unwrap();
        let Err(read_error) = std::fs::read(&path) else {
            eprintln!("skipped: this user (root) can read a 000 file");
            return;
        };
        let result = update_document(&backend, add_b).map_err(|error| error.to_string());
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).unwrap();
        assert_eq!(
            (result, std::fs::read_to_string(&path).unwrap()),
            (
                Err(format!("Failed to read {}: {read_error}", path.display())),
                document.to_owned()
            )
        );
    }
}
