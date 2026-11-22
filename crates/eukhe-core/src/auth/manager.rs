//! `AuthStorage`: credential resolution with runtime overrides, environment
//! keys, stored credentials, fallback resolvers, and stale-marking. Port of
//! the `AuthStorage` class.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::sync::Arc;

use eukhe_bend::rules::config;

use super::accounts::{
    entry_of, keeps_accounts, migrated_entries, with_account, Account, AccountSelector,
};
use super::refresh_error::{OAuthRefreshError, RefreshFailed};
use super::resolve_config_value::{resolve_config_value, resolve_config_value_uncached};
use super::storage::{edit_storage_data, parse_storage_data, AuthStorageBackend};
use super::types::{AuthCredential, AuthSource, AuthSourceToken, AuthStatus, AuthStorageData};

// The inline unit battery moved to the child module at the same tree
// position (auth::manager::tests); its use-super glob keeps resolving
// through the facade bindings and re-exports (the manager stage-1
// precedent, #3039).
#[cfg(test)]
mod tests;

// The API-key lookup + OAuth refresh arm (get_api_key_with_source_token,
// get_api_key, refresh_oauth) moved to the child module at the same tree
// position (auth::manager::lookup) as its own impl AuthStorage block -
// inherent impls split freely; the pub methods stay on the facade-
// resident type (external callers resolve through the type);
// refresh_oauth keeps its private level (the lookup child is its only
// caller - zero pub(super) bumps, verified by the caller map); the
// child's bare calls into the facade's candidate/staleness machinery
// resolve through the use-super glob (the descendant visibility rule).
mod lookup;

/// SHA-256 fingerprint of an auth-source material, `source:hex` form.
fn fingerprint(source: AuthSource, material: &str) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(format!("{source:?}"));
    hasher.update([0]);
    hasher.update(material.as_bytes());
    format!("{source:?}:{}", hex(&hasher.finalize()))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().fold(String::new(), |mut output, b| {
        let _ = write!(output, "{b:02x}");
        output
    })
}

/// Wall-clock milliseconds since the epoch (auth expiry comparison).
fn now_epoch_ms() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(i64::MAX, |d| d.as_millis() as i64)
}

/// One candidate credential source.
#[derive(Clone)]
struct AuthSourceCandidate {
    source: AuthSource,
    configured: bool,
    label: Option<String>,
    identity_fingerprint: String,
    value_fingerprint: Option<String>,
    /// Deferred value material (commands that must run at read time).
    resolve_value_fingerprint: Option<ValueFingerprintResolver>,
}

impl AuthSourceCandidate {
    fn resolved_value_fingerprint(&self) -> Option<String> {
        self.value_fingerprint
            .clone()
            .or_else(|| self.resolve_value_fingerprint.as_ref().and_then(|f| f()))
    }
}

/// The result of an API-key lookup.
#[derive(Debug, Default, Clone)]
pub struct AuthApiKeyResult {
    pub api_key: Option<String>,
    pub source_token: Option<AuthSourceToken>,
    pub credential_type: Option<&'static str>,
    /// Why an expired OAuth credential resolved no key: the failed
    /// refresh's reason. The credential stays stored for a later
    /// `/login` retry.
    pub refresh_error: Option<RefreshFailed>,
}

/// OAuth integration seam: the eukhe-ai oauth provider registry implements this
/// (login flow + token refresh). Kept as a trait so auth storage stays
/// testable without network flows.
pub trait OAuthIntegration: Send + Sync {
    /// The resolved API key for stored OAuth credentials (bearer/token form).
    fn api_key_for(&self, provider_id: &str, credential: &AuthCredential) -> Option<String>;
    /// Refresh an expired credential.
    ///
    /// # Errors
    ///
    /// Returns why no fresh credential came back: the token endpoint's
    /// answer, a transport failure, or no refresh flow for the provider.
    fn refresh(
        &self,
        provider_id: &str,
        credentials: &AuthStorageData,
    ) -> Result<AuthCredential, OAuthRefreshError>;
}

/// No OAuth provider registry available (embedded hosts); stored OAuth
/// credentials still serve their access token until expiry.
#[derive(Default)]
pub struct NoOAuth;

impl OAuthIntegration for NoOAuth {
    fn api_key_for(&self, _provider: &str, credential: &AuthCredential) -> Option<String> {
        match credential {
            AuthCredential::Oauth { access, .. } => Some(access.clone()),
            _ => None,
        }
    }

    fn refresh(
        &self,
        provider: &str,
        _credentials: &AuthStorageData,
    ) -> Result<AuthCredential, OAuthRefreshError> {
        Err(OAuthRefreshError::NoIntegration {
            provider: provider.to_string(),
        })
    }
}

/// Environment credential source: the seam through which auth resolution
/// reads ambient credentials (provider API-key variables and
/// multi-variable ambient identity material such as AWS
/// profiles). The production implementation reads the real process
/// environment via the shared env-var table in `eukhe-ai`; tests inject a fixed
/// mapping so resolution order is deterministic and hermetic against
/// ambient variables and parallel-test env mutation.
pub(crate) trait EnvCredentialSource: Send + Sync {
    /// Env var names (priority order) currently set to non-empty values that
    /// would supply the provider's API key, if any.
    fn key_names(&self, provider: &str) -> Option<Vec<String>>;
    /// The provider's API key from the environment, if any.
    fn api_key(&self, provider: &str) -> Option<String>;
    /// Identity material for ambient multi-variable credential sources
    /// (AWS profiles, container credentials, Google ADC projects).
    fn ambient_identity_material(&self, provider: &str) -> String;
}

/// Process-environment credential source (production).
struct ProcessEnvCredentials;

/// No-op environment credential source: no ambient variable can supply a
/// provider key. The hermetic seam behind
/// [`AuthStorage::in_memory_without_env`].
struct NoEnvCredentials;

impl EnvCredentialSource for NoEnvCredentials {
    fn key_names(&self, _provider: &str) -> Option<Vec<String>> {
        None
    }

    fn api_key(&self, _provider: &str) -> Option<String> {
        None
    }

    fn ambient_identity_material(&self, provider: &str) -> String {
        provider.to_string()
    }
}

impl EnvCredentialSource for ProcessEnvCredentials {
    fn key_names(&self, provider: &str) -> Option<Vec<String>> {
        eukhe_ai::env_api_keys::find_env_keys(provider, None)
    }

    fn api_key(&self, provider: &str) -> Option<String> {
        eukhe_ai::env_api_keys::get_env_api_key(provider, None)
    }

    fn ambient_identity_material(&self, provider: &str) -> String {
        let env = |name: &str| std::env::var(name).unwrap_or_default();
        match provider {
            "amazon-bedrock" => {
                if !env("AWS_PROFILE").is_empty() {
                    return format!("amazon-bedrock:profile:{}", env("AWS_PROFILE"));
                }
                if !env("AWS_ACCESS_KEY_ID").is_empty() {
                    return format!(
                        "amazon-bedrock:access-key:{}:{}:{}",
                        env("AWS_ACCESS_KEY_ID"),
                        env("AWS_SECRET_ACCESS_KEY"),
                        env("AWS_SESSION_TOKEN")
                    );
                }
                if !env("AWS_BEARER_TOKEN_BEDROCK").is_empty() {
                    return format!("amazon-bedrock:bearer:{}", env("AWS_BEARER_TOKEN_BEDROCK"));
                }
                for (name, prefix) in [
                    ("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI", "ecs-relative"),
                    ("AWS_CONTAINER_CREDENTIALS_FULL_URI", "ecs-full"),
                    ("AWS_WEB_IDENTITY_TOKEN_FILE", "web-identity"),
                ] {
                    if !env(name).is_empty() {
                        return format!("amazon-bedrock:{prefix}:{}", env(name));
                    }
                }
                provider.to_string()
            }
            "google-vertex" => format!(
                "google-vertex:{}:{}:{}",
                if env("GOOGLE_CLOUD_PROJECT").is_empty() {
                    env("GCLOUD_PROJECT")
                } else {
                    env("GOOGLE_CLOUD_PROJECT")
                },
                env("GOOGLE_CLOUD_LOCATION"),
                if env("GOOGLE_APPLICATION_CREDENTIALS").is_empty() {
                    "application-default".to_string()
                } else {
                    env("GOOGLE_APPLICATION_CREDENTIALS")
                }
            ),
            other => other.to_string(),
        }
    }
}

/// Fallback key resolver (custom provider configs).
pub type FallbackResolver = Arc<dyn Fn(&str) -> Option<String> + Send + Sync>;

/// Deferred value-fingerprint resolver (command keys).
type ValueFingerprintResolver = Arc<dyn Fn() -> Option<String> + Send + Sync>;

/// Why the auth document did not load (its whole cause chain renders).
#[derive(Debug, Clone, thiserror::Error)]
#[error("{0:#}")]
pub struct AuthLoadError(#[source] Arc<anyhow::Error>);

/// An auth document write that did not happen. Nothing was written.
#[derive(Debug, thiserror::Error)]
#[error("Failed to write {location}: {cause}")]
pub struct AuthWriteError {
    /// The auth document: its file path, or a label for a backend without a file.
    pub location: String,
    /// Why the write did not happen.
    #[source]
    pub cause: AuthWriteCause,
}

/// Why an auth document write did not happen.
#[derive(Debug, thiserror::Error)]
pub enum AuthWriteCause {
    /// The credential did not serialize.
    #[error("{0}")]
    Serialize(#[source] serde_json::Error),
    /// The document failed to load, and the core refuses the edit over a
    /// broken read.
    #[error("the document failed to load: {0}")]
    Unloaded(#[source] AuthLoadError),
    /// The locked read-modify-write failed (its whole cause chain renders).
    #[error("{0:#}")]
    Write(#[source] anyhow::Error),
}

/// A failure the storage reports on its errors channel
/// ([`AuthStorage::drain_errors`]): a failed load.
#[derive(Debug, thiserror::Error)]
pub enum AuthStorageError {
    #[error(transparent)]
    Load(AuthLoadError),
}

pub struct AuthStorage {
    storage: Arc<dyn AuthStorageBackend>,
    oauth: Arc<dyn OAuthIntegration>,
    env_credentials: Arc<dyn EnvCredentialSource>,
    data: AuthStorageData,
    runtime_overrides: HashMap<String, String>,
    stale_auth_sources: HashMap<String, Vec<AuthSourceToken>>,
    fallback_resolver: Option<FallbackResolver>,
    load_error: Option<AuthLoadError>,
    errors: Vec<AuthStorageError>,
    /// Memoized auth-source candidates (TS #2479's `authCandidateMemos`),
    /// keyed by `source:provider`, superseded exactly when the candidate's
    /// hashed material changes. Reuse skips only the SHA-256 work: the
    /// material itself (env reads, stored-value resolution, the fallback
    /// resolver) is recomputed on every call, and stale checks run against
    /// the memoized candidate — candidates are immutable.
    candidate_memos: std::sync::Mutex<HashMap<String, (String, AuthSourceCandidate)>>,
}

impl AuthStorage {
    pub fn from_storage(
        storage: Arc<dyn AuthStorageBackend>,
        oauth: Arc<dyn OAuthIntegration>,
    ) -> Self {
        let mut auth = Self {
            storage,
            oauth,
            env_credentials: Arc::new(ProcessEnvCredentials),
            data: AuthStorageData::default(),
            runtime_overrides: HashMap::new(),
            stale_auth_sources: HashMap::new(),
            fallback_resolver: None,
            load_error: None,
            errors: Vec::new(),
            candidate_memos: std::sync::Mutex::new(HashMap::new()),
        };
        auth.reload();
        auth
    }

    /// File-backed storage at `agentDir/auth.json`.
    pub fn create(agent_dir: impl AsRef<std::path::Path>) -> Self {
        // The built-in subscription providers' integration (the codex
        // refresh): the TS storage delegates to the AI library's oauth
        // registry on every instance, and `api_key_for` matches `NoOAuth`
        // (the access token passthrough), so only token refresh gains.
        Self::create_with_oauth(
            agent_dir,
            Arc::new(super::provider_oauth::ProviderOAuth::new()),
        )
    }

    /// File-backed storage with an explicit OAuth integration (the MCP
    /// manager uses this so stored `mcp:*` tokens refresh on expiry).
    pub fn create_with_oauth(
        agent_dir: impl AsRef<std::path::Path>,
        oauth: Arc<dyn OAuthIntegration>,
    ) -> Self {
        let backend: Arc<dyn AuthStorageBackend> =
            Arc::new(super::storage::FileAuthStorageBackend::new(
                agent_dir.as_ref().join(super::storage::AUTH_FILE_NAME),
            ));
        Self::from_storage(backend, oauth)
    }

    pub fn in_memory(data: &AuthStorageData, oauth: Arc<dyn OAuthIntegration>) -> Self {
        Self::in_memory_with_env_source(data, oauth, Arc::new(ProcessEnvCredentials))
    }

    /// In-memory storage with no ambient environment source: hermetic
    /// resolution for embedded hosts and test harnesses that must pin the
    /// model catalog scope (an ambient provider credential variable cannot
    /// make models available through this storage). Otherwise behaves
    /// like [`AuthStorage::in_memory`].
    pub fn in_memory_without_env(data: &AuthStorageData, oauth: Arc<dyn OAuthIntegration>) -> Self {
        Self::in_memory_with_env_source(data, oauth, Arc::new(NoEnvCredentials))
    }

    /// In-memory storage with an injected environment source: hermetic
    /// resolution for tests and embedded hosts (no ambient env reads).
    #[cfg(test)]
    pub(crate) fn in_memory_with_env(
        data: &AuthStorageData,
        oauth: Arc<dyn OAuthIntegration>,
        env_credentials: Arc<dyn EnvCredentialSource>,
    ) -> Self {
        Self::in_memory_with_env_source(data, oauth, env_credentials)
    }

    fn in_memory_with_env_source(
        data: &AuthStorageData,
        oauth: Arc<dyn OAuthIntegration>,
        env_credentials: Arc<dyn EnvCredentialSource>,
    ) -> Self {
        let backend: Arc<dyn AuthStorageBackend> =
            Arc::new(crate::auth::storage::InMemoryAuthStorageBackend::default());
        let content = serde_json::to_string_pretty(&data.0).unwrap_or_default();
        backend
            .with_lock(&mut |current| {
                let _ = current;
                Ok(((), Some(content.clone())))
            })
            .ok();
        let mut auth = Self {
            storage: backend,
            oauth,
            env_credentials,
            data: AuthStorageData::default(),
            runtime_overrides: HashMap::new(),
            stale_auth_sources: HashMap::new(),
            fallback_resolver: None,
            load_error: None,
            errors: Vec::new(),
            candidate_memos: std::sync::Mutex::new(HashMap::new()),
        };
        auth.reload();
        auth
    }

    pub fn load_error(&self) -> Option<&AuthLoadError> {
        self.load_error.as_ref()
    }

    pub fn drain_errors(&mut self) -> Vec<AuthStorageError> {
        std::mem::take(&mut self.errors)
    }

    /// Reload credentials from storage. A document with entries written
    /// before accounts is rewritten with each as a one-account list, in
    /// one locked write ([`migrated_entries`]).
    pub fn reload(&mut self) {
        // The pure-read arm: a locked protocol read on any cache miss, the
        // process-cached copy on a hit (see `AuthStorageBackend::read`).
        let result = self.storage.read();
        match result.and_then(|content| parse_storage_data(content.as_deref())) {
            Ok(data) => {
                self.data = if migrated_entries(&data.0).is_empty() {
                    data
                } else {
                    self.migrate().unwrap_or(data)
                };
                self.load_error = None;
            }
            Err(error) => {
                let error = AuthLoadError(Arc::new(error));
                self.load_error = Some(error.clone());
                self.errors.push(AuthStorageError::Load(error));
            }
        }
    }

    /// Rewrite every entry written before accounts as a one-account list
    /// (under the document lock, so a peer's write in between stands) and
    /// answer the document written; `None` when the write fails (the
    /// entries still read as one account each).
    fn migrate(&self) -> Option<AuthStorageData> {
        let mut written = None;
        self.storage
            .with_lock(&mut |current| {
                let mut content = current;
                let document = parse_storage_data(content.as_deref())?;
                for (provider, entry) in migrated_entries(&document.0) {
                    let edited = edit_storage_data(content.as_deref(), |_| {
                        Some(config::Edit::Set(provider.clone(), entry.clone()))
                    })?;
                    if let Some(edited) = edited {
                        content = Some(serde_json::to_string_pretty(&edited.0)?);
                    }
                }
                written = Some(parse_storage_data(content.as_deref())?);
                Ok(((), content))
            })
            .ok()?;
        written
    }

    /// Runtime API-key override (CLI `--api-key`); not persisted.
    pub fn set_runtime_api_key(&mut self, provider: &str, api_key: String) {
        self.clear_stale_auth_source(provider, AuthSource::Runtime);
        self.runtime_overrides.insert(provider.to_string(), api_key);
    }

    pub fn remove_runtime_api_key(&mut self, provider: &str) {
        self.clear_stale_auth_source(provider, AuthSource::Runtime);
        self.runtime_overrides.remove(provider);
    }

    /// Fallback resolver for keys from custom provider configs (models.json).
    pub fn set_fallback_resolver(&mut self, resolver: FallbackResolver) {
        self.fallback_resolver = Some(resolver);
    }

    // -- candidates ----------------------------------------------------------

    fn stored_value_material(&self, credential: &AuthCredential) -> Option<String> {
        match credential {
            AuthCredential::ApiKey { key, .. } => {
                if key.starts_with('!') {
                    let resolved = resolve_config_value_uncached(key)?;
                    Some(format!("api_key:command:{key}\0{resolved}"))
                } else {
                    Some(format!(
                        "api_key:{key}\0{}",
                        resolve_config_value(key).unwrap_or_default()
                    ))
                }
            }
            AuthCredential::Oauth {
                access,
                refresh,
                expires,
                ..
            } => {
                let api_key = self
                    .oauth
                    .api_key_for("", credential)
                    .unwrap_or_else(|| access.clone());
                Some(format!(
                    "oauth:{api_key}\0{}\0{expires}",
                    refresh.clone().unwrap_or_default()
                ))
            }
            AuthCredential::McpStaticToken { bearer, .. } => {
                Some(format!("mcp_static_token:{bearer}"))
            }
        }
    }

    /// Memo marker for candidates whose value material could not be
    /// resolved into a key (TS #2479's `AUTH_SOURCE_LAZY_VALUE_KEY`): the
    /// entry is keyed by everything else the candidate hashes.
    fn auth_source_lazy_value_key() -> &'static str {
        "value-lazy"
    }

    /// The memo reuse arm (TS #2479's `reuseAuthSourceCandidate`): the key
    /// is the hashed material itself, so the memo is superseded exactly
    /// when the material is.
    fn reuse_auth_source_candidate(
        &self,
        source: AuthSource,
        provider: &str,
        key: String,
        build: impl FnOnce() -> AuthSourceCandidate,
    ) -> AuthSourceCandidate {
        let memo_slot = format!("{source:?}:{provider}");
        let mut memos = self
            .candidate_memos
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some((memo_key, candidate)) = memos.get(&memo_slot) {
            if memo_key == &key {
                return candidate.clone();
            }
        }
        let candidate = build();
        memos.insert(memo_slot, (key, candidate.clone()));
        candidate
    }

    fn runtime_candidate(&self, provider: &str) -> Option<AuthSourceCandidate> {
        let key = self.runtime_overrides.get(provider)?.clone();
        Some(self.reuse_auth_source_candidate(
            AuthSource::Runtime,
            provider,
            key.clone(),
            move || AuthSourceCandidate {
                source: AuthSource::Runtime,
                configured: true,
                label: None,
                identity_fingerprint: fingerprint(AuthSource::Runtime, "identity:runtime-override"),
                value_fingerprint: Some(fingerprint(
                    AuthSource::Runtime,
                    &format!("value:runtime-override\0{key}"),
                )),
                resolve_value_fingerprint: None,
            },
        ))
    }

    fn stored_candidate(&self, provider: &str) -> Option<AuthSourceCandidate> {
        let credential = self.data.credential(provider)?;
        let value_material = self.stored_value_material(&credential);
        // The key is the hashed material itself (TS #2479: keyed by
        // credential fields, never object identity, so the key
        // changes exactly when the hashed material does).
        let key = format!(
            "identity:auth.json\0{}",
            value_material
                .as_deref()
                .unwrap_or(Self::auth_source_lazy_value_key()),
        );
        Some(
            self.reuse_auth_source_candidate(AuthSource::Stored, provider, key, || {
                AuthSourceCandidate {
                    source: AuthSource::Stored,
                    configured: true,
                    label: None,
                    identity_fingerprint: fingerprint(AuthSource::Stored, "identity:auth.json"),
                    value_fingerprint: value_material.map(|material| {
                        fingerprint(AuthSource::Stored, &format!("value:auth.json\0{material}"))
                    }),
                    resolve_value_fingerprint: None,
                }
            }),
        )
    }

    fn environment_candidate(&self, provider: &str) -> Option<AuthSourceCandidate> {
        let env_keys = self.env_credentials.key_names(provider);
        let api_key = self.env_credentials.api_key(provider)?;
        let label = env_keys
            .as_ref()
            .and_then(|keys| keys.first().cloned())
            .unwrap_or_else(|| "ambient credentials".to_string());
        let identity_material = env_keys
            .and_then(|keys| keys.first().cloned())
            .unwrap_or_else(|| self.env_credentials.ambient_identity_material(provider));
        // Env values are deliberately re-read on every call (TS
        // #2479); the memo only skips re-fingerprinting unchanged
        // material.
        let key = format!("{identity_material}\0{api_key}");
        Some(
            self.reuse_auth_source_candidate(AuthSource::Environment, provider, key, || {
                AuthSourceCandidate {
                    source: AuthSource::Environment,
                    configured: false,
                    label: Some(label),
                    identity_fingerprint: fingerprint(
                        AuthSource::Environment,
                        &format!("identity:{identity_material}"),
                    ),
                    value_fingerprint: Some(fingerprint(
                        AuthSource::Environment,
                        &format!("value:{identity_material}\0{api_key}"),
                    )),
                    resolve_value_fingerprint: None,
                }
            }),
        )
    }

    fn fallback_candidate(&self, provider: &str) -> Option<AuthSourceCandidate> {
        let resolver = self.fallback_resolver.as_ref()?;
        let api_key = resolver(provider)?;
        Some(self.reuse_auth_source_candidate(
            AuthSource::Fallback,
            provider,
            api_key.clone(),
            || AuthSourceCandidate {
                source: AuthSource::Fallback,
                configured: false,
                label: Some("custom provider config".to_string()),
                identity_fingerprint: fingerprint(
                    AuthSource::Fallback,
                    &format!("identity:{provider}"),
                ),
                value_fingerprint: Some(fingerprint(
                    AuthSource::Fallback,
                    &format!("value:{provider}\0{api_key}"),
                )),
                resolve_value_fingerprint: None,
            },
        ))
    }

    /// Candidate priority: runtime, stored, environment, fallback last.
    fn auth_source_candidates(
        &self,
        provider: &str,
        include_fallback: bool,
    ) -> Vec<AuthSourceCandidate> {
        let fallback = include_fallback
            .then(|| self.fallback_candidate(provider))
            .flatten();
        [
            self.runtime_candidate(provider),
            self.stored_candidate(provider),
            self.environment_candidate(provider),
            fallback,
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    fn matching_stale(
        &self,
        provider: &str,
        candidate: &AuthSourceCandidate,
    ) -> Vec<&AuthSourceToken> {
        self.stale_auth_sources
            .get(provider)
            .map(|stale| {
                stale
                    .iter()
                    .filter(|token| {
                        token.source == candidate.source
                            && token.identity_fingerprint == candidate.identity_fingerprint
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn is_stale(&self, provider: &str, candidate: &AuthSourceCandidate) -> bool {
        let matching = self.matching_stale(provider, candidate);
        if matching.is_empty() {
            return false;
        }
        candidate.resolved_value_fingerprint().is_some_and(|value| {
            matching
                .iter()
                .any(|token| token.value_fingerprint == value)
        })
    }

    fn available_candidate(
        &self,
        provider: &str,
        include_fallback: bool,
    ) -> Option<AuthSourceCandidate> {
        self.auth_source_candidates(provider, include_fallback)
            .into_iter()
            .find(|candidate| !self.is_stale(provider, candidate))
    }

    fn token_for(provider: &str, candidate: &AuthSourceCandidate) -> Option<AuthSourceToken> {
        Some(AuthSourceToken {
            provider: provider.to_string(),
            source: candidate.source,
            identity_fingerprint: candidate.identity_fingerprint.clone(),
            value_fingerprint: candidate.resolved_value_fingerprint()?,
        })
    }

    // -- public surface ------------------------------------------------------

    pub fn list(&self) -> Vec<String> {
        self.data.keys()
    }

    pub fn has(&self, provider: &str) -> bool {
        self.data.get(provider).is_some()
    }

    /// Any form of auth configured (never refreshes tokens).
    pub fn has_auth(&self, provider: &str) -> bool {
        self.available_candidate(provider, true).is_some()
    }

    /// Status without credential values.
    pub fn get_auth_status(&self, provider: &str) -> AuthStatus {
        let candidates = self.auth_source_candidates(provider, true);
        let mut has_stale = false;
        for candidate in &candidates {
            if self.is_stale(provider, candidate) {
                has_stale = true;
                continue;
            }
            return AuthStatus {
                configured: candidate.configured,
                source: Some(candidate.source),
                label: candidate.label.clone(),
            };
        }
        if has_stale {
            AuthStatus {
                configured: false,
                source: Some(AuthSource::Stale),
                label: Some("expired".to_string()),
            }
        } else {
            AuthStatus::default()
        }
    }

    pub fn get_all(&self) -> AuthStorageData {
        self.data.clone()
    }

    /// Mark the current credential stale (e.g. the server rejected it).
    pub fn mark_auth_stale(&mut self, provider: &str) -> bool {
        let Some(candidate) = self.available_candidate(provider, true) else {
            return false;
        };
        let Some(token) = Self::token_for(provider, &candidate) else {
            return false;
        };
        self.mark_auth_source_stale(token)
    }

    pub fn mark_auth_source_stale(&mut self, token: AuthSourceToken) -> bool {
        if token.provider.is_empty() {
            return false;
        }
        let stale = self
            .stale_auth_sources
            .entry(token.provider.clone())
            .or_default();
        if !stale.contains(&token) {
            stale.push(token);
        }
        true
    }

    /// Forget every stale marking for a provider.
    pub fn clear_auth_stale(&mut self, provider: &str) {
        self.stale_auth_sources.remove(provider);
    }

    fn clear_stale_auth_source(&mut self, provider: &str, source: AuthSource) {
        if let Some(stale) = self.stale_auth_sources.get_mut(provider) {
            stale.retain(|token| token.source != source);
            if stale.is_empty() {
                self.stale_auth_sources.remove(provider);
            }
        }
    }

    /// Store a credential as the provider's only account (an MCP server's
    /// one credential).
    ///
    /// # Errors
    ///
    /// Returns an error when the credential does not serialize, the auth
    /// document failed to load, cannot be read or parsed now, or cannot be
    /// written. Then nothing is written.
    pub fn set(
        &mut self,
        provider: &str,
        credential: AuthCredential,
    ) -> Result<(), AuthWriteError> {
        let object = self.credential_object(credential)?;
        let entry = if keeps_accounts(provider) {
            entry_of(&[Account::new(provider, object)])
        } else {
            serde_json::Value::Object(object)
        };
        self.persist_entry(provider, |_| Some(entry.clone()))
    }

    /// Add a login of `provider` as an account named `identity` (empty:
    /// the credential's own identity, [`super::accounts::identity_of`]):
    /// it replaces the account of the same identity, else it comes last
    /// and the others stay. Answers the account's label.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::set`].
    pub fn add_account(
        &mut self,
        provider: &str,
        credential: AuthCredential,
        identity: &str,
    ) -> Result<String, AuthWriteError> {
        let mut account = Account::new(provider, self.credential_object(credential)?);
        if !identity.is_empty() {
            identity.clone_into(&mut account.identity);
        }
        self.persist_entry(provider, |data| {
            Some(entry_of(&with_account(
                data.accounts(provider),
                account.clone(),
            )))
        })?;
        let place = self
            .data
            .accounts(provider)
            .iter()
            .position(|known| known.identity == account.identity)
            .map_or(1, |at| at + 1);
        Ok(account.label(place))
    }

    /// Remove one account of `provider`; the provider's entry goes with its
    /// last account. Answers the removed account's label, `None` when no
    /// account matches (nothing is written).
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::set`].
    pub fn remove_account(
        &mut self,
        provider: &str,
        selector: &AccountSelector,
    ) -> Result<Option<String>, AuthWriteError> {
        let accounts = self.data.accounts(provider);
        let Some(at) = selector.index(&accounts) else {
            return Ok(None);
        };
        let removed = accounts[at].clone();
        self.persist_entry(provider, |data| {
            let rest: Vec<Account> = data
                .accounts(provider)
                .into_iter()
                .filter(|account| account.identity != removed.identity)
                .collect();
            (!rest.is_empty()).then(|| entry_of(&rest))
        })?;
        Ok(Some(removed.label(at + 1)))
    }

    /// Remove a provider's stored credentials (every account).
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::set`].
    pub fn remove(&mut self, provider: &str) -> Result<(), AuthWriteError> {
        self.persist_entry(provider, |_| None)
    }

    /// Remove a provider's stored credentials (every account).
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::set`].
    pub fn logout(&mut self, provider: &str) -> Result<(), AuthWriteError> {
        self.remove(provider)
    }

    /// The stored object of `credential`.
    fn credential_object(
        &self,
        credential: AuthCredential,
    ) -> Result<serde_json::Map<String, serde_json::Value>, AuthWriteError> {
        match serde_json::to_value(credential) {
            Ok(serde_json::Value::Object(object)) => Ok(object),
            Ok(other) => Err(AuthWriteError {
                location: self.storage.location(),
                cause: AuthWriteCause::Serialize(<serde_json::Error as serde::de::Error>::custom(
                    format!("a credential serialized as {other}"),
                )),
            }),
            Err(error) => Err(AuthWriteError {
                location: self.storage.location(),
                cause: AuthWriteCause::Serialize(error),
            }),
        }
    }

    /// Write one provider's entry into the document as it is on disk now:
    /// `next` computes it from that document (`None`: the entry goes); the
    /// compiled core decides the write ([`edit_storage_data`]). The other
    /// entries keep their values. A document that failed to load reads as
    /// broken.
    fn persist_entry(
        &mut self,
        provider: &str,
        next: impl Fn(&AuthStorageData) -> Option<serde_json::Value>,
    ) -> Result<(), AuthWriteError> {
        if let Some(load_error) = &self.load_error {
            if config::rmw(
                config::Read::<String, serde_json::Value>::Broken,
                config::Edit::Delete(provider.to_string()),
            )
            .is_none()
            {
                return Err(AuthWriteError {
                    location: self.storage.location(),
                    cause: AuthWriteCause::Unloaded(load_error.clone()),
                });
            }
        }
        self.storage
            .with_lock(&mut |current| {
                let data = edit_storage_data(current.as_deref(), |data| {
                    Some(match next(data) {
                        Some(entry) => config::Edit::Set(provider.to_string(), entry),
                        None => config::Edit::Delete(provider.to_string()),
                    })
                })?;
                let content = data
                    .map(|data| serde_json::to_string_pretty(&data.0))
                    .transpose()?;
                Ok(((), content))
            })
            .map_err(|error| AuthWriteError {
                location: self.storage.location(),
                cause: AuthWriteCause::Write(error),
            })?;
        // Reload from what we wrote.
        self.reload();
        Ok(())
    }
}
