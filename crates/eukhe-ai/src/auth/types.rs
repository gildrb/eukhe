//! Auth vocabulary: credentials, credential storage, auth context, login
//! interaction, and the per-provider api-key / OAuth auth contracts. Port of
//! `auth/types.ts`.

use std::fmt;
use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{ProviderEnv, ProviderHeaders};
use futures::future::BoxFuture;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::utils::diagnostics::Thrown;

/// Request auth for a single model request. If a value cannot be expressed as
/// `apiKey`, `headers`, or `baseUrl`, it is provider config, not auth.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelAuth {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub api_key: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub headers: Option<ProviderHeaders>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub base_url: Option<String>,
}

/// The `type: "api_key"` discriminant.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum ApiKeyType {
    #[default]
    #[serde(rename = "api_key")]
    ApiKey,
}

/// The `type: "oauth"` discriminant.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum OAuthType {
    #[default]
    #[serde(rename = "oauth")]
    OAuth,
}

/// Stored api-key credential. `env` holds provider-scoped environment/config
/// values such as Cloudflare account/gateway ids.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApiKeyCredential {
    #[serde(rename = "type")]
    pub kind: ApiKeyType,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub key: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub env: Option<ProviderEnv>,
}

impl ApiKeyCredential {
    /// `{ type: "api_key", key }`.
    #[must_use]
    pub fn with_key(key: impl Into<String>) -> Self {
        Self {
            kind: ApiKeyType::ApiKey,
            key: Some(key.into()),
            env: None,
        }
    }
}

/// Provider-specific extra OAuth fields (`[key: string]: unknown`), in
/// insertion order.
pub type OAuthExtra = serde_json::Map<String, serde_json::Value>;

/// OAuth token data returned by extension compatibility flows.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct OAuthCredentials {
    pub refresh: String,
    pub access: String,
    /// Expiry in epoch milliseconds (a JS number).
    #[serde(with = "js_number")]
    pub expires: f64,
    #[serde(flatten)]
    pub extra: OAuthExtra,
}

/// Stored canonical OAuth credential.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct OAuthCredential {
    #[serde(rename = "type")]
    pub kind: OAuthType,
    pub refresh: String,
    pub access: String,
    /// Expiry in epoch milliseconds (a JS number).
    #[serde(with = "js_number")]
    pub expires: f64,
    #[serde(flatten)]
    pub extra: OAuthExtra,
}

impl OAuthCredential {
    /// `{ type: "oauth", refresh, access, expires }`.
    #[must_use]
    pub fn new(refresh: impl Into<String>, access: impl Into<String>, expires: f64) -> Self {
        Self {
            kind: OAuthType::OAuth,
            refresh: refresh.into(),
            access: access.into(),
            expires,
            extra: OAuthExtra::new(),
        }
    }

    /// Adds or replaces one extra field.
    #[must_use]
    pub fn with_extra(mut self, key: &str, value: serde_json::Value) -> Self {
        self.extra.insert(key.to_owned(), value);
        self
    }

    /// An extra field when it is a string.
    #[must_use]
    pub fn extra_str(&self, key: &str) -> Option<&str> {
        self.extra.get(key).and_then(serde_json::Value::as_str)
    }
}

impl From<OAuthCredentials> for OAuthCredential {
    fn from(value: OAuthCredentials) -> Self {
        Self {
            kind: OAuthType::OAuth,
            refresh: value.refresh,
            access: value.access,
            expires: value.expires,
            extra: value.extra,
        }
    }
}

impl From<OAuthCredential> for OAuthCredentials {
    fn from(value: OAuthCredential) -> Self {
        Self {
            refresh: value.refresh,
            access: value.access,
            expires: value.expires,
            extra: value.extra,
        }
    }
}

/// One type-tagged credential per provider — the shape of today's auth.json.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Credential {
    ApiKey(ApiKeyCredential),
    OAuth(OAuthCredential),
}

impl Credential {
    /// The `type` discriminant.
    #[must_use]
    pub fn auth_type(&self) -> AuthType {
        match self {
            Self::ApiKey(_) => AuthType::ApiKey,
            Self::OAuth(_) => AuthType::OAuth,
        }
    }
}

/// `"api_key" | "oauth"`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AuthType {
    #[serde(rename = "api_key")]
    ApiKey,
    #[serde(rename = "oauth")]
    OAuth,
}

impl AuthType {
    /// The wire string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ApiKey => "api_key",
            Self::OAuth => "oauth",
        }
    }
}

/// Non-secret credential metadata for account/status enumeration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CredentialInfo {
    pub provider_id: String,
    #[serde(rename = "type")]
    pub kind: AuthType,
}

/// Optional cancellation for public auth and credential operations.
#[derive(Debug, Clone, Default)]
pub struct AuthOperationOptions {
    pub signal: Option<AbortSignal>,
}

impl AuthOperationOptions {
    /// Options carrying `signal`.
    #[must_use]
    pub fn with_signal(signal: AbortSignal) -> Self {
        Self {
            signal: Some(signal),
        }
    }
}

/// The read-modify-write callback of [`CredentialStore::modify`]: sees the
/// current credential, returns the new one or `None` to leave it unchanged.
pub type ModifyFn = Box<
    dyn FnOnce(Option<Credential>) -> BoxFuture<'static, Result<Option<Credential>, Thrown>> + Send,
>;

/// App-owned credential storage, keyed by `Provider.id`, one credential per
/// provider. `modify` is the only write path, so every mutation is a
/// serialized read-modify-write; `Models.getAuth()` runs OAuth refresh inside
/// `modify` so concurrent requests cannot double-refresh a rotated token.
///
/// Error semantics: `read` resolves `None` for missing entries. Methods
/// fail only on storage failure; `Models` wraps such failures in
/// `ModelsError` with code "auth". Best-effort stores that serve an in-memory
/// view and record persistence errors internally are valid implementations.
pub trait CredentialStore: Send + Sync {
    /// Read the stored credential, possibly expired. Display/status use.
    fn read<'a>(
        &'a self,
        provider_id: &'a str,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<Option<Credential>, Thrown>>;

    /// List stored credential metadata without resolving or exposing secrets.
    /// Implementations must not execute configured API-key commands while listing.
    fn list(
        &self,
        options: AuthOperationOptions,
    ) -> BoxFuture<'_, Result<Vec<CredentialInfo>, Thrown>>;

    /// Serialized write — the only write path. `f` sees the current
    /// credential; it returns the new credential, or `None` to leave the
    /// entry unchanged. Mutual exclusion per provider id, cross-process too
    /// where the backing store supports it. Resolves with the post-write
    /// credential. Failures from `f` propagate.
    fn modify<'a>(
        &'a self,
        provider_id: &'a str,
        f: ModifyFn,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<Option<Credential>, Thrown>>;

    /// Remove a credential (logout). Implementations serialize this against `modify`.
    fn delete<'a>(
        &'a self,
        provider_id: &'a str,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<(), Thrown>>;
}

/// Environment access for auth resolution. Injectable for tests.
pub trait AuthContext: Send + Sync {
    /// The value of environment variable `name`, if set.
    fn env<'a>(&'a self, name: &'a str) -> BoxFuture<'a, Option<String>>;
    /// Check whether a file exists. Supports a leading `~`.
    fn file_exists<'a>(&'a self, path: &'a str) -> BoxFuture<'a, bool>;
}

/// Result of resolving auth for a model.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AuthResult {
    pub auth: ModelAuth,
    /// Provider-scoped environment/config values resolved from credentials and ambient context.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub env: Option<ProviderEnv>,
    /// Human-readable label for status UI: "`ANTHROPIC_API_KEY`", "OAuth", "~/.aws/credentials".
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
}

/// Side-effect-free availability check result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthCheck {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    #[serde(rename = "type")]
    pub kind: AuthType,
}

/// One `select` prompt option.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthSelectOption {
    pub id: String,
    pub label: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub description: Option<String>,
}

impl AuthSelectOption {
    /// `{ id, label }`.
    #[must_use]
    pub fn new(id: &str, label: &str) -> Self {
        Self {
            id: id.to_owned(),
            label: label.to_owned(),
            description: None,
        }
    }
}

/// The variant part of an [`AuthPrompt`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum AuthPromptKind {
    Text {
        message: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        placeholder: Option<String>,
    },
    Secret {
        message: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        placeholder: Option<String>,
    },
    Select {
        message: String,
        options: Vec<AuthSelectOption>,
    },
    ManualCode {
        message: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        placeholder: Option<String>,
    },
}

/// Prompt shown to the user during login. `signal` lets the flow cancel a
/// pending prompt when an out-of-band event resolves the step, e.g. a
/// `manual_code` prompt raced against a callback server, aborted when the
/// callback wins.
#[derive(Debug, Clone)]
pub struct AuthPrompt {
    pub signal: Option<AbortSignal>,
    pub kind: AuthPromptKind,
}

impl AuthPrompt {
    /// A prompt without its own signal.
    #[must_use]
    pub fn new(kind: AuthPromptKind) -> Self {
        Self { signal: None, kind }
    }
}

/// A link attached to an `info` event.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthInfoLink {
    pub url: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

/// Login progress notification.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum AuthEvent {
    Info {
        message: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        links: Option<Vec<AuthInfoLink>>,
    },
    AuthUrl {
        url: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        instructions: Option<String>,
    },
    DeviceCode {
        user_code: String,
        verification_uri: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        interval_seconds: Option<f64>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        expires_in_seconds: Option<f64>,
    },
    Progress {
        message: String,
    },
}

/// Login interaction callbacks serving both api-key and OAuth flows.
///
/// `prompt()` returns the entered/selected string (`select` returns the
/// option id) and fails on cancel/abort. `signal` aborts the whole login flow;
/// per-prompt cancellation uses [`AuthPrompt::signal`].
pub trait AuthInteraction: Send + Sync {
    /// The whole-login abort signal, if any.
    fn signal(&self) -> Option<AbortSignal>;
    /// Ask the user; resolves with the answer.
    fn prompt(&self, prompt: AuthPrompt) -> BoxFuture<'_, Result<String, Thrown>>;
    /// Show a login event.
    fn notify(&self, event: AuthEvent);
}

/// Normalized interaction passed to provider login implementations: the
/// app's [`AuthInteraction`] with a guaranteed signal.
#[derive(Clone)]
pub struct ProviderAuthInteraction {
    pub signal: AbortSignal,
    pub interaction: Arc<dyn AuthInteraction>,
}

impl ProviderAuthInteraction {
    /// Pair an interaction with the login signal.
    #[must_use]
    pub fn new(interaction: Arc<dyn AuthInteraction>, signal: AbortSignal) -> Self {
        Self {
            signal,
            interaction,
        }
    }

    /// Forward to [`AuthInteraction::prompt`].
    ///
    /// # Errors
    ///
    /// Whatever the app's prompt fails with (cancel/abort).
    pub async fn prompt(&self, prompt: AuthPrompt) -> Result<String, Thrown> {
        self.interaction.prompt(prompt).await
    }

    /// Forward to [`AuthInteraction::notify`].
    pub fn notify(&self, event: AuthEvent) {
        self.interaction.notify(event);
    }
}

impl fmt::Debug for ProviderAuthInteraction {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ProviderAuthInteraction")
            .field("signal", &self.signal)
            .finish_non_exhaustive()
    }
}

/// Input of [`ApiKeyAuth::check`] and [`ApiKeyAuth::resolve`].
#[derive(Clone)]
pub struct ApiKeyResolveInput {
    pub ctx: Arc<dyn AuthContext>,
    pub credential: Option<ApiKeyCredential>,
    pub signal: AbortSignal,
}

/// Api-key auth: stored key/provider env plus ambient sources (env vars, AWS
/// profiles, ADC files). Ambient-only providers have no `login`.
pub trait ApiKeyAuth: Send + Sync {
    /// Display name, e.g. "Anthropic API key".
    fn name(&self) -> &str;

    /// Interactive setup (prompt for key/provider env). `None` = ambient-only.
    fn login(
        &self,
        interaction: ProviderAuthInteraction,
    ) -> Option<BoxFuture<'_, Result<ApiKeyCredential, Thrown>>> {
        let _ = interaction;
        None
    }

    /// Optional side-effect-free availability check. Implement it when
    /// `resolve()` may execute commands or perform other request-time work.
    /// `None` means Models checks availability by resolving auth.
    fn check(
        &self,
        input: ApiKeyResolveInput,
    ) -> Option<BoxFuture<'_, Result<Option<AuthCheck>, Thrown>>> {
        let _ = input;
        None
    }

    /// Resolve auth from the stored credential and/or ambient sources,
    /// merging per field. `None` = not configured.
    fn resolve(
        &self,
        input: ApiKeyResolveInput,
    ) -> BoxFuture<'_, Result<Option<AuthResult>, Thrown>>;
}

/// Returns the stable ID of this app installation.
pub type GetDeviceId = Arc<dyn Fn() -> String + Send + Sync>;

/// App-supplied context for `Models.login`.
#[derive(Clone, Default)]
pub struct LoginOptions {
    /// Returns the stable ID of this app installation, e.g. sent to `OpenAI` as
    /// its agent host ID. Called only by login flows that need it, so apps can
    /// create the ID on first use and must return the same ID on every later call.
    pub get_device_id: Option<GetDeviceId>,
    /// Name this app introduces itself with during login, e.g. `OpenAI`'s agent
    /// name hint and Codex originator. Defaults to pi's own name.
    pub agent_name: Option<String>,
}

impl fmt::Debug for LoginOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LoginOptions")
            .field("get_device_id", &self.get_device_id.is_some())
            .field("agent_name", &self.agent_name)
            .finish()
    }
}

/// OAuth auth. The `refresh`/`to_auth` split lets `Models` own the locked
/// refresh pattern: `refresh` produces a credential, `to_auth` derives request
/// auth from whatever credential ends up stored.
pub trait OAuthAuth: Send + Sync {
    /// Display name, e.g. "Anthropic (Claude Pro/Max)".
    fn name(&self) -> &str;

    /// Whether access through this auth method is backed by a provider subscription.
    fn is_subscription(&self) -> Option<bool> {
        None
    }

    /// Selector label for the OAuth login option.
    fn login_label(&self) -> Option<&str> {
        None
    }

    /// Run the interactive login.
    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>>;

    /// Exchange the refresh token. Network call; fails on `invalid_grant` etc.
    /// `Models` runs this under the store lock.
    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>>;

    /// Side-effect-free derivation of request auth from a valid credential.
    /// Covers per-credential baseUrl (`GitHub` Copilot).
    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>>;
}

/// Provider auth. At least one of `api_key`/`oauth` must be present.
#[derive(Clone, Default)]
pub struct ProviderAuth {
    pub api_key: Option<Arc<dyn ApiKeyAuth>>,
    pub oauth: Option<Arc<dyn OAuthAuth>>,
}

impl fmt::Debug for ProviderAuth {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ProviderAuth")
            .field(
                "api_key",
                &self.api_key.as_ref().map(|auth| auth.name().to_owned()),
            )
            .field(
                "oauth",
                &self.oauth.as_ref().map(|auth| auth.name().to_owned()),
            )
            .finish()
    }
}

/// Serializes a JS number the way `JSON.stringify` does for the values OAuth
/// expiries take: integral values without a fraction.
mod js_number {
    use super::{Deserialize, Deserializer, Serializer};

    /// Largest integer a JS number holds exactly (`Number.MAX_SAFE_INTEGER`).
    const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

    // serde's `with` passes the field by reference.
    #[allow(clippy::trivially_copy_pass_by_ref)] // signature fixed by serde `with`
    pub(super) fn serialize<S: Serializer>(value: &f64, serializer: S) -> Result<S::Ok, S::Error> {
        if value.fract() == 0.0 && value.abs() <= MAX_SAFE_INTEGER {
            // Exact: integral and within the safe-integer range.
            #[allow(clippy::cast_possible_truncation)] // checked integral and in range above
            serializer.serialize_i64(*value as i64)
        } else {
            serializer.serialize_f64(*value)
        }
    }

    pub(super) fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<f64, D::Error> {
        f64::deserialize(deserializer)
    }
}
