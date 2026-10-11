//! Authentication: credential types and storage, auth resolution with locked
//! OAuth refresh, api-key helpers, and the built-in OAuth flows. Port of
//! `src/auth/*`.

mod context;
mod credential_store;
pub(crate) mod errors;
mod helpers;
pub mod oauth;
mod resolve;
#[cfg(test)]
pub(crate) mod test_oauth;
mod types;

pub use context::default_provider_auth_context;
pub use credential_store::InMemoryCredentialStore;
pub use helpers::{env_api_key_auth, lazy_oauth, LazyOAuthInput, OAuthLoader};
pub use resolve::{
    refresh_stored_oauth_credential, resolve_provider_auth, AuthResolutionOverrides,
};
pub use types::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, ApiKeyType, AuthCheck, AuthContext,
    AuthEvent, AuthInfoLink, AuthInteraction, AuthOperationOptions, AuthPrompt, AuthPromptKind,
    AuthResult, AuthSelectOption, AuthType, Credential, CredentialInfo, CredentialStore,
    GetDeviceId, LoginOptions, ModelAuth, ModifyFn, OAuthAuth, OAuthCredential, OAuthCredentials,
    OAuthExtra, OAuthType, ProviderAuth, ProviderAuthInteraction,
};
