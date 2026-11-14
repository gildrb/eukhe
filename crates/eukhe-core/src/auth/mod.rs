//! Auth subsystem: credential storage, resolution priority, stale-marking.

pub(crate) mod failure_text;
pub(crate) mod flight;
pub(crate) mod manager;
pub(crate) mod provider_oauth;
pub(crate) mod redirect_input;
pub(crate) mod refresh_error;
pub(crate) mod resolve_config_value;
pub(crate) mod storage;
pub(crate) mod types;

pub use flight::RefreshFlights;
pub use manager::{
    AuthApiKeyResult, AuthLoadError, AuthStorage, AuthStorageError, AuthWriteCause, AuthWriteError,
    NoOAuth, OAuthIntegration,
};
pub use provider_oauth::{
    stored_oauth_credential, subscription_oauth_flow, ProviderOAuth, ANTHROPIC_PROVIDER_ID,
    GITHUB_COPILOT_PROVIDER_ID, OPENAI_CODEX_PROVIDER_ID, XAI_PROVIDER_ID,
};
pub use redirect_input::{
    clean_paste, exchange_retry_notice, parse_redirect_input, PastedAuthorization,
    RedirectInputError, VerifiedAuthorization,
};
pub use refresh_error::{AuthFileError, OAuthRefreshError, RefreshError, RefreshFailed};
pub use storage::{
    edit_storage_data, parse_storage_data, AuthStorageBackend, FileAuthStorageBackend,
    InMemoryAuthStorageBackend, AUTH_FILE_NAME,
};
pub use types::{AuthCredential, AuthSource, AuthSourceToken, AuthStatus, AuthStorageData};
