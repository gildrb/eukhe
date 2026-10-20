//! Auth subsystem: credential storage, resolution priority, stale-marking.

pub(crate) mod failure_text;
pub(crate) mod flight;
pub(crate) mod manager;
pub(crate) mod prime_browser_login;
pub(crate) mod prime_inference;
pub(crate) mod prime_inference_login;
pub(crate) mod provider_oauth;
pub(crate) mod redirect_input;
pub(crate) mod resolve_config_value;
pub(crate) mod storage;
pub(crate) mod types;

pub use flight::RefreshFlights;
pub use manager::{AuthApiKeyResult, AuthStorage, NoOAuth, OAuthIntegration};
pub use prime_browser_login::PrimeAuthInfo;
pub use prime_inference::{
    check_prime_inference_access, default_prime_cli_config_path, fetch_prime_teams,
    read_prime_cli_config, resolve_prime_inference_auth_config, PrimeAccessError,
    PrimeAccessFailure, PrimeCliConfig, PrimeHttp, PrimeHttpResponse, PrimeInferenceAuthConfig,
    ReqwestPrimeHttp, DEFAULT_PRIME_API_BASE_URL, DEFAULT_PRIME_FRONTEND_URL,
    DEFAULT_REQUEST_TIMEOUT_MS,
};
pub use prime_inference_login::{
    login_prime_inference, PrimeInferenceLoginCallbacks, PrimeInferenceLoginOptions,
    PrimeInferenceLoginResult, PrimeInferenceLoginSource,
};
pub use provider_oauth::{
    stored_oauth_credential, subscription_oauth_flow, ProviderOAuth, ANTHROPIC_PROVIDER_ID,
    GITHUB_COPILOT_PROVIDER_ID, OPENAI_CODEX_PROVIDER_ID, XAI_PROVIDER_ID,
};
pub use redirect_input::{
    clean_paste, exchange_retry_notice, parse_redirect_input, PastedAuthorization,
    RedirectInputError, VerifiedAuthorization,
};
pub use storage::{
    parse_storage_data, AuthStorageBackend, FileAuthStorageBackend, InMemoryAuthStorageBackend,
    AUTH_FILE_NAME,
};
pub use types::{
    AuthCredential, AuthSource, AuthSourceToken, AuthStatus, AuthStorageData, PrimeTeamAssignment,
    PrimeTeamCredential, StoredPrimeTeam, PRIME_INFERENCE_PROVIDER_ID,
};
