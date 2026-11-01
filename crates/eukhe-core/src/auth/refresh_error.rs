//! Why an OAuth refresh gave no fresh credential: the integration's
//! failure ([`OAuthRefreshError`]), the refresh flight's failure around it
//! ([`RefreshError`]: the auth document's read, parse or save), and the
//! reason a lookup reports ([`RefreshFailed`]). Rendered once, where the
//! model registry turns a failed lookup into the user's message.

use std::sync::Arc;

use eukhe_ai::utils::diagnostics::Thrown;

/// Why an [`OAuthIntegration`](crate::auth::OAuthIntegration) refresh
/// returned no fresh credential.
#[derive(Debug, thiserror::Error)]
pub enum OAuthRefreshError {
    /// No OAuth integration is installed (embedded hosts).
    #[error("no OAuth integration can refresh {provider}")]
    NoIntegration { provider: String },
    /// The integration has no refresh flow for the provider.
    #[error("{provider} has no token refresh flow")]
    NoFlow { provider: String },
    /// The document holds no credential for the provider.
    #[error("no stored credential for {provider}")]
    NotStored { provider: String },
    /// The stored credential carries no refresh token.
    #[error("the stored {provider} credential has no refresh token")]
    NoRefreshToken { provider: String },
    /// The provider id is not an `mcp:<server>` login.
    #[error("{provider} is not an MCP login")]
    NotMcpLogin { provider: String },
    /// The stored MCP credential names no endpoint to refresh at.
    #[error("the stored {provider} credential names no MCP endpoint")]
    NoMcpEndpoint { provider: String },
    /// The refresh thread's private runtime did not start.
    #[error("could not start the refresh runtime: {0}")]
    Runtime(#[source] std::io::Error),
    /// The refresh thread did not start.
    #[error("could not start the refresh thread: {0}")]
    Thread(#[source] std::io::Error),
    /// The refresh thread panicked.
    #[error("the refresh thread panicked")]
    Panicked,
    /// The subscription provider's OAuth flow failed.
    #[error(transparent)]
    Flow(Thrown),
    /// The MCP token endpoint refresh failed (its whole cause chain).
    #[error("{0:#}")]
    Mcp(#[source] anyhow::Error),
}

/// Why the auth document could not be read for a refresh.
#[derive(Debug, Clone, thiserror::Error)]
pub enum AuthFileError {
    #[error("could not read the auth file: {0:#}")]
    Read(#[source] Arc<anyhow::Error>),
    #[error("could not parse the auth file: {0:#}")]
    Parse(#[source] Arc<anyhow::Error>),
}

/// Why one refresh flight gave no credential. Shared by every caller that
/// joined the flight, so its sources sit behind `Arc`.
#[derive(Debug, Clone, thiserror::Error)]
pub enum RefreshError {
    #[error(transparent)]
    File(#[from] AuthFileError),
    #[error("no stored credential for {provider}")]
    NotStored { provider: String },
    #[error("the stored credential for {provider} is not OAuth")]
    NotOAuth { provider: String },
    #[error(transparent)]
    Fetch(Arc<OAuthRefreshError>),
    #[error("could not save the refreshed credential: {0:#}")]
    Save(#[source] Arc<anyhow::Error>),
    /// The leader unwound (a panic in the integration) before it landed
    /// its flight.
    #[error("the token refresh of {provider} ended without an outcome")]
    Unlanded { provider: String },
}

/// Why an expired OAuth credential resolved no key: the failed refresh of
/// `provider`.
#[derive(Debug, Clone, thiserror::Error)]
#[error("OAuth token refresh failed for \"{provider}\": {cause}")]
pub struct RefreshFailed {
    pub provider: String,
    #[source]
    pub cause: RefreshError,
}
