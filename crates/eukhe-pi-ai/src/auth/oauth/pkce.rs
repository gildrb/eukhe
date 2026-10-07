//! PKCE utilities. Port of `auth/oauth/pkce.ts`.

use base64::engine::general_purpose::URL_SAFE_NO_PAD;
use base64::Engine as _;
use sha2::{Digest as _, Sha256};

use crate::auth::errors::js_error;
use crate::utils::diagnostics::Thrown;

/// A PKCE code verifier and its S256 challenge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pkce {
    pub verifier: String,
    pub challenge: String,
}

/// Encode bytes as a base64url string without padding.
pub(crate) fn base64url_encode(bytes: &[u8]) -> String {
    URL_SAFE_NO_PAD.encode(bytes)
}

/// `n` cryptographically random bytes.
pub(crate) fn random_bytes<const N: usize>() -> Result<[u8; N], Thrown> {
    let mut bytes = [0_u8; N];
    getrandom::fill(&mut bytes).map_err(|error| js_error(error.to_string()))?;
    Ok(bytes)
}

/// Generate a PKCE code verifier (32 random bytes, base64url) and its
/// SHA-256 challenge.
///
/// # Errors
///
/// When the OS random source fails.
pub fn generate_pkce() -> Result<Pkce, Thrown> {
    let verifier = base64url_encode(&random_bytes::<32>()?);
    let challenge = base64url_encode(&Sha256::digest(verifier.as_bytes()));
    Ok(Pkce {
        verifier,
        challenge,
    })
}
