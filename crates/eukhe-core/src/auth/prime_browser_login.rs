//! The Prime browser challenge (TS `prime-inference-auth.ts`'s
//! `runPrimeBrowserLogin`): the RSA `auth_challenge` flow that yields a
//! Prime API key. The inference login (`prime_inference_login.rs`) drives
//! it; the interactive surface (the URL display, the paste fallback)
//! lives in the composition root.

use std::time::Duration;

use base64::Engine as _;
use rsa::pkcs8::EncodePublicKey;
use serde_json::{json, Value};

use super::prime_inference::{read_response_message, PrimeHttp};

/// TS `DEFAULT_POLL_INTERVAL_MS` (the challenge status poll).
pub const DEFAULT_POLL_INTERVAL_MS: u64 = 5_000;

/// The browser auth info TS `onAuth` receives: the challenge URL and the
/// code line (the dialog shows both).
pub struct PrimeAuthInfo {
    pub url: String,
    pub instructions: String,
}

/// One challenge round (TS `PrimeChallengeResponse`).
struct PrimeChallenge {
    challenge: String,
    status_auth_token: String,
}

/// TS `generatePrimeChallenge`: POST the public key, read the challenge
/// and the status token.
async fn generate_prime_challenge(
    http: &dyn PrimeHttp,
    base_url: &str,
    public_key: &str,
    timeout_ms: u64,
) -> Result<PrimeChallenge, String> {
    let url = format!("{base_url}/api/v1/auth_challenge/generate");
    let body = json!({"encryptionPublicKey": public_key}).to_string();
    let response = http.post_json(&url, &body, None, timeout_ms).await?;
    if !(200..300).contains(&response.status) {
        return Err(format!(
            "Failed to generate Prime login challenge (HTTP {}): {}",
            response.status,
            read_response_message(response.status, &response.body)
        ));
    }
    let invalid = || {
        format!(
            "Prime login challenge returned an invalid response (HTTP {}): {}",
            response.status,
            crate::auth::failure_text::response_snippet(&response.body)
        )
    };
    let data: Value = serde_json::from_str(&response.body)
        .map_err(|_| invalid())
        .and_then(|data: Value| data.is_object().then_some(data).ok_or_else(invalid))?;
    let string_field = |key: &str| {
        data.get(key)
            .and_then(Value::as_str)
            .map(str::trim)
            .filter(|value| !value.is_empty())
            .map(str::to_string)
    };
    let Some(challenge) = string_field("challenge") else {
        return Err("Prime login challenge response missing required fields".to_string());
    };
    let Some(status_auth_token) = string_field("status_auth_token") else {
        return Err("Prime login challenge response missing required fields".to_string());
    };
    Ok(PrimeChallenge {
        challenge,
        status_auth_token,
    })
}

/// TS `pollPrimeChallengeResult`: poll the status until the encrypted
/// result lands, then decrypt the API key (RSA-OAEP-SHA256).
async fn poll_prime_challenge_result(
    http: &dyn PrimeHttp,
    base_url: &str,
    challenge: &PrimeChallenge,
    private_key: &rsa::RsaPrivateKey,
    timeout_ms: u64,
    poll_interval_ms: u64,
) -> Result<String, String> {
    loop {
        let query = url::form_urlencoded::Serializer::new(String::new())
            .append_pair("challenge", &challenge.challenge)
            .finish();
        let status_url = format!("{base_url}/api/v1/auth_challenge/status?{query}");
        let response = http
            .get(&status_url, &challenge.status_auth_token, timeout_ms)
            .await?;
        if response.status == 404 {
            return Err("Prime login challenge expired".to_string());
        }
        if !(200..300).contains(&response.status) {
            return Err(format!(
                "Failed to check Prime login status (HTTP {}): {}",
                response.status,
                read_response_message(response.status, &response.body)
            ));
        }
        let invalid = || {
            format!(
                "Prime login status returned an invalid response (HTTP {}): {}",
                response.status,
                crate::auth::failure_text::response_snippet(&response.body)
            )
        };
        let data: Value = serde_json::from_str(&response.body)
            .map_err(|_| invalid())
            .and_then(|data: Value| data.is_object().then_some(data).ok_or_else(invalid))?;
        if let Some(encrypted) = data
            .get("result")
            .and_then(Value::as_str)
            .filter(|result| !result.is_empty())
        {
            return decrypt_prime_challenge_result(private_key, encrypted);
        }
        tokio::time::sleep(Duration::from_millis(poll_interval_ms)).await;
    }
}

/// TS `decryptPrimeChallengeResult`: RSA-OAEP-SHA256 over the base64
/// result.
fn decrypt_prime_challenge_result(
    private_key: &rsa::RsaPrivateKey,
    encrypted_result: &str,
) -> Result<String, String> {
    let ciphertext = base64::engine::general_purpose::STANDARD
        .decode(encrypted_result.as_bytes())
        .map_err(|_| "Prime login challenge result could not be decoded".to_string())?;
    let padding = rsa::Oaep::new::<sha2::Sha256>();
    let decrypted = private_key
        .decrypt(padding, &ciphertext)
        .map_err(|_| "Prime login challenge result could not be decrypted".to_string())?;
    String::from_utf8(decrypted)
        .map_err(|_| "Prime login challenge result is not UTF-8".to_string())
}

/// The challenge URL's query: the code. A plain sync fn on purpose: the
/// serializer's encoding callback is not `Sync`, so it must never name a
/// local inside the async login (the future would carry the type and lose
/// `Send`).
fn prime_challenge_query(code: &str) -> String {
    url::form_urlencoded::Serializer::new(String::new())
        .append_pair("code", code)
        .finish()
}

/// TS `runPrimeBrowserLogin`: the keypair, the challenge, the auth URL
/// callback, and the status poll. The challenge URL carries only the code.
pub(super) async fn run_prime_browser_login(
    http: &dyn PrimeHttp,
    base_url: &str,
    frontend_url: &str,
    on_auth: &(dyn Fn(&PrimeAuthInfo) + Send + Sync),
    timeout_ms: u64,
    poll_interval_ms: u64,
) -> Result<String, String> {
    let mut rng = rsa::rand_core::OsRng;
    let private_key = rsa::RsaPrivateKey::new(&mut rng, 2048).map_err(|error| error.to_string())?;
    let public_key = private_key
        .to_public_key()
        .to_public_key_pem(rsa::pkcs8::LineEnding::LF)
        .map_err(|error| error.to_string())?;
    let challenge = generate_prime_challenge(http, base_url, &public_key, timeout_ms).await?;
    // TS builds the URL with `URLSearchParams` (space encodes as `+`).
    let query = prime_challenge_query(&challenge.challenge);
    let auth_url = format!("{frontend_url}/dashboard/tokens/challenge?{query}");
    on_auth(&PrimeAuthInfo {
        url: auth_url,
        instructions: format!("Code: {}", challenge.challenge),
    });
    poll_prime_challenge_result(
        http,
        base_url,
        &challenge,
        &private_key,
        timeout_ms,
        poll_interval_ms,
    )
    .await
}
