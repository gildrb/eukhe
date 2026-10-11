//! `aws login` profiles: `fromLoginCredentials` of
//! `@aws-sdk/credential-provider-login` (cached console-session credentials,
//! refreshed through the Signin `CreateOAuth2Token` operation with a `DPoP`
//! proof).

use base64::engine::general_purpose::{STANDARD, URL_SAFE_NO_PAD};
use base64::Engine as _;
use eukhe_types::pi_ai::{JsonObject, JsonValue};
use reqwest::Method;
use ring::rand::SystemRandom;
use ring::signature::{EcdsaKeyPair, KeyPair, ECDSA_P256_SHA256_FIXED_SIGNING};
use sha2::{Digest, Sha256};
use url::Url;
use uuid::Uuid;

use super::super::client_config::AwsCredentials;
use super::js_compat::{
    js_date_from_json, js_error_string, json_property, json_truthy, node_fs_error, node_path_join,
    now_ms, to_iso_string,
};
use super::sdk_client::{
    json_reply, nested_client, reused_proxy, AwsService, NestedClientConfig, PreparedRequest,
};
use super::shared_ini::parse_known_files;
use super::{ProviderFailure, ProviderResult, Resolution};
use crate::utils::diagnostics::{ErrorObject, SdkValue, Thrown};
use crate::utils::js::{js_to_string, json_stringify, json_stringify_pretty};
use crate::utils::json_parse::js_json_parse;

/// `LoginCredentialsFetcher.REFRESH_THRESHOLD`.
const REFRESH_THRESHOLD_MS: f64 = 5.0 * 60.0 * 1000.0;

/// The login session's token cache file.
fn token_file_path(resolution: &Resolution<'_>, login_session: &str) -> String {
    let env = resolution.env;
    let directory = env.var("AWS_LOGIN_CACHE_DIRECTORY").unwrap_or_else(|| {
        // `os.homedir()` reads `HOME` before the password database.
        let home = env
            .var("HOME")
            .or_else(|| env.os_home_dir.clone())
            .unwrap_or_default();
        node_path_join(&[&home, ".aws", "login", "cache"])
    });
    let hash = hex::encode(Sha256::digest(login_session.as_bytes()));
    node_path_join(&[&directory, &format!("{hash}.json")])
}

/// `loadToken()`: the validated cache file.
fn load_token(path: &str) -> ProviderResult<JsonObject> {
    let failure = |error: &Thrown| {
        ProviderFailure::credentials_final(format!(
            "Failed to load token from {path}: {}",
            js_error_string(error)
        ))
    };
    let bytes =
        std::fs::read(path).map_err(|error| failure(&node_fs_error(&error, "open", path)))?;
    let token = js_json_parse(&String::from_utf8_lossy(&bytes))
        .map_err(|error| failure(&ErrorObject::named("SyntaxError", error.message).thrown()))?;
    let mut missing = Vec::new();
    for key in ["accessToken", "clientId", "refreshToken", "dpopKey"] {
        let value = json_property(&token, key).map_err(|error| failure(&error.thrown()))?;
        if !json_truthy(value) {
            missing.push(key);
        }
    }
    let account_id = token
        .get("accessToken")
        .and_then(|access_token| access_token.get("accountId"));
    if !json_truthy(account_id) {
        missing.push("accountId");
    }
    if !missing.is_empty() {
        return Err(failure(
            &ErrorObject::named(
                "CredentialsProviderError",
                format!(
                    "Token validation failed, missing fields: {}",
                    missing.join(", ")
                ),
            )
            .thrown(),
        ));
    }
    match token {
        JsonValue::Object(token) => Ok(token),
        // Every validated token is an object (its keys were truthy).
        other => Err(failure(
            &ErrorObject::named(
                "TypeError",
                format!("Unexpected token {}", js_to_string(&other)),
            )
            .thrown(),
        )),
    }
}

/// `new Date(token.accessToken.expiresAt).getTime()`.
fn access_token_expiry(token: &JsonObject) -> f64 {
    token
        .get("accessToken")
        .and_then(|access_token| access_token.get("expiresAt"))
        .map_or(f64::NAN, js_date_from_json)
}

/// `toCredentials(token.accessToken)`.
fn to_credentials(token: &JsonObject) -> AwsCredentials {
    let field = |key: &str| {
        token
            .get("accessToken")
            .and_then(|access_token| access_token.get(key))
    };
    let string = |key: &str| field(key).map_or_else(|| "undefined".to_owned(), js_to_string);
    AwsCredentials {
        access_key_id: string("accessKeyId"),
        secret_access_key: string("secretAccessKey"),
        session_token: field("sessionToken")
            .filter(|value| json_truthy(Some(value)))
            .map(js_to_string),
    }
}

/// The SEC1 `ECPrivateKey` DER fields: the 32-byte private scalar and the
/// uncompressed public point.
fn sec1_key_parts(der: &[u8]) -> Result<(Vec<u8>, Vec<u8>), String> {
    let invalid = || "Invalid EC private key".to_owned();
    let mut reader = DerReader { bytes: der };
    let mut sequence = DerReader {
        bytes: reader.read(0x30).ok_or_else(invalid)?,
    };
    sequence.read(0x02).ok_or_else(invalid)?;
    let private_key = sequence.read(0x04).ok_or_else(invalid)?.to_vec();
    let mut public_key = None;
    while let Some((tag, value)) = sequence.next() {
        if tag == 0xa1 {
            let mut inner = DerReader { bytes: value };
            let bits = inner.read(0x03).ok_or_else(invalid)?;
            public_key = bits.get(1..).map(<[u8]>::to_vec);
        }
    }
    let public_key = public_key.ok_or_else(|| "EC private key has no public key".to_owned())?;
    Ok((private_key, public_key))
}

/// A minimal DER TLV reader.
struct DerReader<'a> {
    bytes: &'a [u8],
}

impl<'a> DerReader<'a> {
    fn next(&mut self) -> Option<(u8, &'a [u8])> {
        let (&tag, rest) = self.bytes.split_first()?;
        let (&first, mut rest) = rest.split_first()?;
        let length = if first & 0x80 == 0 {
            usize::from(first)
        } else {
            let count = usize::from(first & 0x7f);
            let (length_bytes, after) = rest.split_at_checked(count)?;
            rest = after;
            length_bytes
                .iter()
                .fold(0_usize, |length, byte| (length << 8) | usize::from(*byte))
        };
        let (value, after) = rest.split_at_checked(length)?;
        self.bytes = after;
        Some((tag, value))
    }

    fn read(&mut self, expected: u8) -> Option<&'a [u8]> {
        let (tag, value) = self.next()?;
        (tag == expected).then_some(value)
    }
}

/// `generateDpop(method, endpoint)`: an ES256 `dpop+jwt` signed with the
/// cached `dpopKey`.
fn generate_dpop(token_path: &str, method: &str, endpoint: &str) -> ProviderResult<String> {
    let token = load_token(token_path)?;
    let dpop_failure = |message: String| {
        ProviderFailure::credentials_final(format!("Failed to generate Dpop proof: {message}"))
    };
    let pem = token.get("dpopKey").map(js_to_string).unwrap_or_default();
    let body: String = pem
        .lines()
        .filter(|line| !line.starts_with("-----"))
        .map(str::trim)
        .collect();
    let der = STANDARD
        .decode(body)
        .map_err(|error| dpop_failure(error.to_string()))?;
    let (private_key, public_key) = sec1_key_parts(&der).map_err(dpop_failure)?;
    let rng = SystemRandom::new();
    let key_pair = EcdsaKeyPair::from_private_key_and_public_key(
        &ECDSA_P256_SHA256_FIXED_SIGNING,
        &private_key,
        &public_key,
        &rng,
    )
    .map_err(|error| dpop_failure(error.to_string()))?;
    let point = key_pair.public_key().as_ref();
    let (Some(x), Some(y)) = (point.get(1..33), point.get(33..65)) else {
        return Err(dpop_failure("Invalid EC public key".to_owned()));
    };
    let header = serde_json::json!({
        "alg": "ES256",
        "typ": "dpop+jwt",
        "jwk": {
            "kty": "EC",
            "crv": "P-256",
            "x": URL_SAFE_NO_PAD.encode(x),
            "y": URL_SAFE_NO_PAD.encode(y),
        },
    });
    let issued_at = (now_ms() / 1000.0).floor();
    let payload = serde_json::json!({
        "jti": Uuid::new_v4().to_string(),
        "htm": method,
        "htu": endpoint,
        "iat": issued_at,
    });
    let message = format!(
        "{}.{}",
        URL_SAFE_NO_PAD.encode(json_stringify(&header)),
        URL_SAFE_NO_PAD.encode(json_stringify(&payload))
    );
    let signature = key_pair
        .sign(&rng, message.as_bytes())
        .map_err(|error| dpop_failure(error.to_string()))?;
    Ok(format!(
        "{message}.{}",
        URL_SAFE_NO_PAD.encode(signature.as_ref())
    ))
}

/// `${protocol}//${hostname}${port ? ":" + port : ""}${path}` of a request.
fn dpop_endpoint(url: &Url) -> String {
    let host = url.host_str().unwrap_or_default();
    match url.port() {
        Some(port) => format!("{}://{host}:{port}{}", url.scheme(), url.path()),
        None => format!("{}://{host}{}", url.scheme(), url.path()),
    }
}

/// The refresh call and cache update (the `try` block of `refresh`).
async fn refresh_with_signin(
    resolution: &Resolution<'_>,
    token_path: &str,
    region: &str,
    fresh: &JsonObject,
) -> ProviderResult<AwsCredentials> {
    let client = nested_client(
        resolution,
        &NestedClientConfig {
            service: AwsService::Signin,
            region,
            profile: None,
            proxy: reused_proxy(resolution.caller.request_handler),
        },
    )
    .await?;
    let mut body = JsonObject::new();
    if let Some(client_id) = fresh.get("clientId") {
        body.insert("clientId".to_owned(), client_id.clone());
    }
    body.insert(
        "grantType".to_owned(),
        JsonValue::String("refresh_token".to_owned()),
    );
    if let Some(refresh_token) = fresh.get("refreshToken") {
        body.insert("refreshToken".to_owned(), refresh_token.clone());
    }
    let dpop = |method: &Method, url: &Url| {
        generate_dpop(token_path, method.as_str(), &dpop_endpoint(url))
            .map(|proof| vec![("DPoP".to_owned(), proof)])
    };
    let request = PreparedRequest {
        method: Method::POST,
        path_and_query: "/v1/token".to_owned(),
        headers: vec![("content-type".to_owned(), "application/json".to_owned())],
        body: json_stringify(&JsonValue::Object(body)).into_bytes(),
        credentials: None,
        attempt_headers: Some(&dpop),
    };
    let response = client
        .send(resolution, &request, |reply| json_reply(&reply))
        .await?;
    let access_token = response.get("accessToken");
    let field = |key: &str| {
        access_token
            .and_then(|access_token| access_token.get(key))
            .filter(|value| json_truthy(Some(value)))
            .cloned()
    };
    let refresh_token = response
        .get("refreshToken")
        .filter(|value| json_truthy(Some(value)))
        .cloned();
    let (Some(access_key_id), Some(secret_access_key), Some(session_token), Some(refresh_token)) = (
        field("accessKeyId"),
        field("secretAccessKey"),
        field("sessionToken"),
        refresh_token,
    ) else {
        return Err(ProviderFailure::credentials_final(
            "Token refresh response missing required fields",
        ));
    };
    let expires_in = match response.get("expiresIn") {
        None | Some(JsonValue::Null) => 900.0,
        Some(value) => value.as_f64().unwrap_or(f64::NAN),
    };
    let expiration =
        to_iso_string(now_ms() + expires_in * 1000.0).map_err(ProviderFailure::error)?;
    let mut updated = fresh.clone();
    let mut updated_access_token = match fresh.get("accessToken") {
        Some(JsonValue::Object(access_token)) => access_token.clone(),
        _ => JsonObject::new(),
    };
    updated_access_token.insert("accessKeyId".to_owned(), access_key_id);
    updated_access_token.insert("secretAccessKey".to_owned(), secret_access_key);
    updated_access_token.insert("sessionToken".to_owned(), session_token);
    updated_access_token.insert("expiresAt".to_owned(), JsonValue::String(expiration));
    updated.insert(
        "accessToken".to_owned(),
        JsonValue::Object(updated_access_token),
    );
    updated.insert("refreshToken".to_owned(), refresh_token);
    if let Some(directory) = std::path::Path::new(token_path).parent() {
        // `mkdir` failures are ignored; the write reports its own.
        let _ = resolution
            .abortable(tokio::fs::create_dir_all(directory))
            .await?;
    }
    resolution
        .abortable(tokio::fs::write(
            token_path,
            json_stringify_pretty(&JsonValue::Object(updated.clone())),
        ))
        .await?
        .map_err(|error| ProviderFailure::thrown(node_fs_error(&error, "open", token_path)))?;
    Ok(to_credentials(&updated))
}

/// `refresh(token)`.
async fn refresh(
    resolution: &Resolution<'_>,
    token_path: &str,
    profile_region: Option<&str>,
    token: JsonObject,
) -> ProviderResult<AwsCredentials> {
    let disk_token = load_token(token_path).unwrap_or_else(|_| token.clone());
    let now = now_ms();
    let disk_expiry = access_token_expiry(&disk_token);
    let token_expiry = access_token_expiry(&token);
    let fresh = if disk_expiry <= now && token_expiry > now {
        token
    } else {
        disk_token
    };
    if access_token_expiry(&fresh) - now_ms() > REFRESH_THRESHOLD_MS {
        return Ok(to_credentials(&fresh));
    }
    let region = profile_region.unwrap_or(resolution.caller.region);
    let error = match refresh_with_signin(resolution, token_path, region, &fresh).await {
        Ok(credentials) => return Ok(credentials),
        Err(failure)
            if resolution
                .signal
                .is_some_and(eukhe_chord::context::AbortSignal::aborted) =>
        {
            return Err(failure)
        }
        Err(failure) => failure.error,
    };
    if let Some(object) = error
        .downcast_ref::<ErrorObject>()
        .filter(|object| object.name == "AccessDeniedException")
    {
        let error_type = match &object.error {
            Some(SdkValue::Json(JsonValue::String(error_type))) => Some(error_type.as_str()),
            _ => None,
        };
        let message = match error_type {
            Some("TOKEN_EXPIRED") => "Your session has expired. Please reauthenticate.".to_owned(),
            Some("USER_CREDENTIALS_CHANGED") => "Unable to refresh credentials because of a change in your password. Please reauthenticate with your new password.".to_owned(),
            Some("INSUFFICIENT_PERMISSIONS") => "Unable to refresh credentials due to insufficient permissions. You may be missing permission for the 'CreateOAuth2Token' action.".to_owned(),
            _ => format!(
                "Failed to refresh token: {}. Please re-authenticate using `aws login`",
                js_error_string(&error)
            ),
        };
        return Err(ProviderFailure::credentials_final(message));
    }
    if access_token_expiry(&fresh) > now_ms() {
        // The SDK logs the refresh failure through the client logger (a no-op).
        return Ok(to_credentials(&fresh));
    }
    Err(ProviderFailure::credentials(format!(
        "Failed to refresh token: {}. Please re-authenticate using aws login",
        js_error_string(&error)
    )))
}

/// `fromLoginCredentials({ profile })()`.
///
/// # Errors
///
/// `Profile … does not contain login_session.` (chain continues), token
/// load/refresh errors (chain stops), or the signal's reason.
pub(crate) async fn from_login_credentials(
    resolution: &Resolution<'_>,
    profile_name: &str,
) -> ProviderResult<AwsCredentials> {
    let profiles = parse_known_files(resolution.env).await;
    let profile = profiles.get(profile_name);
    let Some(login_session) = profile.and_then(|profile| profile.get("login_session")) else {
        return Err(ProviderFailure::credentials(format!(
            "Profile {profile_name} does not contain login_session."
        )));
    };
    let token_path = token_file_path(resolution, login_session);
    let token = load_token(&token_path)?;
    if access_token_expiry(&token) - now_ms() <= REFRESH_THRESHOLD_MS {
        let region = profile.and_then(|profile| profile.get("region"));
        return refresh(resolution, &token_path, region, token).await;
    }
    Ok(to_credentials(&token))
}
