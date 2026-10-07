//! SSO profiles: `fromSSO` of `@aws-sdk/credential-provider-sso` (as
//! `fromIni` invokes it), the `fromSso` token provider of
//! `@aws-sdk/token-providers` (SSO-OIDC refresh of `sso-session` tokens), and
//! the SSO portal `GetRoleCredentials` call.

use std::sync::PoisonError;

use eukhe_types::pi_ai::{JsonObject, JsonValue};
use reqwest::Method;
use sha1::{Digest, Sha1};

use super::super::client_config::AwsCredentials;
use super::super::sigv4::escape_uri;
use super::js_compat::{
    js_date_from_json, js_date_parse, js_error_string, json_truthy, now_ms, to_iso_string,
};
use super::sdk_client::{
    json_reply, nested_client, AwsService, NestedClientConfig, PreparedRequest,
};
use super::shared_ini::{load_sso_session_data, parse_known_files};
use super::{CredentialEnv, ProviderFailure, ProviderResult, Resolution};
use crate::utils::diagnostics::ErrorObject;
use crate::utils::js::{js_to_string, json_stringify_pretty};
use crate::utils::json_parse::js_json_parse;

/// `REFRESH_MESSAGE` of the token provider.
const TOKEN_REFRESH_MESSAGE: &str =
    "To refresh this SSO session run 'aws sso login' with the corresponding profile.";

/// The refresh hint of `resolveSSOCredentials`.
const CREDENTIALS_REFRESH_MESSAGE: &str =
    "To refresh this SSO session run aws sso login with the corresponding profile.";

/// `EXPIRE_WINDOW_MS`.
const EXPIRE_WINDOW_MS: f64 = 5.0 * 60.0 * 1000.0;

/// `getSSOTokenFilepath(id)`: `~/.aws/sso/cache/<sha1 hex of id>.json`.
pub(crate) fn sso_token_file_path(env: &CredentialEnv<'_>, id: &str) -> String {
    let cache_name = hex::encode(Sha1::digest(id.as_bytes()));
    env.home_path(&[".aws", "sso", "cache", &format!("{cache_name}.json")])
}

/// `getSSOTokenFromFile(id)`: the parsed cache file.
async fn sso_token_from_file(env: &CredentialEnv<'_>, id: &str) -> Option<JsonValue> {
    let bytes = tokio::fs::read(sso_token_file_path(env, id)).await.ok()?;
    js_json_parse(&String::from_utf8_lossy(&bytes)).ok()
}

/// `TokenProviderError` of a missing token key (`validateTokenKey`).
fn missing_token_key(key: &str, for_refresh: bool) -> ProviderFailure {
    let cannot_refresh = if for_refresh { ". Cannot refresh" } else { "" };
    ProviderFailure::token(
        format!(
            "Value not present for '{key}' in SSO Token{cannot_refresh}. {TOKEN_REFRESH_MESSAGE}"
        ),
        false,
    )
}

/// An SSO bearer token and its expiration (epoch ms; `NaN` when invalid).
struct SsoToken {
    token: JsonValue,
    expiration: f64,
}

/// `validateTokenExpiry(existingToken)`.
fn validate_token_expiry(token: SsoToken) -> ProviderResult<SsoToken> {
    if token.expiration < now_ms() {
        return Err(ProviderFailure::token(
            format!("Token is expired. {TOKEN_REFRESH_MESSAGE}"),
            false,
        ));
    }
    Ok(token)
}

/// `CreateToken` (`grant_type = refresh_token`) against SSO-OIDC.
async fn create_token(
    resolution: &Resolution<'_>,
    sso_region: &str,
    cached: &JsonObject,
) -> ProviderResult<JsonValue> {
    let client = nested_client(
        resolution,
        &NestedClientConfig {
            service: AwsService::SsoOidc,
            region: sso_region,
            profile: None,
            proxy: None,
        },
    )
    .await?;
    let mut body = JsonObject::new();
    for (key, source) in [("clientId", "clientId"), ("clientSecret", "clientSecret")] {
        if let Some(value) = cached.get(source) {
            body.insert(key.to_owned(), value.clone());
        }
    }
    body.insert(
        "grantType".to_owned(),
        JsonValue::String("refresh_token".to_owned()),
    );
    if let Some(value) = cached.get("refreshToken") {
        body.insert("refreshToken".to_owned(), value.clone());
    }
    let request = PreparedRequest {
        method: Method::POST,
        path_and_query: "/token".to_owned(),
        headers: vec![("content-type".to_owned(), "application/json".to_owned())],
        body: JsonValue::Object(body).to_string().into_bytes(),
        credentials: None,
        attempt_headers: None,
    };
    client
        .send(resolution, &request, |reply| json_reply(&reply))
        .await
}

/// The refreshed token of `fromSso`, saved back to the cache file.
async fn refresh_token(
    resolution: &Resolution<'_>,
    session_name: &str,
    sso_region: &str,
    cached: &JsonObject,
) -> ProviderResult<SsoToken> {
    let response = create_token(resolution, sso_region, cached).await?;
    let access_token = response
        .get("accessToken")
        .cloned()
        .ok_or_else(|| missing_token_key("accessToken", false))?;
    let expires_in = response
        .get("expiresIn")
        .ok_or_else(|| missing_token_key("expiresIn", false))?;
    let expires_in = expires_in.as_f64().unwrap_or(f64::NAN);
    let expiration = now_ms() + expires_in * 1000.0;
    let expires_at = to_iso_string(expiration).map_err(ProviderFailure::error)?;
    let mut updated = cached.clone();
    updated.insert("accessToken".to_owned(), access_token.clone());
    updated.insert("expiresAt".to_owned(), JsonValue::String(expires_at));
    match response.get("refreshToken") {
        Some(refresh) => {
            updated.insert("refreshToken".to_owned(), refresh.clone());
        }
        None => {
            updated.shift_remove("refreshToken");
        }
    }
    // Write failures are ignored, as in the SDK.
    let path = sso_token_file_path(resolution.env, session_name);
    let text = json_stringify_pretty(&JsonValue::Object(updated));
    let _ = resolution.abortable(tokio::fs::write(path, text)).await?;
    Ok(SsoToken {
        token: access_token,
        expiration,
    })
}

/// The `sso-session` of `profile_name` and its `sso_region` (the profile and
/// session checks of `fromSso`).
async fn sso_session_of_profile(
    env: &CredentialEnv<'_>,
    profile_name: &str,
) -> ProviderResult<(String, String)> {
    let profiles = parse_known_files(env).await;
    let Some(profile) = profiles.get(profile_name) else {
        return Err(ProviderFailure::token(
            format!("Profile '{profile_name}' could not be found in shared credentials file."),
            false,
        ));
    };
    let Some(session_name) = profile.get("sso_session") else {
        return Err(ProviderFailure::token(
            format!("Profile '{profile_name}' is missing required property 'sso_session'."),
            true,
        ));
    };
    let sessions = load_sso_session_data(env).await;
    let Some(session) = sessions.get(session_name) else {
        return Err(ProviderFailure::token(
            format!("Sso session '{session_name}' could not be found in shared credentials file."),
            false,
        ));
    };
    for key in ["sso_start_url", "sso_region"] {
        if session.get(key).is_none() {
            return Err(ProviderFailure::token(
                format!("Sso session '{session_name}' is missing required property '{key}'."),
                false,
            ));
        }
    }
    let sso_region = session.get("sso_region").unwrap_or_default().to_owned();
    Ok((session_name.to_owned(), sso_region))
}

/// `fromSso({ profile })()` of `@aws-sdk/token-providers`.
async fn sso_session_token(
    resolution: &Resolution<'_>,
    profile_name: &str,
) -> ProviderResult<SsoToken> {
    let env = resolution.env;
    let (session_name, sso_region) = sso_session_of_profile(env, profile_name).await?;
    let session_name = session_name.as_str();
    let invalid = || {
        ProviderFailure::token(
            format!(
                "The SSO session token associated with profile={profile_name} was not found or is invalid. {TOKEN_REFRESH_MESSAGE}"
            ),
            false,
        )
    };
    let cached = sso_token_from_file(env, session_name)
        .await
        .ok_or_else(invalid)?;
    let cached = match cached {
        JsonValue::Object(object) => object,
        JsonValue::Null => {
            return Err(ProviderFailure::error(ErrorObject::named(
                "TypeError",
                "Cannot read properties of null (reading 'accessToken')",
            )))
        }
        JsonValue::Array(_) | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::String(_) => {
            JsonObject::new()
        }
    };
    let access_token = cached
        .get("accessToken")
        .ok_or_else(|| missing_token_key("accessToken", false))?;
    let expires_at = cached
        .get("expiresAt")
        .ok_or_else(|| missing_token_key("expiresAt", false))?;
    let existing = SsoToken {
        token: access_token.clone(),
        expiration: js_date_from_json(expires_at),
    };
    if existing.expiration - now_ms() > EXPIRE_WINDOW_MS {
        return Ok(existing);
    }
    let last_attempt = env
        .state
        .sso_last_refresh_attempts
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .get(session_name)
        .copied()
        .unwrap_or(0.0);
    if now_ms() - last_attempt < 30.0 * 1000.0 {
        return validate_token_expiry(existing);
    }
    for key in ["clientId", "clientSecret", "refreshToken"] {
        if !cached.contains_key(key) {
            return Err(missing_token_key(key, true));
        }
    }
    env.state
        .sso_last_refresh_attempts
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .insert(session_name.to_owned(), now_ms());
    match refresh_token(resolution, session_name, &sso_region, &cached).await {
        Ok(token) => Ok(token),
        // An abort is not a refresh failure.
        Err(failure)
            if resolution
                .signal
                .is_some_and(eukhe_chord::context::AbortSignal::aborted) =>
        {
            Err(failure)
        }
        Err(_) => validate_token_expiry(existing),
    }
}

/// The SSO fields of a profile after `sso-session` resolution.
struct SsoProfileFields {
    start_url: String,
    account_id: String,
    region: String,
    role_name: String,
    session: Option<String>,
}

/// `resolveSSOCredentials(...)`.
async fn resolve_sso_credentials(
    resolution: &Resolution<'_>,
    profile_name: &str,
    fields: SsoProfileFields,
) -> ProviderResult<AwsCredentials> {
    let access_token = if fields.session.is_some() {
        let token = sso_session_token(resolution, profile_name)
            .await
            .and_then(|token| {
                to_iso_string(token.expiration)
                    .map(|expires_at| (token.token, js_date_parse(&expires_at)))
                    .map_err(ProviderFailure::error)
            });
        match token {
            Ok(token) => token,
            Err(failure)
                if resolution
                    .signal
                    .is_some_and(eukhe_chord::context::AbortSignal::aborted) =>
            {
                return Err(failure)
            }
            Err(failure) => return Err(ProviderFailure::credentials_final(failure.message())),
        }
    } else {
        let invalid = || {
            ProviderFailure::credentials_final(format!(
                "The SSO session associated with this profile is invalid. {CREDENTIALS_REFRESH_MESSAGE}"
            ))
        };
        let cached = sso_token_from_file(resolution.env, &fields.start_url)
            .await
            .ok_or_else(invalid)?;
        match cached {
            JsonValue::Null => {
                return Err(ProviderFailure::error(ErrorObject::named(
                    "TypeError",
                    "Cannot read properties of null (reading 'expiresAt')",
                )))
            }
            other => {
                let expiration = other.get("expiresAt").map_or(f64::NAN, js_date_from_json);
                let token = other.get("accessToken").cloned().unwrap_or(JsonValue::Null);
                (token, expiration)
            }
        }
    };
    let (token, expiration) = access_token;
    if expiration - now_ms() <= 0.0 {
        return Err(ProviderFailure::credentials_final(format!(
            "The SSO session associated with this profile has expired. {CREDENTIALS_REFRESH_MESSAGE}"
        )));
    }
    get_role_credentials(resolution, &fields, &token).await
}

/// SSO portal `GetRoleCredentials`.
async fn get_role_credentials(
    resolution: &Resolution<'_>,
    fields: &SsoProfileFields,
    token: &JsonValue,
) -> ProviderResult<AwsCredentials> {
    let wrap = |failure: ProviderFailure| {
        if resolution
            .signal
            .is_some_and(eukhe_chord::context::AbortSignal::aborted)
        {
            failure
        } else {
            ProviderFailure::credentials_final(js_error_string(&failure.error))
        }
    };
    let client = nested_client(
        resolution,
        &NestedClientConfig {
            service: AwsService::Sso,
            region: &fields.region,
            profile: None,
            proxy: None,
        },
    )
    .await
    .map_err(wrap)?;
    let mut headers = Vec::new();
    if !token.is_null() {
        headers.push(("x-amz-sso_bearer_token".to_owned(), js_to_string(token)));
    }
    let request = PreparedRequest {
        method: Method::GET,
        path_and_query: format!(
            "/federation/credentials?account_id={}&role_name={}",
            escape_uri(&fields.account_id),
            escape_uri(&fields.role_name)
        ),
        headers,
        body: Vec::new(),
        credentials: None,
        attempt_headers: None,
    };
    let response = client
        .send(resolution, &request, |reply| json_reply(&reply))
        .await
        .map_err(wrap)?;
    let role = response.get("roleCredentials");
    let field = |key: &str| {
        role.and_then(|role| role.get(key))
            .filter(|value| json_truthy(Some(value)))
    };
    match (
        field("accessKeyId"),
        field("secretAccessKey"),
        field("sessionToken"),
        field("expiration"),
    ) {
        (Some(access_key_id), Some(secret_access_key), Some(session_token), Some(_)) => {
            Ok(AwsCredentials {
                access_key_id: js_to_string(access_key_id),
                secret_access_key: js_to_string(secret_access_key),
                session_token: Some(js_to_string(session_token)),
            })
        }
        _ => Err(ProviderFailure::credentials_final(
            "SSO returns an invalid temporary credential.",
        )),
    }
}

/// `fromSSO({ profile })()` for a profile `fromIni` classified as SSO.
///
/// # Errors
///
/// `CredentialsProviderError`s for missing profiles (chain continues) and for
/// invalid configuration, tokens, or portal errors (chain stops).
pub(crate) async fn from_sso_profile(
    resolution: &Resolution<'_>,
    profile_name: &str,
) -> ProviderResult<AwsCredentials> {
    let env = resolution.env;
    let profiles = parse_known_files(env).await;
    let Some(profile) = profiles.get(profile_name) else {
        return Err(ProviderFailure::credentials(format!(
            "Profile {profile_name} was not found."
        )));
    };
    let is_sso = [
        "sso_start_url",
        "sso_account_id",
        "sso_session",
        "sso_region",
        "sso_role_name",
    ]
    .iter()
    .any(|key| profile.get(key).is_some());
    if !is_sso {
        return Err(ProviderFailure::credentials(format!(
            "Profile {profile_name} is not configured with SSO credentials."
        )));
    }
    let mut keys: Vec<String> = profile.keys().into_iter().map(str::to_owned).collect();
    let mut sso_region = profile.get("sso_region").map(str::to_owned);
    let mut sso_start_url = profile.get("sso_start_url").map(str::to_owned);
    if let Some(session_name) = profile.get("sso_session") {
        let sessions = load_sso_session_data(env).await;
        let Some(session) = sessions.get(session_name) else {
            return Err(ProviderFailure::error(ErrorObject::named(
                "TypeError",
                "Cannot read properties of undefined (reading 'sso_region')",
            )));
        };
        // `profile.sso_region = session.sso_region` (and the start URL)
        // define the keys even when the session lacks them.
        for key in ["sso_region", "sso_start_url"] {
            if !keys.iter().any(|existing| existing == key) {
                keys.push(key.to_owned());
            }
        }
        sso_region = session.get("sso_region").map(str::to_owned);
        sso_start_url = session.get("sso_start_url").map(str::to_owned);
    }
    let (Some(start_url), Some(account_id), Some(region), Some(role_name)) = (
        sso_start_url,
        profile.get("sso_account_id").map(str::to_owned),
        sso_region,
        profile.get("sso_role_name").map(str::to_owned),
    ) else {
        return Err(ProviderFailure::credentials_final(format!(
            "Profile is configured with invalid SSO credentials. Required parameters \"sso_account_id\", \"sso_region\", \"sso_role_name\", \"sso_start_url\". Got {}\nReference: https://docs.aws.amazon.com/cli/latest/userguide/cli-configure-sso.html",
            keys.join(", ")
        )));
    };
    let fields = SsoProfileFields {
        start_url,
        account_id,
        region,
        role_name,
        session: profile.get("sso_session").map(str::to_owned),
    };
    resolve_sso_credentials(resolution, profile_name, fields).await
}
