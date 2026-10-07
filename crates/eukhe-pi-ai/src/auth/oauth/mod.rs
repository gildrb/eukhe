//! Built-in OAuth flows and their shared pieces (PKCE, loopback callback
//! server, device-code polling). Port of `auth/oauth/*`.

mod anthropic;
mod callback_server;
mod device_code;
mod github_copilot;
mod http;
mod kimi_coding;
mod load;
mod meta;
mod openai_chatgpt;
mod openai_codex;
mod openrouter;
mod pkce;
mod radius;
#[cfg(test)]
mod test_support;
mod xai;

use std::sync::Arc;

pub use anthropic::anthropic_oauth;
pub use callback_server::{
    start_oauth_callback_server, wait_for_callback_or_manual_input, CallbackOrManual, CompleteFn,
    OAuthCallbackServer, OAuthCallbackServerOptions,
};
pub use device_code::{
    abortable_sleep, poll_oauth_device_code_flow, OAuthDeviceCodePollOptions,
    OAuthDeviceCodePollResult,
};
pub use github_copilot::github_copilot_oauth;
pub use kimi_coding::kimi_coding_oauth;
pub use load::{
    load_anthropic_oauth, load_github_copilot_oauth, load_kimi_coding_oauth, load_meta_oauth,
    load_openai_chatgpt_oauth, load_openai_codex_oauth, load_openrouter_oauth, load_radius_oauth,
    load_xai_oauth,
};
pub use meta::meta_oauth;
pub use openai_chatgpt::openai_chatgpt_oauth;
pub use openai_codex::openai_codex_oauth;
pub use openrouter::open_router_oauth;
pub use pkce::{generate_pkce, Pkce};
pub use radius::{create_radius_oauth, RadiusOAuthOptions};
pub use xai::xai_oauth;

use crate::auth::types::ModelAuth;
use crate::utils::diagnostics::Thrown;

/// A code (and state) pasted by the user.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct AuthorizationInput {
    pub(crate) code: Option<String>,
    pub(crate) state: Option<String>,
}

/// Parse a pasted redirect URL, `code#state`, query string, or bare code
/// (the `parseAuthorizationInput` shared by the Anthropic and Codex flows).
pub(crate) fn parse_authorization_input(input: &str) -> AuthorizationInput {
    let value = input.trim();
    if value.is_empty() {
        return AuthorizationInput::default();
    }

    if let Ok(url) = url::Url::parse(value) {
        return AuthorizationInput {
            code: callback_server_query(&url, "code"),
            state: callback_server_query(&url, "state"),
        };
    }

    if value.contains('#') {
        let mut parts = value.split('#');
        return AuthorizationInput {
            code: parts.next().map(str::to_owned),
            state: parts.next().map(str::to_owned),
        };
    }

    if value.contains("code=") {
        let params = query_pairs(value);
        return AuthorizationInput {
            code: first_param(&params, "code"),
            state: first_param(&params, "state"),
        };
    }

    AuthorizationInput {
        code: Some(value.to_owned()),
        state: None,
    }
}

fn callback_server_query(url: &url::Url, name: &str) -> Option<String> {
    callback_server::query_param(url, name)
}

/// `new URLSearchParams(value)` pairs (a leading `?` is ignored).
pub(crate) fn query_pairs(value: &str) -> Vec<(String, String)> {
    let value = value.strip_prefix('?').unwrap_or(value);
    url::form_urlencoded::parse(value.as_bytes())
        .into_owned()
        .collect()
}

/// `params.get(name)`.
pub(crate) fn first_param(params: &[(String, String)], name: &str) -> Option<String> {
    params
        .iter()
        .find(|(key, _)| key == name)
        .map(|(_, value)| value.clone())
}

/// `{ apiKey: credential.access }`.
pub(crate) fn api_key_auth(access: &str) -> ModelAuth {
    ModelAuth {
        api_key: Some(access.to_owned()),
        ..ModelAuth::default()
    }
}

/// The JS `error.name` of a thrown value.
pub(crate) fn error_name(error: &Thrown) -> String {
    crate::utils::diagnostics::error_name(error.as_ref())
}

/// `Arc` of a fresh flow, the TS module-level `const xOAuth: OAuthAuth`.
pub(crate) fn shared<T: crate::auth::types::OAuthAuth + 'static>(
    auth: T,
) -> Arc<dyn crate::auth::types::OAuthAuth> {
    Arc::new(auth)
}

/// A JSON field that is a non-empty string (the TS truthiness check).
pub(crate) fn truthy_str<'a>(json: &'a serde_json::Value, field: &str) -> Option<&'a str> {
    json.get(field)
        .and_then(serde_json::Value::as_str)
        .filter(|value| !value.is_empty())
}

/// A JSON field that is a string (TS `typeof x === "string"`).
pub(crate) fn string_field<'a>(json: &'a serde_json::Value, field: &str) -> Option<&'a str> {
    json.get(field).and_then(serde_json::Value::as_str)
}

/// A JSON field that is a finite positive number.
pub(crate) fn positive_number(json: &serde_json::Value, field: &str) -> Option<f64> {
    json.get(field)
        .and_then(serde_json::Value::as_f64)
        .filter(|value| value.is_finite() && *value > 0.0)
}

/// JS `Number(value.trim())` for a string: empty is 0, unparsable is NaN.
pub(crate) fn js_number_from_string(value: &str) -> f64 {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        return 0.0;
    }
    trimmed.parse::<f64>().unwrap_or(f64::NAN)
}

/// `JSON.parse(atob(token.split(".")[1]))` for a three-part JWT; `None` when
/// anything fails. `atob` yields one char per byte (Latin-1).
pub(crate) fn decode_jwt_payload(token: &str) -> Option<serde_json::Value> {
    use base64::engine::{DecodePaddingMode, GeneralPurpose, GeneralPurposeConfig};
    use base64::Engine as _;

    const FORGIVING: GeneralPurpose = GeneralPurpose::new(
        &base64::alphabet::STANDARD,
        GeneralPurposeConfig::new().with_decode_padding_mode(DecodePaddingMode::Indifferent),
    );
    let parts: Vec<&str> = token.split('.').collect();
    if parts.len() != 3 {
        return None;
    }
    let bytes = FORGIVING.decode(parts[1]).ok()?;
    let decoded: String = bytes.iter().map(|&byte| char::from(byte)).collect();
    serde_json::from_str(&decoded).ok()
}

/// `new URL(value)` restricted to http(s): the parsed href, else `None`.
pub(crate) fn trusted_http_url(value: Option<&serde_json::Value>) -> Option<String> {
    let value = value?.as_str().filter(|value| !value.is_empty())?;
    let url = url::Url::parse(value).ok()?;
    matches!(url.scheme(), "https" | "http").then(|| url.to_string())
}
