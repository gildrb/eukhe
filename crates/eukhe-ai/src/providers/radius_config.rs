//! Radius gateway configuration: gateway URL normalization, the model list
//! carried on Radius OAuth credentials, and the `/v1/config` loader. Port of
//! `providers/radius-config.ts`.

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{JsonObject, JsonValue, Model};

use crate::auth::OAuthCredential;
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::js::{js_trim, utf16_len, utf16_prefix};

/// Default Radius gateway.
pub const DEFAULT_RADIUS_GATEWAY: &str = "https://radius.pi.dev";

/// A gateway model entry (TS `RadiusGatewayModel`), kept as its JSON object:
/// the TS sanitizer copies every key of a valid entry (`{ ...model }`).
pub type RadiusGatewayModel = JsonObject;

/// The gateway's model configuration: TS `RadiusGatewayConfig`.
#[derive(Debug, Clone, PartialEq)]
pub struct RadiusGatewayConfig {
    pub base_url: String,
    pub models: Vec<RadiusGatewayModel>,
}

/// Field checks of TS `isRadiusGatewayModel`.
fn is_radius_gateway_model(value: &JsonValue) -> bool {
    let Some(model) = value.as_object() else {
        return false;
    };
    model.get("id").is_some_and(JsonValue::is_string)
        && model.get("name").is_some_and(JsonValue::is_string)
        && model.get("reasoning").is_some_and(JsonValue::is_boolean)
        && model.get("input").is_some_and(JsonValue::is_array)
        && model.get("cost").is_some_and(JsonValue::is_object)
        && model.get("contextWindow").is_some_and(JsonValue::is_number)
        && model.get("maxTokens").is_some_and(JsonValue::is_number)
}

fn sanitize_radius_gateway_config(config: Option<&JsonValue>) -> Option<RadiusGatewayConfig> {
    let config = config?.as_object()?;
    let base_url = config.get("baseUrl")?.as_str()?;
    let models = config.get("models")?.as_array()?;
    Some(RadiusGatewayConfig {
        base_url: base_url.to_owned(),
        models: models
            .iter()
            .filter(|model| is_radius_gateway_model(model))
            .filter_map(|model| model.as_object().cloned())
            .collect(),
    })
}

/// Adds `https://` when the value has no `http://`/`https://` scheme
/// (case-insensitive) and strips trailing slashes.
#[must_use]
pub fn normalize_radius_gateway_url(value: &str) -> String {
    let has_scheme = starts_with_ignore_ascii_case(value, "https://")
        || starts_with_ignore_ascii_case(value, "http://");
    let with_scheme = if has_scheme {
        value.to_owned()
    } else {
        format!("https://{value}")
    };
    with_scheme.trim_end_matches('/').to_owned()
}

fn starts_with_ignore_ascii_case(value: &str, prefix: &str) -> bool {
    value
        .as_bytes()
        .get(..prefix.len())
        .is_some_and(|head| head.eq_ignore_ascii_case(prefix.as_bytes()))
}

/// The sanitized `gatewayConfig` stored on a Radius OAuth credential.
#[must_use]
pub fn get_radius_credential_config(
    credential: Option<&OAuthCredential>,
) -> Option<RadiusGatewayConfig> {
    sanitize_radius_gateway_config(credential?.extra.get("gatewayConfig"))
}

/// Chat models of a gateway config: `{ ...model, api: "pi-messages",
/// provider, baseUrl }`. Entries that do not form a chat model (for example
/// an unknown input modality) are skipped.
#[must_use]
pub fn get_radius_models_from_config(
    provider_id: &str,
    config: &RadiusGatewayConfig,
) -> Vec<Model> {
    config
        .models
        .iter()
        .filter_map(|model| {
            let mut entry = model.clone();
            entry.insert("api".to_owned(), JsonValue::from("pi-messages"));
            entry.insert("provider".to_owned(), JsonValue::from(provider_id));
            entry.insert(
                "baseUrl".to_owned(),
                JsonValue::from(config.base_url.clone()),
            );
            serde_json::from_value(JsonValue::Object(entry)).ok()
        })
        .collect()
}

/// Models of the gateway config stored on `credential`, or none.
#[must_use]
pub fn get_radius_models(provider_id: &str, credential: Option<&OAuthCredential>) -> Vec<Model> {
    get_radius_credential_config(credential)
        .map(|config| get_radius_models_from_config(provider_id, &config))
        .unwrap_or_default()
}

fn truncate_http_body(body: &str) -> String {
    let trimmed = js_trim(body);
    if utf16_len(trimmed) > 512 {
        format!("{}…", utf16_prefix(trimmed, 512))
    } else {
        trimmed.to_owned()
    }
}

fn error(message: String) -> Thrown {
    ErrorObject::new(message).thrown()
}

async fn fetch_config(gateway: &str, api_key: Option<&str>) -> Result<RadiusGatewayConfig, Thrown> {
    let url = url::Url::parse(gateway)
        .and_then(|base| base.join("/v1/config"))
        .map_err(|_| ErrorObject::named("TypeError", "Invalid URL").thrown())?;
    let mut request = reqwest::Client::new()
        .get(url)
        .header("accept", "application/json");
    if let Some(api_key) = api_key.filter(|key| !key.is_empty()) {
        request = request.header("authorization", format!("Bearer {api_key}"));
    }
    let response = request
        .send()
        .await
        .map_err(|error| ErrorObject::named("TypeError", error.to_string()).thrown())?;
    let status = response.status();
    if !status.is_success() {
        let body = response
            .text()
            .await
            .map_err(|error| ErrorObject::named("TypeError", error.to_string()).thrown())?;
        return Err(error(format!(
            "Could not load Radius config from {gateway}: {}: {}",
            status.as_u16(),
            truncate_http_body(&body)
        )));
    }
    let body: JsonValue = response
        .json()
        .await
        .map_err(|error| ErrorObject::named("SyntaxError", error.to_string()).thrown())?;
    sanitize_radius_gateway_config(Some(&body))
        .ok_or_else(|| error(format!("Invalid Radius config from {gateway}")))
}

/// Fetches `GET <gateway>/v1/config` (with a bearer key when given) and
/// sanitizes it.
///
/// # Errors
///
/// Network or HTTP failures, invalid JSON or config, or the abort reason
/// when `signal` aborts.
pub async fn load_radius_gateway_config(
    gateway: &str,
    api_key: Option<&str>,
    signal: Option<&AbortSignal>,
) -> Result<RadiusGatewayConfig, Thrown> {
    let Some(signal) = signal else {
        return fetch_config(gateway, api_key).await;
    };
    signal.throw_if_aborted()?;
    tokio::select! {
        result = fetch_config(gateway, api_key) => result,
        reason = signal.cancelled() => Err(reason),
    }
}
