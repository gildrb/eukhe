//! Azure `OpenAI` endpoint and deployment resolution, shared by the
//! `azure-openai-responses` API and the Azure provider's
//! `openai-completions` wrapper. Port of `api/azure-openai-config.ts`.

use serde_json::{Map, Value};

use crate::types::ProviderEnv;
use crate::utils::provider_env::get_provider_env_value;

const DEFAULT_AZURE_API_VERSION: &str = "v1";

/// Azure models ship without a baseUrl: one resource per user, resolved per
/// request. TS `AzureEndpointOptions` (the Azure-specific keys of the stream
/// options), read from the API-specific option keys.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AzureEndpointOptions {
    pub azure_api_version: Option<String>,
    pub azure_resource_name: Option<String>,
    pub azure_base_url: Option<String>,
    pub azure_deployment_name: Option<String>,
}

impl AzureEndpointOptions {
    /// Reads the camelCase Azure keys (`azureApiVersion`, ...) from
    /// API-specific stream options. Non-string values are ignored.
    #[must_use]
    pub fn from_extra(extra: &Map<String, Value>) -> Self {
        let read = |key: &str| extra.get(key).and_then(Value::as_str).map(str::to_owned);
        Self {
            azure_api_version: read("azureApiVersion"),
            azure_resource_name: read("azureResourceName"),
            azure_base_url: read("azureBaseUrl"),
            azure_deployment_name: read("azureDeploymentName"),
        }
    }
}

/// An unparseable Azure base URL or a missing endpoint.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum AzureConfigError {
    #[error("Invalid Azure OpenAI base URL: {0}")]
    InvalidBaseUrl(String),
    #[error(
        "Azure OpenAI base URL is required. Set AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME, or pass azureBaseUrl, azureResourceName, or model.baseUrl."
    )]
    MissingBaseUrl,
}

fn non_empty(value: Option<&String>) -> Option<&str> {
    value.map(String::as_str).filter(|value| !value.is_empty())
}

fn parse_deployment_name_map(value: Option<&str>) -> Vec<(String, String)> {
    let mut map: Vec<(String, String)> = Vec::new();
    let Some(value) = value else { return map };
    for entry in value.split(',') {
        let trimmed = entry.trim();
        if trimmed.is_empty() {
            continue;
        }
        // JS `split("=", 2)`: at most the first two pieces.
        let mut pieces = trimmed.split('=');
        let model_id = pieces.next().unwrap_or_default();
        let deployment_name = pieces.next().unwrap_or_default();
        if model_id.is_empty() || deployment_name.is_empty() {
            continue;
        }
        let model_id = model_id.trim().to_owned();
        let deployment_name = deployment_name.trim().to_owned();
        // JS `Map.set`: a repeated id keeps its first position, last value.
        if let Some(existing) = map.iter_mut().find(|(id, _)| *id == model_id) {
            existing.1 = deployment_name;
        } else {
            map.push((model_id, deployment_name));
        }
    }
    map
}

/// The deployment to send as the request's model: the explicit option, else
/// the `AZURE_OPENAI_DEPLOYMENT_NAME_MAP` entry for `model_id`, else the id.
#[must_use]
pub fn resolve_deployment_name(
    model_id: &str,
    options: &AzureEndpointOptions,
    env: Option<&ProviderEnv>,
) -> String {
    if let Some(name) = non_empty(options.azure_deployment_name.as_ref()) {
        return name.to_owned();
    }
    let map_value = get_provider_env_value("AZURE_OPENAI_DEPLOYMENT_NAME_MAP", env);
    parse_deployment_name_map(map_value.as_deref())
        .into_iter()
        .find(|(id, _)| id == model_id)
        .map(|(_, deployment)| deployment)
        .filter(|deployment| !deployment.is_empty())
        .unwrap_or_else(|| model_id.to_owned())
}

fn normalize_azure_base_url(base_url: &str) -> Result<String, AzureConfigError> {
    let trimmed = base_url.trim().trim_end_matches('/');
    let mut url = url::Url::parse(trimmed)
        .map_err(|_| AzureConfigError::InvalidBaseUrl(base_url.to_owned()))?;

    let host = url.host_str().unwrap_or_default();
    let is_azure_host = host.ends_with(".openai.azure.com")
        || host.ends_with(".cognitiveservices.azure.com")
        || host.ends_with(".ai.azure.com");
    let normalized_path = url.path().trim_end_matches('/').to_owned();

    // Ensure Azure hosts have /openai/v1 as base path so the request can
    // append /deployments/<model>/... and ?api-version=v1 correctly.
    if is_azure_host
        && matches!(
            normalized_path.as_str(),
            "" | "/" | "/openai" | "/openai/v1/responses"
        )
    {
        url.set_path("/openai/v1");
        url.set_query(None);
    }

    Ok(url.as_str().trim_end_matches('/').to_owned())
}

fn build_default_base_url(resource_name: &str) -> String {
    format!("https://{resource_name}.openai.azure.com/openai/v1")
}

/// Resolves the Azure endpoint: explicit option, `AZURE_OPENAI_BASE_URL`,
/// the resource-name default, then `model_base_url`.
///
/// # Errors
///
/// Fails when no endpoint is configured or the endpoint does not parse.
pub fn resolve_azure_base_url(
    model_base_url: &str,
    options: &AzureEndpointOptions,
    env: Option<&ProviderEnv>,
) -> Result<String, AzureConfigError> {
    let base_url = options
        .azure_base_url
        .as_deref()
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(str::to_owned)
        .or_else(|| {
            get_provider_env_value("AZURE_OPENAI_BASE_URL", env)
                .map(|value| value.trim().to_owned())
                .filter(|value| !value.is_empty())
        });
    let resource_name = non_empty(options.azure_resource_name.as_ref())
        .map(str::to_owned)
        .or_else(|| get_provider_env_value("AZURE_OPENAI_RESOURCE_NAME", env));

    let resolved = base_url
        .or_else(|| resource_name.as_deref().map(build_default_base_url))
        .or_else(|| (!model_base_url.is_empty()).then(|| model_base_url.to_owned()))
        .ok_or(AzureConfigError::MissingBaseUrl)?;

    normalize_azure_base_url(&resolved)
}

/// Resolved Azure endpoint and API version.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AzureConfig {
    pub base_url: String,
    pub api_version: String,
}

/// Resolves the endpoint and API version (`azureApiVersion`,
/// `AZURE_OPENAI_API_VERSION`, else `v1`).
///
/// # Errors
///
/// Fails like [`resolve_azure_base_url`].
pub fn resolve_azure_config(
    model_base_url: &str,
    options: &AzureEndpointOptions,
    env: Option<&ProviderEnv>,
) -> Result<AzureConfig, AzureConfigError> {
    Ok(AzureConfig {
        base_url: resolve_azure_base_url(model_base_url, options, env)?,
        api_version: non_empty(options.azure_api_version.as_ref())
            .map(str::to_owned)
            .or_else(|| get_provider_env_value("AZURE_OPENAI_API_VERSION", env))
            .unwrap_or_else(|| DEFAULT_AZURE_API_VERSION.to_owned()),
    })
}
