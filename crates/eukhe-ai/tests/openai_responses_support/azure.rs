//! Utility functions for Azure `OpenAI` tests. Port of `test/azure-utils.ts`.

use std::collections::HashMap;

fn env_value(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

fn parse_deployment_name_map(value: Option<&str>) -> HashMap<String, String> {
    let mut map = HashMap::new();
    let Some(value) = value.filter(|value| !value.is_empty()) else {
        return map;
    };
    for entry in value.split(',') {
        let trimmed = entry.trim();
        if trimmed.is_empty() {
            continue;
        }
        let mut parts = trimmed.split('=');
        let (Some(model_id), Some(deployment_name)) = (parts.next(), parts.next()) else {
            continue;
        };
        if model_id.is_empty() || deployment_name.is_empty() {
            continue;
        }
        map.insert(
            model_id.trim().to_owned(),
            deployment_name.trim().to_owned(),
        );
    }
    map
}

/// TS `hasAzureOpenAICredentials`.
pub fn has_azure_openai_credentials() -> bool {
    let has_key = env_value("AZURE_OPENAI_API_KEY").is_some();
    let has_base_url = env_value("AZURE_OPENAI_BASE_URL").is_some()
        || env_value("AZURE_OPENAI_RESOURCE_NAME").is_some();
    has_key && has_base_url
}

/// TS `resolveAzureDeploymentName`.
pub fn resolve_azure_deployment_name(model_id: &str) -> Option<String> {
    let map_value = env_value("AZURE_OPENAI_DEPLOYMENT_NAME_MAP")?;
    parse_deployment_name_map(Some(&map_value)).remove(model_id)
}
