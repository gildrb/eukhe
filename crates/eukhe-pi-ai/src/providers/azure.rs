//! The `azure` provider. Port of `providers/azure.ts`.

use std::sync::Arc;

use eukhe_types::pi_ai::{IndexMap, JsonValue, Model};

use super::azure_models::AZURE_MODELS;
use super::chat_models;
use crate::api::azure_openai_config::{
    resolve_azure_base_url, resolve_deployment_name, AzureEndpointOptions,
};
use crate::api::builtin::{azure_openai_responses_api, openai_completions_api};
use crate::api::lazy::lazy_stream;
use crate::api::ProviderStreams;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};
use crate::types::{OnPayload, ProviderRequestOptions};
use crate::utils::diagnostics::Thrown;

fn resolve_azure_model(
    model: &Model,
    endpoint: &AzureEndpointOptions,
    request: &ProviderRequestOptions<Model>,
) -> Result<Model, Thrown> {
    let base_url = resolve_azure_base_url(&model.base_url, endpoint, request.env.as_ref())
        .map_err(|error| Arc::new(error) as Thrown)?;
    Ok(Model {
        base_url,
        ..model.clone()
    })
}

/// Send the deployment name as the request's model, keeping `model.id` as
/// the catalog id: wraps `on_payload` to set the payload's `model`.
fn with_deployment_name(
    model: &Model,
    endpoint: &AzureEndpointOptions,
    request: &mut ProviderRequestOptions<Model>,
) {
    let deployment_name = resolve_deployment_name(&model.id, endpoint, request.env.as_ref());
    if deployment_name == model.id {
        return;
    }
    let previous = request.on_payload.take();
    let on_payload: OnPayload<Model> =
        Arc::new(move |payload: JsonValue, payload_model: &Model| {
            let previous = previous.clone();
            let deployment_name = deployment_name.clone();
            Box::pin(async move {
                // `{ ...payload, model }`: spread copies own enumerable keys of
                // objects only.
                let mut params = match payload {
                    JsonValue::Object(object) => object,
                    JsonValue::Null
                    | JsonValue::Bool(_)
                    | JsonValue::Number(_)
                    | JsonValue::String(_)
                    | JsonValue::Array(_) => serde_json::Map::new(),
                };
                params.insert("model".to_owned(), JsonValue::String(deployment_name));
                let params = JsonValue::Object(params);
                let replaced = match &previous {
                    Some(previous) => previous(params.clone(), payload_model).await?,
                    None => None,
                };
                Ok(Some(replaced.unwrap_or(params)))
            })
        });
    request.on_payload = Some(on_payload);
}

/// Resolve the Azure endpoint and deployment before dispatch, inside
/// `lazy_stream` so an unconfigured endpoint errors on the stream instead of
/// failing out of `stream()`.
fn azure_streams(streams: ProviderStreams) -> ProviderStreams {
    let simple = streams.clone();
    ProviderStreams {
        stream: Arc::new(move |model, context, options| {
            let streams = streams.clone();
            let (request_model, context) = (model.clone(), context.clone());
            let mut options = options;
            lazy_stream(model, async move {
                let endpoint = AzureEndpointOptions::from_extra(&options.extra);
                let resolved =
                    resolve_azure_model(&request_model, &endpoint, &options.stream.request)?;
                with_deployment_name(&request_model, &endpoint, &mut options.stream.request);
                Ok((streams.stream)(&resolved, &context, options))
            })
        }),
        stream_simple: Arc::new(move |model, context, options| {
            let streams = simple.clone();
            let (request_model, context) = (model.clone(), context.clone());
            let mut options = options;
            lazy_stream(model, async move {
                // Simple options carry no API-specific keys.
                let endpoint = AzureEndpointOptions::default();
                let resolved =
                    resolve_azure_model(&request_model, &endpoint, &options.stream.request)?;
                with_deployment_name(&request_model, &endpoint, &mut options.stream.request);
                Ok((streams.stream_simple)(&resolved, &context, options))
            })
        }),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}

/// TS `azureProvider()`.
#[must_use]
pub fn azure_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "azure".to_owned(),
        name: Some("Azure".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "Azure OpenAI API key",
                &["AZURE_OPENAI_API_KEY"],
            )),
            oauth: None,
        },
        models: chat_models(&AZURE_MODELS),
        api: Some(ProviderApi::ByApi(IndexMap::from([
            (
                "azure-openai-responses".to_owned(),
                azure_openai_responses_api(),
            ),
            (
                "openai-completions".to_owned(),
                azure_streams(openai_completions_api()),
            ),
        ]))),
        ..CreateProviderOptions::default()
    })
}
