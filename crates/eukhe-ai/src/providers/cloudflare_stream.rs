//! Cloudflare endpoint placeholder materialization. Port of
//! `providers/cloudflare-stream.ts`.

use std::sync::Arc;

use crate::api::{ProviderClassifier, ProviderStreams};
use crate::models::{CatalogModel, RegistryStreamAuth};
use crate::types::ProviderEnv;

const CLOUDFLARE_ACCOUNT_ID: &str = "CLOUDFLARE_ACCOUNT_ID";
const CLOUDFLARE_GATEWAY_ID: &str = "CLOUDFLARE_GATEWAY_ID";

/// Cloudflare endpoints need the account/gateway env and credentials the
/// provider auth resolves; a caller credential rides in the API key or the
/// AI Gateway's `cf-aig-authorization` header.
pub(crate) const CLOUDFLARE_REGISTRY_STREAM_AUTH: RegistryStreamAuth = RegistryStreamAuth {
    credential_header: "cf-aig-authorization",
};

/// Replaces `{CLOUDFLARE_ACCOUNT_ID}` / `{CLOUDFLARE_GATEWAY_ID}` in the
/// model's base URL with values from `env`; placeholders without a value
/// stay. Returns the model unchanged without `env`.
#[must_use]
pub fn resolve_cloudflare_model<M: CatalogModel>(model: &M, env: Option<&ProviderEnv>) -> M {
    let Some(env) = env else {
        return model.clone();
    };
    let account = format!("{{{CLOUDFLARE_ACCOUNT_ID}}}");
    let gateway = format!("{{{CLOUDFLARE_GATEWAY_ID}}}");
    let base_url = model
        .model_base_url()
        .replace(&account, env.get(CLOUDFLARE_ACCOUNT_ID).unwrap_or(&account))
        .replace(&gateway, env.get(CLOUDFLARE_GATEWAY_ID).unwrap_or(&gateway));
    let mut resolved = model.clone();
    if base_url != model.model_base_url() {
        resolved.set_base_url(base_url);
    }
    resolved
}

/// Wrap an API implementation so Cloudflare account/gateway endpoint
/// placeholders materialize from the resolved provider env before dispatch.
#[must_use]
pub fn cloudflare_streams(streams: ProviderStreams) -> ProviderStreams {
    let simple = streams.stream_simple.clone();
    let stream = streams.stream;
    ProviderStreams {
        stream: Arc::new(move |model, context, options| {
            let resolved = resolve_cloudflare_model(model, options.stream.request.env.as_ref());
            stream(&resolved, context, options)
        }),
        stream_simple: Arc::new(move |model, context, options| {
            let resolved = resolve_cloudflare_model(model, options.stream.request.env.as_ref());
            simple(&resolved, context, options)
        }),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}

/// Classifier counterpart of [`cloudflare_streams`].
#[must_use]
pub fn cloudflare_classifier(classifier: ProviderClassifier) -> ProviderClassifier {
    let classify = classifier.classify;
    ProviderClassifier {
        classify: Arc::new(move |model, context, options| {
            let resolved = resolve_cloudflare_model(model, options.request.env.as_ref());
            classify(&resolved, context, options)
        }),
    }
}
