//! Per-model wire API routing of a provider (per-provider API routes,
//! applied per request). A catalog entry names one
//! API (`model.api`), and the bundled catalog snapshot can restate it; a
//! route moves the request of a matching model to another API at dispatch,
//! so the request takes the routed API whatever API the catalog names.

use std::sync::Arc;

use crate::api::ProviderStreams;
use crate::types::Model;

/// A route: the model the target API streams, or `None` when the request
/// stays on the API the catalog names.
pub type Route = fn(&Model) -> Option<Model>;

/// `default` with the models `route` matches moved to `target`.
#[must_use]
pub fn routed_streams(
    default: ProviderStreams,
    target: ProviderStreams,
    route: Route,
) -> ProviderStreams {
    let default_stream = default.stream;
    let default_simple = default.stream_simple;
    let target_stream = target.stream;
    let target_simple = target.stream_simple;
    ProviderStreams {
        stream: Arc::new(move |model, context, options| match route(model) {
            Some(routed) => target_stream(&routed, context, options),
            None => default_stream(model, context, options),
        }),
        stream_simple: Arc::new(move |model, context, options| match route(model) {
            Some(routed) => target_simple(&routed, context, options),
            None => default_simple(model, context, options),
        }),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}

/// `target` for every model of a catalog API, each request's model
/// rewritten by `rewrite` first.
#[must_use]
pub fn moved_streams(target: ProviderStreams, rewrite: fn(&Model) -> Model) -> ProviderStreams {
    let target_stream = target.stream;
    let target_simple = target.stream_simple;
    ProviderStreams {
        stream: Arc::new(move |model, context, options| {
            target_stream(&rewrite(model), context, options)
        }),
        stream_simple: Arc::new(move |model, context, options| {
            target_simple(&rewrite(model), context, options)
        }),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}
