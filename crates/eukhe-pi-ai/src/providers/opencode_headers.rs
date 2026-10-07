//! `OpenCode`'s per-conversation routing header. Port of
//! `providers/opencode-headers.ts`.

use std::sync::Arc;

use eukhe_types::pi_ai::{Model, ProviderHeaders};

use crate::api::ProviderStreams;
use crate::types::StreamOptions;

const OPENCODE_SESSION_HEADER: &str = "x-opencode-session";

fn has_header(headers: Option<&ProviderHeaders>, name: &str) -> bool {
    let expected = name.to_lowercase();
    headers
        .into_iter()
        .flatten()
        .any(|(key, _)| key.to_lowercase() == expected)
}

fn with_session_header(options: &mut StreamOptions) {
    let Some(session_id) = options.session_id.clone().filter(|id| !id.is_empty()) else {
        return;
    };
    if has_header(options.request.headers.as_ref(), OPENCODE_SESSION_HEADER) {
        return;
    }
    options
        .request
        .headers
        .get_or_insert_with(ProviderHeaders::new)
        .insert(OPENCODE_SESSION_HEADER.to_owned(), Some(session_id));
}

/// Adds `OpenCode`'s required per-conversation routing header before API
/// dispatch.
#[must_use]
pub fn with_opencode_session_header(streams: ProviderStreams) -> ProviderStreams {
    let stream = Arc::clone(&streams.stream);
    let stream_simple = Arc::clone(&streams.stream_simple);
    ProviderStreams {
        stream: Arc::new(move |model: &Model, context, mut options| {
            with_session_header(&mut options.stream);
            stream(model, context, options)
        }),
        stream_simple: Arc::new(move |model: &Model, context, mut options| {
            with_session_header(&mut options.stream);
            stream_simple(model, context, options)
        }),
        // `{ ...streams, ... }` keeps the deferred methods.
        fetch_deferred: streams.fetch_deferred,
        cancel_deferred: streams.cancel_deferred,
    }
}
