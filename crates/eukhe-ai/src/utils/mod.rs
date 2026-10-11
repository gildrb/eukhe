//! `src/utils/*`: transcript, estimation, retry, overflow, validation, JSON,
//! streaming, and provider helpers. Every module is public, like the TS
//! package's `./utils/*` export.

pub mod abort;
pub mod abort_signals;
pub mod assistant_message_frame;
pub mod diagnostics;
pub mod error_body;
pub mod estimate;
pub mod event_stream;
pub mod hash;
pub mod headers;
pub(crate) mod js;
pub mod json_parse;
pub mod model_operations;
pub mod models_error;
pub mod node_http_proxy;
pub mod oauth_page;
pub mod overflow;
pub mod pi_user_agent;
pub mod provider_env;
pub mod provider_retry;
pub mod retry;
pub mod sanitize_unicode;
pub mod sleep;
pub mod stream_failure;
#[cfg(test)]
pub(crate) mod test_support;
pub mod text;
pub mod transcript;
pub mod typebox_helpers;
pub mod uuid;
pub mod validation;

/// `Date.now()`: Unix time in milliseconds.
pub(crate) fn now_ms() -> u64 {
    let elapsed = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default();
    u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
}
