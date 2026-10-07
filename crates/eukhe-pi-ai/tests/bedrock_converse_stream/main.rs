//! Ports of the `test/bedrock-*.test.ts` files (and `bedrock-utils.ts`).
//! The TS tests mock `@aws-sdk/client-bedrock-runtime`; here a local server
//! speaks the Bedrock HTTP and event-stream protocol instead, and the
//! client-config assertions read [`client_config`], the configuration the
//! TS module passes to `new BedrockRuntimeClient`.
//!
//! [`client_config`]: eukhe_pi_ai::api::bedrock_converse_stream::client_config

mod cache_write_1h_cost;
mod convert_messages;
mod credentials;
mod custom_headers;
mod endpoint_resolution;
mod error_metadata;
mod raw_stop_reason;
mod redacted_reasoning;
mod response_headers;
mod support;
mod thinking_payload;

/// TS `hasBedrockCredentials()` (`bedrock-utils.ts`): any AWS credential
/// source configured in the environment.
#[must_use]
pub fn has_bedrock_credentials() -> bool {
    let set = |name: &str| std::env::var(name).is_ok_and(|value| !value.is_empty());
    set("AWS_PROFILE")
        || (set("AWS_ACCESS_KEY_ID") && set("AWS_SECRET_ACCESS_KEY"))
        || set("AWS_BEARER_TOKEN_BEDROCK")
}
