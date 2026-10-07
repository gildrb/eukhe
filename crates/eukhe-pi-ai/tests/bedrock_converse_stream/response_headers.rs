//! Port of `test/bedrock-response-headers.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::api::bedrock_converse_stream::stream;
use eukhe_types::pi_ai::{CacheRetention, ProviderResponse, StopReason};
use serde_json::json;

use super::support::{
    context_of, env, get_model, options, user, with_base_url, EnvGuard, MockBedrock, Reply,
};

const MODEL_ID: &str = "us.anthropic.claude-haiku-4-5-20251001-v1:0";

#[tokio::test]
async fn forwards_raw_smithy_response_headers_to_on_response() {
    let _env = EnvGuard::new(&[]).await;
    let server = MockBedrock::start(vec![Reply::events(
        &[
            ("x-bifrost-provider", "bedrock"),
            ("x-bifrost-resolved-model", MODEL_ID),
            ("x-amzn-requestid", "req-123"),
        ],
        Vec::new(),
    )])
    .await;
    let model = with_base_url(&get_model("amazon-bedrock", MODEL_ID), &server.url);
    let responses: Arc<Mutex<Vec<ProviderResponse>>> = Arc::default();
    let recorded = responses.clone();
    let mut options = options(json!({}));
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.env = Some(env(&[
        ("AWS_BEDROCK_FORCE_HTTP1", "1"),
        ("AWS_BEDROCK_SKIP_AUTH", "1"),
    ]));
    options.stream.request.on_response = Some(Arc::new(move |response, _model| {
        let recorded = recorded.clone();
        Box::pin(async move {
            recorded
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(response);
            Ok(())
        })
    }));

    let result = stream(&model, &context_of(vec![user("hello")]), options)
        .result()
        .await;

    // The empty event stream documents that the callback fires before the
    // stream is consumed.
    assert_eq!(result.stop_reason, StopReason::Error);
    let responses = responses
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(responses.len(), 1);
    assert_eq!(responses[0].status, 200);
    assert_eq!(
        responses[0]
            .headers
            .get("x-amzn-requestid")
            .map(String::as_str),
        Some("req-123")
    );
    assert_eq!(
        responses[0]
            .headers
            .get("x-bifrost-provider")
            .map(String::as_str),
        Some("bedrock")
    );
    assert_eq!(
        responses[0]
            .headers
            .get("x-bifrost-resolved-model")
            .map(String::as_str),
        Some(MODEL_ID)
    );
}
