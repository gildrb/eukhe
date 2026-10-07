//! Port of `test/bedrock-cache-write-1h-cost.test.ts`.

use eukhe_pi_ai::api::bedrock_converse_stream::stream;
use eukhe_types::pi_ai::CacheRetention;
use serde_json::json;

use super::support::{
    context_of, event_stream, get_model, mock_env, options, user, with_base_url, EnvGuard,
    MockBedrock, Reply,
};

#[tokio::test]
async fn prices_the_1h_cache_details_at_2x_while_preserving_the_total_cache_write() {
    // Regression test for https://github.com/earendil-works/pi/issues/9457
    let _env = EnvGuard::new(&[]).await;
    let server = MockBedrock::start(vec![Reply::events(
        &[],
        event_stream(&[
            json!({ "messageStart": { "role": "assistant" } }),
            json!({ "metadata": { "usage": {
                "inputTokens": 100,
                "outputTokens": 5,
                "totalTokens": 1_000_105,
                "cacheWriteInputTokens": 1_000_000,
                "cacheDetails": [
                    { "ttl": "1h", "inputTokens": 150_000 },
                    { "ttl": "5m", "inputTokens": 600_000 },
                    { "ttl": "1h", "inputTokens": 250_000 },
                ],
            } } }),
            json!({ "messageStop": { "stopReason": "end_turn" } }),
        ]),
    )])
    .await;
    let model = with_base_url(
        &get_model("amazon-bedrock", "us.anthropic.claude-opus-4-8"),
        &server.url,
    );
    let mut options = options(json!({}));
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.env = Some(mock_env());

    let result = stream(&model, &context_of(vec![user("hi")]), options)
        .result()
        .await;

    assert_eq!(result.usage.cache_write, 1_000_000);
    assert_eq!(result.usage.cache_write_1h, Some(400_000));
    let expected_cache_write_cost =
        (600_000.0 * model.cost.cache_write + 400_000.0 * model.cost.input * 2.0) / 1_000_000.0;
    assert!((result.usage.cost.cache_write - expected_cache_write_cost).abs() < 5e-11);
}
