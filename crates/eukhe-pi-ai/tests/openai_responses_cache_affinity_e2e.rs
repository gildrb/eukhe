//! Port of `test/openai-responses-cache-affinity-e2e.test.ts`.

use eukhe_pi_ai::compat::{complete, get_model};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{AssistantContentBlock, Context, StopReason};
use serde_json::json;

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn handles_direct_openai_responses_requests_with_aligned_cache_affinity_identifiers() {
    let api_key = std::env::var("OPENAI_API_KEY").expect("OPENAI_API_KEY");
    let model = get_model("openai", "gpt-5.4").expect("model");
    let session_id = "0195d6e4-4cf9-7f44-a2d8-f8f7f49ee9d3";
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock")
        .as_millis();
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are a helpful assistant. Reply exactly as requested.",
        "messages": [{
            "role": "user",
            "content": "Reply with exactly: openai cache affinity e2e success",
            "timestamp": timestamp,
        }],
    }))
    .expect("context");

    // TS `{ retry: 2 }`: up to three attempts.
    let mut last_failure = String::new();
    for _ in 0..3 {
        let mut options = ProviderStreamOptions::default();
        options.stream.request.api_key = Some(api_key.clone());
        options.stream.session_id = Some(session_id.to_owned());
        let response = complete(&model, context.clone(), options)
            .await
            .expect("complete");

        let text: String = response
            .content
            .iter()
            .map(|block| match block {
                AssistantContentBlock::Text(text) => text.text.as_str(),
                _ => "",
            })
            .collect();
        if response.stop_reason != StopReason::Error
            && response.error_message.is_none()
            && text.contains("openai cache affinity e2e success")
        {
            return;
        }
        last_failure = format!(
            "stopReason={:?} errorMessage={:?} text={text:?}",
            response.stop_reason, response.error_message
        );
    }
    panic!("{last_failure}");
}
