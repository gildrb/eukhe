//! Port of `test/bedrock-models.test.ts`. The per-model live requests (TS
//! registers them only with AWS credentials and
//! `BEDROCK_EXTENSIVE_MODEL_TEST`) run as one ignored test over every model.

mod common;

use common::now;
use eukhe_pi_ai::compat::{complete, get_models};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, Context, Message, Model, UserContent, UserMessage,
};

fn models() -> Vec<Model> {
    get_models("amazon-bedrock")
}

#[test]
fn should_get_all_available_bedrock_models() {
    let models = models();
    assert!(!models.is_empty());
    println!("Found {} Bedrock models", models.len());
}

#[test]
fn exposes_claude_opus_5_through_an_inference_profile_only() {
    let models = models();
    assert!(models
        .iter()
        .any(|model| model.id == "global.anthropic.claude-opus-5"));
    assert!(!models
        .iter()
        .any(|model| model.id == "anthropic.claude-opus-5"));
}

#[tokio::test]
#[ignore = "needs AWS credentials and BEDROCK_EXTENSIVE_MODEL_TEST; run with --ignored"]
async fn should_make_a_simple_request_with_each_model() {
    for model in models() {
        let context = Context {
            system_prompt: Some("You are a helpful assistant. Be extremely concise.".into()),
            messages: vec![Message::User(UserMessage {
                content: UserContent::Text("Reply with exactly: 'OK'".into()),
                timestamp: now(),
            })],
            tools: None,
        };

        let response = tokio::time::timeout(
            std::time::Duration::from_secs(10),
            complete(&model, context, ProviderStreamOptions::default()),
        )
        .await
        .unwrap_or_else(|_| panic!("{} timed out", model.id))
        .unwrap_or_else(|error| panic!("{}: {error:?}", model.id));

        assert!(!response.content.is_empty(), "{}", model.id);
        assert!(
            response.usage.input + response.usage.cache_read > 0,
            "{}",
            model.id
        );
        assert!(response.usage.output > 0, "{}", model.id);
        assert!(
            response
                .error_message
                .as_deref()
                .unwrap_or_default()
                .is_empty(),
            "{}: {:?}",
            model.id,
            response.error_message
        );

        let text_content: String = response
            .content
            .iter()
            .filter_map(|block| match block {
                AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                _ => None,
            })
            .collect::<String>()
            .trim()
            .to_owned();
        assert!(!text_content.is_empty(), "{}", model.id);
        println!(
            "{}: {}",
            model.id,
            text_content.chars().take(100).collect::<String>()
        );
    }
}
