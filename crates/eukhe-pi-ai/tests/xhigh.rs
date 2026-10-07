//! Port of `test/xhigh.test.ts`: real `OpenAI` endpoint cases (TS
//! `describe.skipIf(!process.env.OPENAI_API_KEY)`).

use eukhe_pi_ai::compat::{get_model, stream};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, Context, Message, Model,
    StopReason, UserContent, UserMessage,
};
use futures::StreamExt;

fn make_context() -> Context {
    let timestamp = u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|duration| duration.as_millis())
            .unwrap_or_default(),
    )
    .unwrap_or_default();
    let (a, b) = (
        rand::random_range(0..100_u32),
        rand::random_range(0..100_u32),
    );
    Context {
        system_prompt: None,
        messages: vec![Message::User(UserMessage {
            content: UserContent::Text(format!("What is {a} + {b}? Think step by step.")),
            timestamp,
        })],
        tools: None,
    }
}

fn xhigh_options() -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options
        .extra
        .insert("reasoningEffort".to_owned(), "xhigh".into());
    options
}

/// Streams `model` with `reasoningEffort: "xhigh"`; returns whether a
/// thinking event arrived and the final message.
async fn run(model: &Model) -> (bool, AssistantMessage) {
    let events = stream(model, make_context(), xhigh_options()).expect("stream");
    let mut has_thinking = false;
    let mut iter = events.events();
    while let Some(event) = iter.next().await {
        if matches!(
            event,
            AssistantMessageEvent::ThinkingStart { .. }
                | AssistantMessageEvent::ThinkingDelta { .. }
        ) {
            has_thinking = true;
        }
    }
    (has_thinking, events.result().await)
}

// Note: codex models only support the responses API, not chat completions.
#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn should_work_with_openai_responses() {
    let model = get_model("openai", "gpt-5.5").expect("model");
    let (has_thinking, response) = run(&model).await;

    assert_eq!(
        response.stop_reason,
        StopReason::Stop,
        "Error: {:?}",
        response.error_message
    );
    assert!(response
        .content
        .iter()
        .any(|block| matches!(block, AssistantContentBlock::Text(_))));
    assert!(
        has_thinking
            || response
                .content
                .iter()
                .any(|block| matches!(block, AssistantContentBlock::Thinking(_)))
    );
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn should_error_with_openai_responses_when_using_xhigh() {
    let model = get_model("openai", "gpt-5-mini").expect("model");
    let (_, response) = run(&model).await;

    assert_eq!(response.stop_reason, StopReason::Error);
    assert!(response
        .error_message
        .as_deref()
        .is_some_and(|message| message.contains("xhigh")));
}

#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn should_error_with_openai_completions_when_using_xhigh() {
    let model = Model {
        api: "openai-completions".to_owned(),
        compat: None,
        ..get_model("openai", "gpt-5-mini").expect("model")
    };
    let (_, response) = run(&model).await;

    assert_eq!(response.stop_reason, StopReason::Error);
    assert!(response
        .error_message
        .as_deref()
        .is_some_and(|message| message.contains("xhigh")));
}
