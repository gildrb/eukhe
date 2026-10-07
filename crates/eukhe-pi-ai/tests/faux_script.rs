//! eukhe addition: the faux-script format (port of the old
//! `eukhe-ai/src/providers/faux/script.rs` and its tests).

use std::time::Duration;

use eukhe_chord::context::AbortController;
use eukhe_pi_ai::models::Models;
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_thinking, faux_tool_call, FauxAssistantMessageOptions,
    FauxModelDefinition, FauxResponseStep,
};
use eukhe_pi_ai::providers::faux_script::{
    create_faux_script_models, parse_faux_script, parse_faux_script_value, FauxScriptProvider,
};
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, Context, ErrorReason, JsonObject, Message, Modality,
    StopReason, UserContent, UserMessage,
};
use futures::StreamExt;
use serde_json::json;

fn user_text(text: &str) -> Message {
    Message::User(UserMessage {
        content: UserContent::Text(text.to_owned()),
        timestamp: 0,
    })
}

fn context(system_prompt: Option<&str>) -> Context {
    Context {
        system_prompt: system_prompt.map(str::to_owned),
        messages: vec![user_text("hi")],
        tools: None,
    }
}

fn scripted(script: &serde_json::Value) -> (Models, FauxScriptProvider) {
    create_faux_script_models(parse_faux_script_value(script).expect("script parses"))
}

fn register() -> (Models, FauxScriptProvider) {
    scripted(&json!({}))
}

fn text_msg(text: &str) -> FauxResponseStep {
    faux_assistant_message(text, FauxAssistantMessageOptions::default()).into()
}

async fn complete(models: &Models, faux: &FauxScriptProvider) -> AssistantMessage {
    models
        .complete_simple(
            &faux.get_model(),
            context(None),
            SimpleStreamOptions::default().into(),
        )
        .await
}

#[test]
fn parses_the_model_keys_with_defaults() {
    let defaults = parse_faux_script("{}").expect("script parses");
    assert_eq!(
        defaults.model,
        FauxModelDefinition {
            id: "faux-1".to_owned(),
            name: Some("Faux Model".to_owned()),
            reasoning: Some(false),
            input: Some(vec![Modality::Text, Modality::Image]),
            input_limits: None,
            cost: None,
            context_window: Some(128_000),
            max_tokens: Some(16_384),
        }
    );
    assert_eq!(defaults.tokens_per_second, None);
    assert!(defaults.responses.is_empty());
    assert!(!defaults.repeat_last_response);

    let custom = parse_faux_script_value(&json!({
        "modelId": "faux-custom",
        "modelName": "Custom",
        "reasoning": true,
        "contextWindow": 4096,
        "maxTokens": 512,
        "tokensPerSecond": 25.5,
    }))
    .expect("script parses");
    assert_eq!(
        custom.model,
        FauxModelDefinition {
            id: "faux-custom".to_owned(),
            name: Some("Custom".to_owned()),
            reasoning: Some(true),
            input: Some(vec![Modality::Text, Modality::Image]),
            input_limits: None,
            cost: None,
            context_window: Some(4096),
            max_tokens: Some(512),
        }
    );
    assert_eq!(custom.tokens_per_second, Some(25.5));
}

#[test]
fn drops_non_positive_tokens_per_second() {
    for rate in [json!(0), json!(-3), json!("fast")] {
        let parsed =
            parse_faux_script_value(&json!({ "tokensPerSecond": rate })).expect("script parses");
        assert_eq!(parsed.tokens_per_second, None);
    }
}

#[test]
fn rejects_malformed_scripts() {
    let cases = [
        (
            "not json",
            "invalid faux script JSON: expected ident at line 1 column 2",
        ),
        ("[]", "the faux script must be a JSON object"),
        (
            r#"{"responses": {}}"#,
            "the faux script responses must be an array",
        ),
        (
            r#"{"responses": [1]}"#,
            "a faux script response must be a string or object",
        ),
        (
            r#"{"responses": [null]}"#,
            "a faux script response must be a string or object",
        ),
        (
            r#"{"responses": [{"content": ["x"]}]}"#,
            "a faux script content block must be an object",
        ),
        (
            r#"{"responses": [{"content": [{}]}]}"#,
            "a faux script content block needs a type",
        ),
        (
            r#"{"responses": [{"content": [{"type": "image"}]}]}"#,
            "unknown faux script content type image",
        ),
        (
            r#"{"responses": [{"content": [{"type": "thinking"}]}]}"#,
            "a thinking block needs thinking text",
        ),
        (
            r#"{"responses": [{"content": [{"type": "text", "text": 1}]}]}"#,
            "a text block needs text",
        ),
        (
            r#"{"responses": [{"content": [{"type": "toolCall"}]}]}"#,
            "a toolCall block needs a name",
        ),
        (
            r#"{"responses": [{"content": [{"type": "toolCall", "name": "x", "arguments": "{}"}]}]}"#,
            "a toolCall block's arguments must be an object",
        ),
        (
            r#"{"responses": [{"text": "x", "stopReason": "paused"}]}"#,
            "unknown faux script stopReason paused",
        ),
    ];
    for (script, expected) in cases {
        let error = parse_faux_script(script).expect_err(script);
        assert_eq!(error.to_string(), expected, "{script}");
    }
}

#[tokio::test]
async fn streams_each_entry_form_through_models() {
    let (models, faux) = scripted(&json!({
        "responses": [
            "plain",
            { "text": "text entry" },
            { "text": 1 },
            { "content": 1 },
            {
                "content": [
                    { "type": "thinking", "thinking": "think first" },
                    { "type": "text", "text": "then answer" },
                ],
            },
            {
                "content": [
                    { "type": "text", "text": "calling" },
                    { "type": "toolCall", "name": "ipython", "arguments": { "code": "1 + 1" }, "id": "call-1" },
                    { "type": "toolCall", "name": "noop", "id": "call-2" },
                ],
            },
        ],
    }));

    let mut code = JsonObject::new();
    code.insert("code".to_owned(), json!("1 + 1"));
    let expected = [
        (vec![faux_text("plain")], StopReason::Stop),
        (vec![faux_text("text entry")], StopReason::Stop),
        (vec![faux_text("")], StopReason::Stop),
        (vec![faux_text("")], StopReason::Stop),
        (
            vec![faux_thinking("think first"), faux_text("then answer")],
            StopReason::Stop,
        ),
        (
            vec![
                faux_text("calling"),
                faux_tool_call("ipython", code, Some("call-1".to_owned())),
                faux_tool_call("noop", JsonObject::new(), Some("call-2".to_owned())),
            ],
            StopReason::ToolUse,
        ),
    ];
    for (content, stop_reason) in expected {
        let message = complete(&models, &faux).await;
        assert_eq!(
            (message.content, message.stop_reason),
            (content, stop_reason)
        );
        assert_eq!(
            (
                message.api.as_str(),
                message.provider.as_str(),
                message.model.as_str()
            ),
            ("faux", "faux", "faux-1")
        );
        assert!(message.usage.input > 0);
    }
    assert_eq!(faux.call_count(), 6);
}

#[tokio::test]
async fn streams_scripted_error_and_aborted_stop_reasons() {
    let (models, faux) = scripted(&json!({
        "responses": [
            { "text": "partial", "stopReason": "error", "errorMessage": "prompt is too long" },
            { "text": "cut", "stopReason": "aborted" },
            { "text": "truncated", "stopReason": "length" },
            {
                "content": [{ "type": "toolCall", "name": "x", "id": "call-1" }],
                "stopReason": "stop",
            },
        ],
    }));

    let stream = models.stream_simple(
        &faux.get_model(),
        context(None),
        SimpleStreamOptions::default().into(),
    );
    let events: Vec<AssistantMessageEvent> = stream.events().collect().await;
    let error = stream.result().await;
    assert_eq!(error.stop_reason, StopReason::Error);
    assert_eq!(error.error_message.as_deref(), Some("prompt is too long"));
    assert_eq!(error.content, vec![faux_text("partial")]);
    assert!(matches!(
        events.last(),
        Some(AssistantMessageEvent::Error {
            reason: ErrorReason::Error,
            ..
        })
    ));

    let aborted = complete(&models, &faux).await;
    assert_eq!(
        (aborted.stop_reason, aborted.content),
        (StopReason::Aborted, vec![faux_text("cut")])
    );
    let length = complete(&models, &faux).await;
    assert_eq!(length.stop_reason, StopReason::Length);
    let explicit_stop = complete(&models, &faux).await;
    assert_eq!(explicit_stop.stop_reason, StopReason::Stop);
}

#[tokio::test]
async fn echoes_the_system_prompt() {
    let (models, faux) = scripted(&json!({
        "responses": [{ "systemPrompt": true }, { "systemPrompt": true, "stopReason": "length" }],
    }));
    let echoed = models
        .complete_simple(
            &faux.get_model(),
            context(Some("Be concise.")),
            SimpleStreamOptions::default().into(),
        )
        .await;
    assert_eq!(
        (echoed.content, echoed.stop_reason),
        (vec![faux_text("Be concise.")], StopReason::Stop)
    );
    let without_prompt = complete(&models, &faux).await;
    assert_eq!(
        (without_prompt.content, without_prompt.stop_reason),
        (vec![faux_text("")], StopReason::Length)
    );
}

#[tokio::test]
async fn registers_under_the_faux_identity() {
    let (models, faux) = scripted(&json!({ "modelId": "faux-x" }));
    let model = models
        .get_model("faux", "faux-x")
        .expect("the scripted model is in the collection");
    assert_eq!(model, faux.get_model());
    assert_eq!(
        (model.api.as_str(), model.provider.as_str()),
        ("faux", "faux")
    );
    assert_eq!(faux.provider().id, "faux");
}

#[tokio::test]
async fn consumes_queued_responses_in_order_and_errors_when_exhausted() {
    let (models, faux) = register();
    faux.set_responses(vec![text_msg("first"), text_msg("second")]);

    let first = complete(&models, &faux).await;
    let second = complete(&models, &faux).await;
    let exhausted = complete(&models, &faux).await;

    assert_eq!(first.content, vec![faux_text("first")]);
    assert_eq!(second.content, vec![faux_text("second")]);
    assert_eq!(exhausted.stop_reason, StopReason::Error);
    assert_eq!(
        exhausted.error_message.as_deref(),
        Some("No more faux responses queued")
    );
    assert_eq!(faux.get_pending_response_count(), 0);
    assert_eq!(faux.call_count(), 3);
}

#[tokio::test]
async fn can_replace_and_append_queued_responses() {
    let (models, faux) = register();
    faux.set_responses(vec![text_msg("first")]);
    faux.set_responses(vec![text_msg("replaced")]);
    faux.append_responses(vec![text_msg("appended")]);
    assert_eq!(faux.get_pending_response_count(), 2);

    assert_eq!(
        complete(&models, &faux).await.content,
        vec![faux_text("replaced")]
    );
    assert_eq!(
        complete(&models, &faux).await.content,
        vec![faux_text("appended")]
    );
    assert_eq!(faux.get_pending_response_count(), 0);
}

#[tokio::test]
async fn repeat_last_response_replays_the_last_step_once_the_queue_runs_dry() {
    let (models, faux) = register();
    faux.set_repeat_last_response(true);
    faux.set_responses(vec![text_msg("first"), text_msg("last")]);

    let first = complete(&models, &faux).await;
    let last = complete(&models, &faux).await;
    let dry_one = complete(&models, &faux).await;
    let dry_two = complete(&models, &faux).await;

    assert_eq!(first.content, vec![faux_text("first")]);
    assert_eq!(last.content, vec![faux_text("last")]);
    assert_eq!(dry_one.content, vec![faux_text("last")]);
    assert_eq!(dry_one.stop_reason, StopReason::Stop);
    assert_eq!(dry_two.content, vec![faux_text("last")]);
    assert_eq!(faux.get_pending_response_count(), 0);
    assert_eq!(faux.call_count(), 4);
}

#[tokio::test]
async fn parses_the_repeat_last_response_script_key_into_the_registration() {
    let parsed = parse_faux_script_value(&json!({
        "responses": ["only"],
        "repeatLastResponse": true,
    }))
    .expect("script parses");
    assert!(parsed.repeat_last_response);
    let (models, faux) = create_faux_script_models(parsed);

    let queued = complete(&models, &faux).await;
    let repeated = complete(&models, &faux).await;
    assert_eq!(queued.content, vec![faux_text("only")]);
    assert_eq!(repeated.content, vec![faux_text("only")]);
    assert_eq!(faux.get_pending_response_count(), 0);
    assert_eq!(faux.call_count(), 2);

    // The knob stays off unless the script opts in: the finite queue and
    // its exhaustion error are the response-budget contract.
    let parsed = parse_faux_script_value(&json!({ "responses": ["only"] })).expect("script parses");
    assert!(!parsed.repeat_last_response);
}

#[tokio::test]
async fn repeat_last_response_switched_on_after_serving_replays_the_last_step() {
    let (models, faux) = register();
    faux.set_responses(vec![text_msg("first"), text_msg("last")]);

    let first = complete(&models, &faux).await;
    let last = complete(&models, &faux).await;
    // The queue is dry and the mode was off while it drained; switching
    // repeat-last on now still has the last served step recorded.
    faux.set_repeat_last_response(true);
    let replay = complete(&models, &faux).await;

    assert_eq!(first.content, vec![faux_text("first")]);
    assert_eq!(last.content, vec![faux_text("last")]);
    assert_eq!(replay.content, vec![faux_text("last")]);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn overlapping_streams_in_repeat_last_mode_never_hit_the_exhaustion_error() {
    let (models, faux) = register();
    faux.set_repeat_last_response(true);
    faux.set_responses(vec![text_msg("only")]);

    let calls: Vec<_> = (0..8)
        .map(|_| {
            let models = models.clone();
            let faux = faux.clone();
            tokio::spawn(async move { complete(&models, &faux).await })
        })
        .collect();
    for call in calls {
        let response = call.await.expect("the call completes");
        assert_eq!(response.content, vec![faux_text("only")]);
        assert_ne!(response.stop_reason, StopReason::Error);
    }
    assert_eq!(faux.get_pending_response_count(), 0);
    assert_eq!(faux.call_count(), 8);
}

#[tokio::test(start_paused = true)]
async fn delay_ms_holds_the_request_before_the_first_event() {
    let (models, faux) = scripted(&json!({
        "responses": [{ "text": "late", "delayMs": 250 }, "prompt"],
    }));
    let started = tokio::time::Instant::now();
    let late = complete(&models, &faux).await;
    assert_eq!(late.content, vec![faux_text("late")]);
    assert!(started.elapsed() >= Duration::from_millis(250));

    let started = tokio::time::Instant::now();
    let prompt = complete(&models, &faux).await;
    assert_eq!(prompt.content, vec![faux_text("prompt")]);
    assert!(started.elapsed() < Duration::from_millis(250));
}

#[tokio::test(start_paused = true)]
async fn aborting_during_the_delay_ends_the_stream_aborted() {
    let (models, faux) = scripted(&json!({
        "responses": [{ "text": "never", "delayMs": 60_000 }],
    }));
    let controller = AbortController::new();
    let mut options = SimpleStreamOptions::default();
    options.stream.request.signal = Some(controller.signal());
    let stream = models.stream_simple(&faux.get_model(), context(None), options.into());
    tokio::time::sleep(Duration::from_millis(10)).await;
    controller.abort(None);

    let started = tokio::time::Instant::now();
    let events: Vec<AssistantMessageEvent> = stream.events().collect().await;
    let aborted = stream.result().await;
    assert!(started.elapsed() < Duration::from_secs(60));
    assert_eq!(aborted.stop_reason, StopReason::Aborted);
    assert_eq!(
        aborted.error_message.as_deref(),
        Some("Request was aborted")
    );
    assert!(aborted.content.is_empty());
    assert_eq!(
        events
            .iter()
            .map(AssistantMessageEvent::type_name)
            .collect::<Vec<_>>(),
        ["error"]
    );
}

#[tokio::test(start_paused = true)]
async fn tokens_per_second_paces_streaming() {
    // 40 characters = 10 tokens; at 10 tokens per second the stream takes
    // one second of (paused) time.
    let (models, faux) = scripted(&json!({
        "tokensPerSecond": 10,
        "responses": ["a".repeat(40)],
    }));
    let started = tokio::time::Instant::now();
    let message = complete(&models, &faux).await;
    assert_eq!(message.content, vec![faux_text("a".repeat(40))]);
    assert_eq!(started.elapsed(), Duration::from_secs(1));
}
