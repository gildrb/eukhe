//! Port of `test/faux-provider.test.ts` (through the compat registry, as in
//! TS).

mod common;

use std::sync::Arc;

use common::{now, user};
use eukhe_chord::context::AbortController;
use eukhe_pi_ai::compat::{complete, register_faux_provider, stream, FauxProviderRegistration};
use eukhe_pi_ai::providers::faux::{
    faux_assistant_message, faux_text, faux_thinking, faux_tool_call, FauxAssistantMessageOptions,
    FauxModelDefinition, FauxResponseStep, FauxTokenSize, RegisterFauxProviderOptions,
};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, CacheRetention, Context,
    ErrorReason, ImageContent, JsonObject, Message, StopReason, TextContent, ThinkingContent, Tool,
    ToolCall, ToolResultMessage, UserContent, UserContentBlock, UserMessage,
};
use futures::StreamExt;

/// Unregisters on drop (the TS `afterEach`).
struct Registered(FauxProviderRegistration);

impl Drop for Registered {
    fn drop(&mut self) {
        self.0.unregister();
    }
}

impl std::ops::Deref for Registered {
    type Target = FauxProviderRegistration;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

fn register(options: RegisterFauxProviderOptions) -> Registered {
    Registered(register_faux_provider(options))
}

fn message(text: &str) -> FauxResponseStep {
    faux_assistant_message(text, FauxAssistantMessageOptions::default()).into()
}

fn hi() -> Context {
    Context {
        system_prompt: None,
        messages: vec![user("hi")],
        tools: None,
    }
}

fn session(session_id: &str, retention: CacheRetention) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.session_id = Some(session_id.to_owned());
    options.stream.cache_retention = Some(retention);
    options
}

async fn collect(stream: AssistantMessageEventStream) -> Vec<AssistantMessageEvent> {
    stream.events().collect().await
}

fn types(events: &[AssistantMessageEvent]) -> Vec<&'static str> {
    events
        .iter()
        .map(AssistantMessageEvent::type_name)
        .collect()
}

fn text_block(text: &str) -> AssistantContentBlock {
    AssistantContentBlock::Text(TextContent::new(text))
}

fn args(value: serde_json::Value) -> JsonObject {
    serde_json::from_value(value).expect("object")
}

async fn done(
    registration: &Registered,
    context: Context,
    options: ProviderStreamOptions,
) -> AssistantMessage {
    complete(&registration.get_model(), context, options)
        .await
        .expect("registered")
}

#[tokio::test]
async fn registers_a_custom_provider_and_estimates_usage() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![message("hello world")]);

    let context = Context {
        system_prompt: Some("Be concise.".into()),
        messages: vec![user("hi there")],
        tools: None,
    };

    let response = done(&registration, context, ProviderStreamOptions::default()).await;
    assert_eq!(response.content, vec![text_block("hello world")]);
    assert!(response.usage.input > 0);
    assert!(response.usage.output > 0);
    assert_eq!(
        response.usage.total_tokens,
        response.usage.input + response.usage.output
    );
    assert_eq!(registration.state().call_count, 1);
}

#[tokio::test]
async fn supports_helper_blocks_for_text_thinking_and_tool_calls() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![faux_assistant_message(
        vec![
            faux_thinking("think"),
            faux_tool_call("echo", args(serde_json::json!({ "text": "hi" })), None),
            faux_text("done"),
        ],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()]);

    let response = done(&registration, hi(), ProviderStreamOptions::default()).await;

    assert_eq!(response.content.len(), 3);
    assert_eq!(
        response.content[0],
        AssistantContentBlock::Thinking(ThinkingContent {
            thinking: "think".into(),
            thinking_signature: None,
            redacted: None,
        })
    );
    let AssistantContentBlock::ToolCall(call) = &response.content[1] else {
        panic!("tool call");
    };
    assert!(!call.id.is_empty());
    assert_eq!(call.name, "echo");
    assert_eq!(call.arguments, args(serde_json::json!({ "text": "hi" })));
    assert_eq!(response.content[2], text_block("done"));
    assert_eq!(response.stop_reason, StopReason::ToolUse);
}

#[tokio::test]
async fn supports_multiple_models_with_per_model_reasoning_and_model_aware_factories() {
    let registration = register(RegisterFauxProviderOptions {
        models: Some(vec![
            FauxModelDefinition {
                name: Some("Faux Fast".into()),
                reasoning: Some(false),
                ..FauxModelDefinition::new("faux-fast")
            },
            FauxModelDefinition {
                name: Some("Faux Thinker".into()),
                reasoning: Some(true),
                ..FauxModelDefinition::new("faux-thinker")
            },
        ]),
        ..RegisterFauxProviderOptions::default()
    });
    let factory = || {
        FauxResponseStep::factory(|_context, _options, _state, model| {
            Ok(faux_assistant_message(
                format!("{}:{}", model.id, model.reasoning),
                FauxAssistantMessageOptions::default(),
            ))
        })
    };
    registration.set_responses(vec![factory(), factory()]);

    let ids: Vec<String> = registration
        .models()
        .iter()
        .map(|model| model.id.clone())
        .collect();
    assert_eq!(ids, ["faux-fast", "faux-thinker"]);
    assert_eq!(registration.get_model(), registration.models()[0]);
    assert_eq!(
        registration
            .get_model_by_id("faux-fast")
            .map(|model| model.reasoning),
        Some(false)
    );
    assert_eq!(
        registration
            .get_model_by_id("faux-thinker")
            .map(|model| model.reasoning),
        Some(true)
    );

    let fast_model = registration.get_model_by_id("faux-fast").expect("fast");
    let fast = complete(&fast_model, hi(), ProviderStreamOptions::default())
        .await
        .expect("fast");
    let thinker_model = registration
        .get_model_by_id("faux-thinker")
        .expect("thinker");
    let thinker = complete(&thinker_model, hi(), ProviderStreamOptions::default())
        .await
        .expect("thinker");

    assert_eq!(fast.content, vec![text_block("faux-fast:false")]);
    assert_eq!(thinker.content, vec![text_block("faux-thinker:true")]);
}

#[tokio::test]
async fn rewrites_api_provider_and_model_on_returned_messages() {
    let registration = register(RegisterFauxProviderOptions {
        api: Some("faux:test".into()),
        provider: Some("faux-provider".into()),
        models: Some(vec![FauxModelDefinition::new("faux-model")]),
        ..RegisterFauxProviderOptions::default()
    });
    registration.set_responses(vec![message("hello")]);

    let response = done(&registration, hi(), ProviderStreamOptions::default()).await;

    assert_eq!(response.api, "faux:test");
    assert_eq!(response.provider, "faux-provider");
    assert_eq!(response.model, "faux-model");
}

#[tokio::test]
async fn consumes_queued_responses_in_order_and_errors_when_exhausted() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![message("first"), message("second")]);

    let first = done(&registration, hi(), ProviderStreamOptions::default()).await;
    let second = done(&registration, hi(), ProviderStreamOptions::default()).await;
    let exhausted = done(&registration, hi(), ProviderStreamOptions::default()).await;

    assert_eq!(first.content, vec![text_block("first")]);
    assert_eq!(second.content, vec![text_block("second")]);
    assert_eq!(exhausted.stop_reason, StopReason::Error);
    assert_eq!(
        exhausted.error_message.as_deref(),
        Some("No more faux responses queued")
    );
    assert_eq!(registration.get_pending_response_count(), 0);
    assert_eq!(registration.state().call_count, 3);
}

#[tokio::test]
async fn can_replace_and_append_queued_responses() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![message("first")]);

    assert_eq!(
        done(&registration, hi(), ProviderStreamOptions::default())
            .await
            .content,
        vec![text_block("first")]
    );
    assert_eq!(registration.get_pending_response_count(), 0);

    registration.set_responses(vec![message("second")]);
    assert_eq!(registration.get_pending_response_count(), 1);
    assert_eq!(
        done(&registration, hi(), ProviderStreamOptions::default())
            .await
            .content,
        vec![text_block("second")]
    );

    registration.append_responses(vec![message("third"), message("fourth")]);
    assert_eq!(registration.get_pending_response_count(), 2);
    assert_eq!(
        done(&registration, hi(), ProviderStreamOptions::default())
            .await
            .content,
        vec![text_block("third")]
    );
    assert_eq!(
        done(&registration, hi(), ProviderStreamOptions::default())
            .await
            .content,
        vec![text_block("fourth")]
    );
    assert_eq!(registration.get_pending_response_count(), 0);
}

#[tokio::test]
async fn supports_async_response_factories() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![FauxResponseStep::Factory(Arc::new(
        |context, _options, state, _model| {
            let text = format!("{}:{}", context.messages().len(), state.call_count);
            Box::pin(async move {
                Ok(faux_assistant_message(
                    text,
                    FauxAssistantMessageOptions::default(),
                ))
            })
        },
    ))]);

    let response = done(&registration, hi(), ProviderStreamOptions::default()).await;

    assert_eq!(response.content, vec![text_block("1:1")]);
}

#[tokio::test]
async fn emits_an_error_when_a_response_factory_throws() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![FauxResponseStep::factory(|_, _, _, _| {
        Err(common::error("boom"))
    })]);

    let events = collect(
        stream(
            &registration.get_model(),
            hi(),
            ProviderStreamOptions::default(),
        )
        .expect("stream"),
    )
    .await;

    assert_eq!(events.len(), 1);
    let AssistantMessageEvent::Error { error, .. } = &events[0] else {
        panic!("error event");
    };
    assert_eq!(error.stop_reason, StopReason::Error);
    assert_eq!(error.error_message.as_deref(), Some("boom"));
}

#[tokio::test]
async fn rejects_a_queued_response_without_a_terminal_stop_reason() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![faux_assistant_message(
        "partial",
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::Pending),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()]);

    let events = collect(
        stream(
            &registration.get_model(),
            hi(),
            ProviderStreamOptions::default(),
        )
        .expect("stream"),
    )
    .await;

    assert!(!events.iter().any(|event| event.type_name() == "done"));
    let Some(AssistantMessageEvent::Error { error, .. }) = events.last() else {
        panic!("terminal error");
    };
    assert_eq!(error.stop_reason, StopReason::Error);
    assert_eq!(
        error.error_message.as_deref(),
        Some("Faux response ended without a stop reason")
    );
}

#[tokio::test]
async fn estimates_prompt_and_output_tokens_from_serialized_context() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![message("done")]);

    // TypeBox `Type.Object({ text: Type.String() })` as JSON.
    let parameters = serde_json::json!({
        "type": "object",
        "properties": { "text": { "type": "string" } },
        "required": ["text"],
    });
    let tool = Tool {
        name: "echo".into(),
        description: "Echo back text".into(),
        parameters: parameters.into(),
        constrained_sampling: None,
    };
    let context = Context {
        system_prompt: Some("sys".into()),
        messages: vec![
            Message::User(UserMessage {
                content: UserContent::Blocks(vec![
                    UserContentBlock::Text(TextContent::new("hello")),
                    UserContentBlock::Image(ImageContent {
                        data: "abcd".into(),
                        mime_type: "image/png".into(),
                    }),
                ]),
                timestamp: 1,
            }),
            Message::Assistant(faux_assistant_message(
                "prior",
                FauxAssistantMessageOptions::default(),
            )),
            Message::ToolResult(ToolResultMessage {
                tool_call_id: "tool-1".into(),
                tool_name: "echo".into(),
                content: vec![UserContentBlock::Text(TextContent::new("tool out"))],
                details: None,
                usage: None,
                nested_calls: None,
                is_error: false,
                timestamp: 2,
            }),
        ],
        tools: Some(vec![tool.clone()]),
    };

    let response = done(&registration, context, ProviderStreamOptions::default()).await;
    let prompt_text = [
        "system:sys".to_owned(),
        "user:hello\n[image:image/png:4]".to_owned(),
        "assistant:prior".to_owned(),
        "toolResult:echo\ntool out".to_owned(),
        format!(
            "tools:{}",
            serde_json::to_string(&vec![tool]).expect("json")
        ),
    ]
    .join("\n\n");
    let expected_prompt_tokens =
        u64::try_from(prompt_text.encode_utf16().count().div_ceil(4)).expect("small");
    let expected_output_tokens = u64::try_from("done".len().div_ceil(4)).expect("small");

    assert_eq!(response.usage.input, expected_prompt_tokens);
    assert_eq!(response.usage.output, expected_output_tokens);
    assert_eq!(response.usage.cache_read, 0);
    assert_eq!(response.usage.cache_write, 0);
    assert_eq!(
        response.usage.total_tokens,
        expected_prompt_tokens + expected_output_tokens
    );
}

#[tokio::test]
async fn does_not_share_cache_across_sessions_or_requests_without_session_id() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![message("first"), message("second"), message("third")]);

    let mut context = Context {
        system_prompt: None,
        messages: vec![user("hello")],
        tools: None,
    };

    let first = done(
        &registration,
        context.clone(),
        session("session-1", CacheRetention::Short),
    )
    .await;
    assert!(first.usage.cache_write > 0);
    context.messages.push(Message::Assistant(first));
    context.messages.push(Message::User(UserMessage {
        content: UserContent::Text("follow up".into()),
        timestamp: now() + 1,
    }));

    let second = done(
        &registration,
        context.clone(),
        session("session-2", CacheRetention::Short),
    )
    .await;
    assert_eq!(second.usage.cache_read, 0);
    assert!(second.usage.cache_write > 0);

    let third = done(&registration, context, ProviderStreamOptions::default()).await;
    assert_eq!(third.usage.cache_read, 0);
    assert_eq!(third.usage.cache_write, 0);
}

#[tokio::test]
async fn simulates_prompt_caching_per_session_id() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![message("first"), message("second")]);

    let mut context = Context {
        system_prompt: Some("Be concise.".into()),
        messages: vec![user("hello")],
        tools: None,
    };

    let first = done(
        &registration,
        context.clone(),
        session("session-1", CacheRetention::Short),
    )
    .await;
    assert_eq!(first.usage.cache_read, 0);
    assert!(first.usage.cache_write > 0);

    context.messages.push(Message::Assistant(first));
    context.messages.push(Message::User(UserMessage {
        content: UserContent::Text("follow up".into()),
        timestamp: now() + 1,
    }));

    let second = done(
        &registration,
        context,
        session("session-1", CacheRetention::Short),
    )
    .await;
    assert!(second.usage.cache_read > 0);
    assert!(second.usage.input + second.usage.cache_read > second.usage.input);
}

#[tokio::test]
async fn does_not_simulate_caching_when_cache_retention_is_none() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![message("first"), message("second")]);

    let mut context = Context {
        system_prompt: None,
        messages: vec![user("hello")],
        tools: None,
    };

    done(
        &registration,
        context.clone(),
        session("session-1", CacheRetention::None),
    )
    .await;
    context
        .messages
        .push(Message::Assistant(faux_assistant_message(
            "first",
            FauxAssistantMessageOptions::default(),
        )));
    context.messages.push(Message::User(UserMessage {
        content: UserContent::Text("follow up".into()),
        timestamp: now() + 1,
    }));
    let second = done(
        &registration,
        context,
        session("session-1", CacheRetention::None),
    )
    .await;
    assert_eq!(second.usage.cache_read, 0);
    assert_eq!(second.usage.cache_write, 0);
}

#[tokio::test]
async fn streams_thinking_text_and_partial_tool_call_deltas() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![faux_assistant_message(
        vec![
            faux_thinking("thinking text"),
            faux_text("answer text"),
            faux_tool_call(
                "echo",
                args(serde_json::json!({ "text": "hi", "count": 12 })),
                Some("tool-1".into()),
            ),
        ],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()]);

    let events = collect(
        stream(
            &registration.get_model(),
            hi(),
            ProviderStreamOptions::default(),
        )
        .expect("stream"),
    )
    .await;
    let names = types(&events);
    let tool_call_deltas: Vec<String> = events
        .iter()
        .filter_map(|event| match event {
            AssistantMessageEvent::ToolCallDelta { delta, .. } => Some(delta.clone()),
            _ => None,
        })
        .collect();

    for expected in [
        "thinking_start",
        "thinking_delta",
        "text_start",
        "text_delta",
        "toolcall_start",
        "toolcall_delta",
        "toolcall_end",
    ] {
        assert!(names.contains(&expected), "{expected}");
    }
    assert!(tool_call_deltas.len() > 1);
    let parsed: serde_json::Value = serde_json::from_str(&tool_call_deltas.concat()).expect("json");
    assert_eq!(parsed, serde_json::json!({ "text": "hi", "count": 12 }));
}

#[tokio::test]
async fn streams_an_exact_event_order_for_fixed_size_chunks() {
    let registration = register(RegisterFauxProviderOptions {
        token_size: Some(FauxTokenSize {
            min: Some(1),
            max: Some(1),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    registration.set_responses(vec![faux_assistant_message(
        vec![
            faux_thinking("go"),
            faux_text("ok"),
            faux_tool_call("echo", JsonObject::new(), Some("tool-1".into())),
        ],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()]);

    let events = collect(
        stream(
            &registration.get_model(),
            hi(),
            ProviderStreamOptions::default(),
        )
        .expect("stream"),
    )
    .await;

    let AssistantMessageEvent::Start { partial } = &events[0] else {
        panic!("start");
    };
    assert_eq!(partial.stop_reason, StopReason::Pending);
    assert_eq!(
        types(&events),
        [
            "start",
            "thinking_start",
            "thinking_delta",
            "thinking_end",
            "text_start",
            "text_delta",
            "text_end",
            "toolcall_start",
            "toolcall_delta",
            "toolcall_end",
            "done",
        ]
    );
}

#[tokio::test]
async fn streams_multiple_tool_calls_in_one_message() {
    let registration = register(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![faux_assistant_message(
        vec![
            faux_tool_call(
                "echo",
                args(serde_json::json!({ "text": "one" })),
                Some("tool-1".into()),
            ),
            faux_tool_call(
                "echo",
                args(serde_json::json!({ "text": "two" })),
                Some("tool-2".into()),
            ),
        ],
        FauxAssistantMessageOptions {
            stop_reason: Some(StopReason::ToolUse),
            ..FauxAssistantMessageOptions::default()
        },
    )
    .into()]);

    let events = collect(
        stream(
            &registration.get_model(),
            hi(),
            ProviderStreamOptions::default(),
        )
        .expect("stream"),
    )
    .await;

    assert_eq!(
        types(&events)
            .iter()
            .filter(|name| **name == "toolcall_start")
            .count(),
        2
    );
    assert_eq!(
        types(&events)
            .iter()
            .filter(|name| **name == "toolcall_end")
            .count(),
        2
    );
}

async fn terminal_message(stop_reason: StopReason, error_message: &str, reason: ErrorReason) {
    let registration = register(RegisterFauxProviderOptions {
        token_size: Some(FauxTokenSize {
            min: Some(2),
            max: Some(2),
        }),
        ..RegisterFauxProviderOptions::default()
    });
    registration.set_responses(vec![AssistantMessage {
        stop_reason,
        error_message: Some(error_message.to_owned()),
        ..faux_assistant_message("partial", FauxAssistantMessageOptions::default())
    }
    .into()]);

    let events = collect(
        stream(
            &registration.get_model(),
            hi(),
            ProviderStreamOptions::default(),
        )
        .expect("stream"),
    )
    .await;

    assert_eq!(
        types(&events),
        ["start", "text_start", "text_delta", "text_end", "error"]
    );
    let Some(AssistantMessageEvent::Error {
        reason: terminal_reason,
        error,
    }) = events.last()
    else {
        panic!("terminal error");
    };
    assert_eq!(*terminal_reason, reason);
    assert_eq!(error.stop_reason, stop_reason);
    assert_eq!(error.error_message.as_deref(), Some(error_message));
}

#[tokio::test]
async fn streams_an_explicit_assistant_error_message_as_a_terminal_error() {
    terminal_message(StopReason::Error, "upstream failed", ErrorReason::Error).await;
}

#[tokio::test]
async fn streams_an_explicit_assistant_aborted_message_as_a_terminal_error() {
    terminal_message(
        StopReason::Aborted,
        "Request was aborted",
        ErrorReason::Aborted,
    )
    .await;
}

fn paced(tokens_per_second: f64) -> RegisterFauxProviderOptions {
    RegisterFauxProviderOptions {
        tokens_per_second: Some(tokens_per_second),
        token_size: Some(FauxTokenSize {
            min: Some(3),
            max: Some(3),
        }),
        ..RegisterFauxProviderOptions::default()
    }
}

fn with_signal(controller: &AbortController) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.signal = Some(controller.signal());
    options
}

#[tokio::test(start_paused = true)]
async fn supports_aborting_before_the_first_chunk() {
    let registration = register(paced(50.0));
    registration.set_responses(vec![message("abcdefghijklmnopqrstuvwxyz")]);

    let controller = AbortController::new();
    controller.abort(None);
    let events =
        collect(stream(&registration.get_model(), hi(), with_signal(&controller)).expect("stream"))
            .await;

    assert_eq!(events.len(), 1);
    let AssistantMessageEvent::Error { reason, error } = &events[0] else {
        panic!("error event");
    };
    assert_eq!(*reason, ErrorReason::Aborted);
    assert_eq!(error.stop_reason, StopReason::Aborted);
}

/// Streams with a paced faux provider, aborting at the first `delta_type`.
async fn abort_at_first_delta(
    response: AssistantMessage,
    delta_type: &str,
) -> (Vec<&'static str>, usize) {
    let registration = register(paced(100.0));
    registration.set_responses(vec![response.into()]);
    let controller = AbortController::new();
    let stream = stream(&registration.get_model(), hi(), with_signal(&controller)).expect("stream");
    let mut events = stream.events();
    let mut names = Vec::new();
    let mut delta_count = 0;
    while let Some(event) = events.next().await {
        names.push(event.type_name());
        if event.type_name() == delta_type {
            delta_count += 1;
            controller.abort(None);
        }
    }
    (names, delta_count)
}

#[tokio::test(start_paused = true)]
async fn supports_aborting_mid_text_stream_when_paced() {
    let (events, count) = abort_at_first_delta(
        faux_assistant_message(
            "abcdefghijklmnopqrstuvwxyz",
            FauxAssistantMessageOptions::default(),
        ),
        "text_delta",
    )
    .await;

    assert_eq!(count, 1);
    assert!(events.contains(&"text_start"));
    assert!(events.contains(&"text_delta"));
    assert!(events.contains(&"error"));
    assert!(!events.contains(&"text_end"));
}

#[tokio::test(start_paused = true)]
async fn supports_aborting_mid_thinking_stream_when_paced() {
    let (events, count) = abort_at_first_delta(
        AssistantMessage {
            content: vec![faux_thinking("abcdefghijklmnopqrstuvwxyz")],
            ..faux_assistant_message("ignored", FauxAssistantMessageOptions::default())
        },
        "thinking_delta",
    )
    .await;

    assert_eq!(count, 1);
    assert!(events.contains(&"thinking_start"));
    assert!(events.contains(&"thinking_delta"));
    assert!(events.contains(&"error"));
    assert!(!events.contains(&"thinking_end"));
}

#[tokio::test(start_paused = true)]
async fn supports_aborting_mid_toolcall_stream_when_paced() {
    let (events, count) = abort_at_first_delta(
        AssistantMessage {
            content: vec![AssistantContentBlock::ToolCall(ToolCall {
                id: "tool-1".into(),
                name: "echo".into(),
                arguments: args(serde_json::json!({ "text": "abcdefghijklmnopqrstuvwxyz", "count": 123_456_789 })),
                thought_signature: None,
                namespace: None,
            })],
            stop_reason: StopReason::ToolUse,
            ..faux_assistant_message("done", FauxAssistantMessageOptions::default())
        },
        "toolcall_delta",
    )
    .await;

    assert_eq!(count, 1);
    assert!(events.contains(&"toolcall_start"));
    assert!(events.contains(&"toolcall_delta"));
    assert!(events.contains(&"error"));
    assert!(!events.contains(&"toolcall_end"));
}

#[tokio::test]
async fn unregisters_the_provider() {
    let registration = register_faux_provider(RegisterFauxProviderOptions::default());
    registration.set_responses(vec![message("hello")]);
    registration.unregister();

    let error = complete(
        &registration.get_model(),
        hi(),
        ProviderStreamOptions::default(),
    )
    .await
    .expect_err("unregistered");
    assert_eq!(
        error.to_string(),
        format!("No API provider registered for api: {}", registration.api())
    );
}
