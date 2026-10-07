//! Port of `test/stream.test.ts`: the "Generate E2E Tests" provider matrix.
//! Every case hits a real endpoint (TS `describe.skipIf(!process.env.X)` /
//! `it.skipIf(!token)`), so each is `#[ignore]`d with the variables it needs
//! and fails with a clear message when they are missing. OAuth tokens (TS
//! `resolveApiKey`) come from `PI_TEST_<PROVIDER>_TOKEN`. TS `{ retry: N }`
//! runs the case up to N times.

use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use base64::Engine;
use eukhe_pi_ai::compat::{complete, get_model, stream};
use eukhe_pi_ai::typebox::{Options, Type};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::typebox_helpers::string_enum;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, Context, JsonValue, Message,
    Modality, Model, ProviderHeaders, StopReason, Tool, Transport,
};
use futures::StreamExt;
use serde_json::json;

// ---------------------------------------------------------------------------
// Environment and setup
// ---------------------------------------------------------------------------

fn env(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

/// Fails the case unless every variable in `names` is set.
fn require_env(names: &[&str]) {
    for name in names {
        assert!(env(name).is_some(), "{name} must be set to run this test");
    }
}

/// TS `hasAzureOpenAICredentials()`.
fn require_azure_credentials() {
    require_env(&["AZURE_OPENAI_API_KEY"]);
    assert!(
        env("AZURE_OPENAI_BASE_URL").is_some() || env("AZURE_OPENAI_RESOURCE_NAME").is_some(),
        "AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME must be set to run this test"
    );
}

/// TS `resolveAzureDeploymentName()`: `AZURE_OPENAI_DEPLOYMENT_NAME_MAP` is a
/// comma-separated `modelId=deploymentName` list.
fn resolve_azure_deployment_name(model_id: &str) -> Option<String> {
    let map = env("AZURE_OPENAI_DEPLOYMENT_NAME_MAP")?;
    let mut found = None;
    for entry in map.split(',') {
        let trimmed = entry.trim();
        if trimmed.is_empty() {
            continue;
        }
        let mut parts = trimmed.split('=');
        let (Some(id), Some(deployment)) = (parts.next(), parts.next()) else {
            continue;
        };
        if id.is_empty() || deployment.is_empty() {
            continue;
        }
        if id.trim() == model_id {
            found = Some(deployment.trim().to_owned());
        }
    }
    found
}

/// TS `hasBedrockCredentials()`.
fn require_bedrock_credentials() {
    assert!(
        env("AWS_PROFILE").is_some()
            || (env("AWS_ACCESS_KEY_ID").is_some() && env("AWS_SECRET_ACCESS_KEY").is_some())
            || env("AWS_BEARER_TOKEN_BEDROCK").is_some(),
        "AWS_PROFILE, AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK must be set to run this test"
    );
}

/// TS `resolveApiKey(provider)`: the resolved OAuth token.
fn oauth_token(variable: &str) -> String {
    env(variable).unwrap_or_else(|| panic!("{variable} must be set to run this test"))
}

/// Vertex `{ project, location }` (`GOOGLE_CLOUD_PROJECT || GCLOUD_PROJECT`).
fn vertex_options() -> JsonValue {
    let project = env("GOOGLE_CLOUD_PROJECT")
        .or_else(|| env("GCLOUD_PROJECT"))
        .expect("GOOGLE_CLOUD_PROJECT or GCLOUD_PROJECT must be set to run this test");
    let location =
        env("GOOGLE_CLOUD_LOCATION").expect("GOOGLE_CLOUD_LOCATION must be set to run this test");
    json!({ "project": project, "location": location })
}

fn model(provider: &str, id: &str) -> Model {
    get_model(provider, id).unwrap_or_else(|| panic!("model {provider}/{id}"))
}

/// Options with API-specific keys (TS `StreamOptions & Record<string, unknown>`).
fn options(extra: &JsonValue) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    if let JsonValue::Object(entries) = extra {
        for (key, value) in entries {
            options.extra.insert(key.clone(), value.clone());
        }
    }
    options
}

fn with_api_key(mut options: ProviderStreamOptions, api_key: String) -> ProviderStreamOptions {
    options.stream.request.api_key = Some(api_key);
    options
}

fn with_bearer(mut options: ProviderStreamOptions, variable: &str) -> ProviderStreamOptions {
    let token = oauth_token(variable);
    let mut headers = ProviderHeaders::new();
    headers.insert("Authorization".to_owned(), Some(format!("Bearer {token}")));
    options.stream.request.headers = Some(headers);
    options
}

fn websocket(api_key: String, extra: &JsonValue) -> ProviderStreamOptions {
    let mut options = with_api_key(options(extra), api_key);
    options.stream.transport = Some(Transport::Websocket);
    options
}

/// TS `{ retry: N }`: runs `attempt` until it passes, at most `attempts` times,
/// and re-raises the last failure.
async fn with_retry<F, Fut>(attempts: u32, attempt: F)
where
    F: Fn() -> Fut,
    Fut: Future<Output = ()> + Send + 'static,
{
    let mut last_failure = None;
    for _ in 0..attempts {
        match tokio::spawn(attempt()).await {
            Ok(()) => return,
            Err(error) => last_failure = Some(error),
        }
    }
    let error = last_failure.expect("at least one attempt");
    match error.try_into_panic() {
        Ok(payload) => std::panic::resume_unwind(payload),
        Err(error) => panic!("attempt did not complete: {error}"),
    }
}

// ---------------------------------------------------------------------------
// Shared fixtures
// ---------------------------------------------------------------------------

fn now_ms() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock after epoch")
            .as_millis(),
    )
    .expect("timestamp fits u64")
}

fn user(content: &JsonValue) -> Message {
    serde_json::from_value(json!({ "role": "user", "content": content, "timestamp": now_ms() }))
        .expect("user message")
}

fn context(system_prompt: &str, messages: Vec<Message>, tools: Option<Vec<Tool>>) -> Context {
    Context {
        system_prompt: Some(system_prompt.to_owned()),
        messages,
        tools,
    }
}

/// Calculator tool definition (same as examples). `StringEnum` because Google's
/// API doesn't support the `anyOf`/`const` patterns `Type.Enum` generates.
fn calculator_tool() -> Tool {
    let schema = Type::object([
        (
            "a",
            Type::number_with(Options::new().set("description", "First number")),
        ),
        (
            "b",
            Type::number_with(Options::new().set("description", "Second number")),
        ),
        (
            "operation",
            string_enum(
                &["add", "subtract", "multiply", "divide"],
                Some("The operation to perform. One of 'add', 'subtract', 'multiply', 'divide'."),
                None,
            ),
        ),
    ]);
    Tool {
        name: "math_operation".to_owned(),
        description: "Perform basic arithmetic operations".to_owned(),
        parameters: schema.into(),
        constrained_sampling: None,
    }
}

fn text_of(response: &AssistantMessage) -> String {
    response
        .content
        .iter()
        .map(|block| match block {
            AssistantContentBlock::Text(text) => text.text.as_str(),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => "",
        })
        .collect()
}

fn complete_ok(response: &AssistantMessage) {
    assert!(!response.content.is_empty());
    assert!(response.usage.input + response.usage.cache_read > 0);
    assert!(response.usage.output > 0);
    assert!(
        response
            .error_message
            .as_deref()
            .unwrap_or_default()
            .is_empty(),
        "{:?}",
        response.error_message
    );
}

fn number_arg(arguments: &serde_json::Map<String, JsonValue>, name: &str) -> Option<f64> {
    arguments.get(name).and_then(JsonValue::as_f64)
}

// ---------------------------------------------------------------------------
// Scenarios (TS helpers)
// ---------------------------------------------------------------------------

async fn basic_text_generation(model: Model, options: ProviderStreamOptions) {
    let mut context = context(
        "You are a helpful assistant. Be concise.",
        vec![user(&json!("Reply with exactly: 'Hello test successful'"))],
        None,
    );
    let response = complete(&model, context.clone(), options.clone())
        .await
        .expect("complete");
    complete_ok(&response);
    assert!(text_of(&response).contains("Hello test successful"));

    context.messages.push(Message::Assistant(response));
    context
        .messages
        .push(user(&json!("Now say 'Goodbye test successful'")));

    let second_response = complete(&model, context, options).await.expect("complete");
    complete_ok(&second_response);
    assert!(text_of(&second_response).contains("Goodbye test successful"));
}

async fn handle_tool_call(model: Model, options: ProviderStreamOptions) {
    let context = context(
        "You are a helpful assistant that uses tools when asked.",
        vec![user(&json!(
            "Calculate 15 + 27 using the math_operation tool."
        ))],
        Some(vec![calculator_tool()]),
    );
    let events = stream(&model, context, options).expect("stream");
    let mut has_tool_start = false;
    let mut has_tool_delta = false;
    let mut has_tool_end = false;
    let mut accumulated_tool_args = String::new();
    let mut index = 0;
    let mut iter = events.events();
    while let Some(event) = iter.next().await {
        match event {
            AssistantMessageEvent::ToolCallStart {
                content_index,
                partial,
            } => {
                has_tool_start = true;
                index = content_index;
                let AssistantContentBlock::ToolCall(tool_call) = &partial.content[content_index]
                else {
                    panic!("expected toolCall at {content_index}");
                };
                assert_eq!(tool_call.name, "math_operation");
                assert!(!tool_call.id.is_empty());
            }
            AssistantMessageEvent::ToolCallDelta {
                content_index,
                delta,
                partial,
            } => {
                has_tool_delta = true;
                assert_eq!(content_index, index);
                let AssistantContentBlock::ToolCall(tool_call) = &partial.content[content_index]
                else {
                    panic!("expected toolCall at {content_index}");
                };
                assert_eq!(tool_call.name, "math_operation");
                accumulated_tool_args.push_str(&delta);
                // `arguments` is always a (possibly empty) parsed object while streaming;
                // the Rust type guarantees it is never undefined/null.
            }
            AssistantMessageEvent::ToolCallEnd {
                content_index,
                partial,
                ..
            } => {
                has_tool_end = true;
                assert_eq!(content_index, index);
                let AssistantContentBlock::ToolCall(tool_call) = &partial.content[content_index]
                else {
                    panic!("expected toolCall at {content_index}");
                };
                assert_eq!(tool_call.name, "math_operation");
                serde_json::from_str::<JsonValue>(&accumulated_tool_args)
                    .expect("accumulated tool args are JSON");
                assert_eq!(number_arg(&tool_call.arguments, "a"), Some(15.0));
                assert_eq!(number_arg(&tool_call.arguments, "b"), Some(27.0));
                let operation = tool_call
                    .arguments
                    .get("operation")
                    .and_then(JsonValue::as_str);
                assert!(
                    matches!(operation, Some("add" | "subtract" | "multiply" | "divide")),
                    "{operation:?}"
                );
            }
            _ => {}
        }
    }

    assert!(has_tool_start);
    assert!(has_tool_delta);
    assert!(has_tool_end);

    let response = events.result().await;
    assert_eq!(response.stop_reason, StopReason::ToolUse);
    let Some(AssistantContentBlock::ToolCall(tool_call)) = response
        .content
        .iter()
        .find(|block| matches!(block, AssistantContentBlock::ToolCall(_)))
    else {
        panic!("No tool call found in response");
    };
    assert_eq!(tool_call.name, "math_operation");
    assert!(!tool_call.id.is_empty());
}

async fn handle_streaming(model: Model, options: ProviderStreamOptions) {
    let context = context(
        "You are a helpful assistant.",
        vec![user(&json!("Count from 1 to 3"))],
        None,
    );
    let events = stream(&model, context, options).expect("stream");
    let mut text_started = false;
    let mut text_chunks = String::new();
    let mut text_completed = false;
    let mut iter = events.events();
    while let Some(event) = iter.next().await {
        match event {
            AssistantMessageEvent::TextStart { .. } => text_started = true,
            AssistantMessageEvent::TextDelta { delta, .. } => text_chunks.push_str(&delta),
            AssistantMessageEvent::TextEnd { .. } => text_completed = true,
            _ => {}
        }
    }
    let response = events.result().await;

    assert!(text_started);
    assert!(!text_chunks.is_empty());
    assert!(text_completed);
    assert!(response
        .content
        .iter()
        .any(|block| matches!(block, AssistantContentBlock::Text(_))));
}

async fn handle_thinking(model: Model, options: ProviderStreamOptions) {
    let operand = rand::random_range(0..255_u32);
    let context = context(
        "You are a helpful assistant.",
        vec![user(&json!(format!(
            "Think long and hard about {operand} + 27. Think step by step. Then output the result."
        )))],
        None,
    );
    let events = stream(&model, context, options).expect("stream");
    let mut thinking_started = false;
    let mut thinking_chunks = String::new();
    let mut thinking_completed = false;
    let mut iter = events.events();
    while let Some(event) = iter.next().await {
        match event {
            AssistantMessageEvent::ThinkingStart { .. } => thinking_started = true,
            AssistantMessageEvent::ThinkingDelta { delta, .. } => {
                thinking_chunks.push_str(&delta);
            }
            AssistantMessageEvent::ThinkingEnd { .. } => thinking_completed = true,
            _ => {}
        }
    }
    let response = events.result().await;

    assert_eq!(
        response.stop_reason,
        StopReason::Stop,
        "Error: {:?}",
        response.error_message
    );
    assert!(thinking_started);
    assert!(!thinking_chunks.is_empty());
    assert!(thinking_completed);
    assert!(response
        .content
        .iter()
        .any(|block| matches!(block, AssistantContentBlock::Thinking(_))));
}

async fn handle_image(model: Model, options: ProviderStreamOptions) {
    if !model.input.contains(&Modality::Image) {
        println!(
            "Skipping image test - model {} doesn't support images",
            model.id
        );
        return;
    }
    let image_path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/red-circle.png");
    let image = std::fs::read(image_path).expect("red-circle.png");
    let base64_image = base64::engine::general_purpose::STANDARD.encode(image);
    let context = context(
        "You are a helpful assistant.",
        vec![user(&json!([
            {
                "type": "text",
                "text": "What do you see in this image? Please describe the shape (circle, rectangle, square, triangle, ...) and color (red, blue, green, ...). You MUST reply in English.",
            },
            { "type": "image", "data": base64_image, "mimeType": "image/png" },
        ]))],
        None,
    );
    let response = complete(&model, context, options).await.expect("complete");

    assert!(!response.content.is_empty());
    if let Some(AssistantContentBlock::Text(text)) = response
        .content
        .iter()
        .find(|block| matches!(block, AssistantContentBlock::Text(_)))
    {
        let lower_content = text.text.to_lowercase();
        assert!(lower_content.contains("red"), "{lower_content}");
        assert!(lower_content.contains("circle"), "{lower_content}");
    }
}

async fn multi_turn(model: Model, options: ProviderStreamOptions) {
    let mut context = context(
        "You are a helpful assistant that can use tools to answer questions.",
        vec![user(&json!(
            "Think about this briefly, then calculate 42 * 17 and 453 + 434 using the math_operation tool."
        ))],
        Some(vec![calculator_tool()]),
    );
    let mut all_text_content = String::new();
    let mut has_seen_thinking = false;
    let mut has_seen_tool_calls = false;
    let max_turns = 5; // Prevent infinite loops

    for _ in 0..max_turns {
        let response = complete(&model, context.clone(), options.clone())
            .await
            .expect("complete");
        context.messages.push(Message::Assistant(response.clone()));

        let mut results = Vec::new();
        for block in &response.content {
            match block {
                AssistantContentBlock::Text(text) => all_text_content.push_str(&text.text),
                AssistantContentBlock::Thinking(_) => has_seen_thinking = true,
                AssistantContentBlock::ToolCall(tool_call) => {
                    has_seen_tool_calls = true;
                    assert_eq!(tool_call.name, "math_operation");
                    assert!(!tool_call.id.is_empty());
                    let (Some(a), Some(b)) = (
                        number_arg(&tool_call.arguments, "a"),
                        number_arg(&tool_call.arguments, "b"),
                    ) else {
                        panic!("Invalid math arguments");
                    };
                    let result = match tool_call
                        .arguments
                        .get("operation")
                        .and_then(JsonValue::as_str)
                    {
                        Some("add") => a + b,
                        Some("multiply") => a * b,
                        _ => 0.0,
                    };
                    results.push(
                        serde_json::from_value::<Message>(json!({
                            "role": "toolResult",
                            "toolCallId": tool_call.id,
                            "toolName": tool_call.name,
                            "content": [{ "type": "text", "text": format!("{result}") }],
                            "isError": false,
                            "timestamp": now_ms(),
                        }))
                        .expect("tool result"),
                    );
                }
            }
        }
        context.messages.extend(results);

        assert_ne!(
            response.stop_reason,
            StopReason::Error,
            "Error: {:?}",
            response.error_message
        );
        if response.stop_reason == StopReason::Stop {
            break;
        }
    }

    assert!(has_seen_thinking || has_seen_tool_calls);
    assert!(!all_text_content.is_empty());
    assert!(all_text_content.contains("714"), "{all_text_content}");
    assert!(all_text_content.contains("887"), "{all_text_content}");
}

// ---------------------------------------------------------------------------
// Provider matrix
// ---------------------------------------------------------------------------

/// One ignored live case: `attempts` is the TS `{ retry: N }`.
macro_rules! live {
    ($name:ident, $reason:literal, $attempts:literal, $body:expr) => {
        #[tokio::test]
        #[ignore = $reason]
        async fn $name() {
            with_retry($attempts, || $body).await;
        }
    };
}

const NO_OPTIONS: JsonValue = JsonValue::Null;

// Gemini Provider (gemini-2.5-flash)
macro_rules! gemini {
    ($name:ident, $scenario:ident, $extra:expr) => {
        live!(
            $name,
            "needs GEMINI_API_KEY; run with --ignored",
            3,
            async {
                require_env(&["GEMINI_API_KEY"]);
                $scenario(model("google", "gemini-2.5-flash"), options(&$extra)).await;
            }
        );
    };
}
gemini!(
    gemini_should_complete_basic_text_generation,
    basic_text_generation,
    NO_OPTIONS
);
gemini!(
    gemini_should_handle_tool_calling,
    handle_tool_call,
    NO_OPTIONS
);
gemini!(gemini_should_handle_streaming, handle_streaming, NO_OPTIONS);
gemini!(
    gemini_should_handle_thinking,
    handle_thinking,
    json!({ "thinking": { "enabled": true, "budgetTokens": 1024 } })
);
gemini!(
    gemini_should_handle_multi_turn_with_thinking_and_tools,
    multi_turn,
    json!({ "thinking": { "enabled": true, "budgetTokens": 2048 } })
);
gemini!(gemini_should_handle_image_input, handle_image, NO_OPTIONS);

// Google Vertex Provider (gemini-3-flash-preview)
macro_rules! vertex {
    ($name:ident, $scenario:ident, $thinking:expr) => {
        live!(
            $name,
            "needs GOOGLE_CLOUD_PROJECT (or GCLOUD_PROJECT) and GOOGLE_CLOUD_LOCATION; run with --ignored",
            3,
            async {
                let mut extra = vertex_options();
                if let JsonValue::Object(thinking) = $thinking {
                    extra["thinking"] = JsonValue::Object(thinking);
                }
                $scenario(model("google-vertex", "gemini-3-flash-preview"), options(&extra)).await;
            }
        );
    };
}
vertex!(
    google_vertex_should_complete_basic_text_generation,
    basic_text_generation,
    NO_OPTIONS
);
live!(
    google_vertex_should_complete_basic_text_generation_with_vertex_api_key,
    "needs GOOGLE_CLOUD_API_KEY; run with --ignored",
    3,
    async {
        let api_key = oauth_token("GOOGLE_CLOUD_API_KEY");
        basic_text_generation(
            model("google-vertex", "gemini-3-flash-preview"),
            with_api_key(ProviderStreamOptions::default(), api_key),
        )
        .await;
    }
);
vertex!(
    google_vertex_should_handle_tool_calling,
    handle_tool_call,
    NO_OPTIONS
);
vertex!(
    google_vertex_should_handle_thinking,
    handle_thinking,
    json!({ "enabled": true, "budgetTokens": 1024, "level": "LOW" })
);
vertex!(
    google_vertex_should_handle_streaming,
    handle_streaming,
    NO_OPTIONS
);
vertex!(
    google_vertex_should_handle_multi_turn_with_thinking_and_tools,
    multi_turn,
    json!({ "enabled": true, "budgetTokens": 1024, "level": "MEDIUM" })
);
vertex!(
    google_vertex_should_handle_image_input,
    handle_image,
    NO_OPTIONS
);

/// TS `{ ...getModel("openai", "gpt-4o-mini"), api: "openai-completions" }`
/// without `compat`.
fn openai_completions_model() -> Model {
    Model {
        api: "openai-completions".to_owned(),
        compat: None,
        ..model("openai", "gpt-4o-mini")
    }
}

// OpenAI Completions Provider (gpt-4o-mini)
macro_rules! openai_completions {
    ($name:ident, $scenario:ident) => {
        live!(
            $name,
            "needs OPENAI_API_KEY; run with --ignored",
            3,
            async {
                require_env(&["OPENAI_API_KEY"]);
                $scenario(openai_completions_model(), ProviderStreamOptions::default()).await;
            }
        );
    };
}
openai_completions!(
    openai_completions_should_complete_basic_text_generation,
    basic_text_generation
);
openai_completions!(
    openai_completions_should_handle_tool_calling,
    handle_tool_call
);
openai_completions!(openai_completions_should_handle_streaming, handle_streaming);
openai_completions!(openai_completions_should_handle_image_input, handle_image);

/// A suite keyed by one env var: `provider/model` with per-case options.
macro_rules! keyed {
    ($name:ident, $reason:literal, [$($var:literal),+], $attempts:literal, $provider:literal, $model:literal, $scenario:ident, $extra:expr) => {
        live!($name, $reason, $attempts, async {
            require_env(&[$($var),+]);
            $scenario(model($provider, $model), options(&$extra)).await;
        });
    };
}

// DeepSeek Provider (deepseek-flash via OpenAI Completions)
macro_rules! deepseek {
    ($name:ident, $scenario:ident, $extra:expr) => {
        keyed!(
            $name,
            "needs DEEPSEEK_API_KEY; run with --ignored",
            ["DEEPSEEK_API_KEY"],
            3,
            "deepseek",
            "deepseek-flash",
            $scenario,
            $extra
        );
    };
}
deepseek!(
    deepseek_should_complete_basic_text_generation,
    basic_text_generation,
    NO_OPTIONS
);
deepseek!(
    deepseek_should_handle_tool_calling,
    handle_tool_call,
    NO_OPTIONS
);
deepseek!(
    deepseek_should_handle_streaming,
    handle_streaming,
    NO_OPTIONS
);
deepseek!(
    deepseek_should_handle_thinking_mode,
    handle_thinking,
    json!({ "reasoningEffort": "high" })
);
deepseek!(
    deepseek_should_handle_multi_turn_with_thinking_and_tools,
    multi_turn,
    json!({ "reasoningEffort": "high" })
);

// OpenAI Responses Provider (gpt-5.4)
macro_rules! openai_responses {
    ($name:ident, $attempts:literal, $scenario:ident, $extra:expr) => {
        keyed!(
            $name,
            "needs OPENAI_API_KEY; run with --ignored",
            ["OPENAI_API_KEY"],
            $attempts,
            "openai",
            "gpt-5.4",
            $scenario,
            $extra
        );
    };
}
openai_responses!(
    openai_responses_should_complete_basic_text_generation,
    3,
    basic_text_generation,
    NO_OPTIONS
);
openai_responses!(
    openai_responses_should_handle_tool_calling,
    3,
    handle_tool_call,
    NO_OPTIONS
);
openai_responses!(
    openai_responses_should_handle_streaming,
    3,
    handle_streaming,
    NO_OPTIONS
);
openai_responses!(
    openai_responses_should_handle_thinking,
    2,
    handle_thinking,
    json!({ "reasoningEffort": "high" })
);
openai_responses!(
    openai_responses_should_handle_multi_turn_with_thinking_and_tools,
    3,
    multi_turn,
    json!({ "reasoningEffort": "high" })
);
openai_responses!(
    openai_responses_should_handle_image_input,
    3,
    handle_image,
    NO_OPTIONS
);

// Anthropic Provider (claude-haiku-4-5)
macro_rules! anthropic {
    ($name:ident, $scenario:ident, $extra:expr) => {
        keyed!(
            $name,
            "needs ANTHROPIC_API_KEY; run with --ignored",
            ["ANTHROPIC_API_KEY"],
            3,
            "anthropic",
            "claude-haiku-4-5",
            $scenario,
            $extra
        );
    };
}
anthropic!(
    anthropic_should_complete_basic_text_generation,
    basic_text_generation,
    json!({ "thinkingEnabled": true })
);
anthropic!(
    anthropic_should_handle_tool_calling,
    handle_tool_call,
    NO_OPTIONS
);
anthropic!(
    anthropic_should_handle_streaming,
    handle_streaming,
    NO_OPTIONS
);
anthropic!(
    anthropic_should_handle_image_input,
    handle_image,
    NO_OPTIONS
);

// Azure OpenAI Responses Provider (gpt-4o-mini)
macro_rules! azure {
    ($name:ident, $scenario:ident) => {
        live!(
            $name,
            "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL (or AZURE_OPENAI_RESOURCE_NAME); run with --ignored",
            3,
            async {
                require_azure_credentials();
                let llm = model("azure", "gpt-4o-mini");
                let azure_options = match resolve_azure_deployment_name(&llm.id) {
                    Some(name) => json!({ "azureDeploymentName": name }),
                    None => json!({}),
                };
                $scenario(llm, options(&azure_options)).await;
            }
        );
    };
}
azure!(
    azure_openai_responses_should_complete_basic_text_generation,
    basic_text_generation
);
azure!(
    azure_openai_responses_should_handle_tool_calling,
    handle_tool_call
);
azure!(
    azure_openai_responses_should_handle_streaming,
    handle_streaming
);
azure!(
    azure_openai_responses_should_handle_image_input,
    handle_image
);

/// The five-case suite most OpenAI-compatible providers share, inside a
/// module named after the provider so the test path reads `<provider>::<case>`.
macro_rules! five_case_suite {
    ($prefix:ident, $reason:literal, [$($var:literal),+], $provider:literal, $model:literal, $thinking:expr) => {
        mod $prefix {
            use super::*;
            keyed!(should_complete_basic_text_generation, $reason, [$($var),+], 3, $provider, $model, basic_text_generation, NO_OPTIONS);
            keyed!(should_handle_tool_calling, $reason, [$($var),+], 3, $provider, $model, handle_tool_call, NO_OPTIONS);
            keyed!(should_handle_streaming, $reason, [$($var),+], 3, $provider, $model, handle_streaming, NO_OPTIONS);
            keyed!(should_handle_thinking_mode, $reason, [$($var),+], 3, $provider, $model, handle_thinking, $thinking);
            keyed!(should_handle_multi_turn_with_thinking_and_tools, $reason, [$($var),+], 3, $provider, $model, multi_turn, $thinking);
        }
    };
}

// xAI Provider (grok-4.7 via OpenAI Responses)
five_case_suite!(
    xai,
    "needs XAI_API_KEY; run with --ignored",
    ["XAI_API_KEY"],
    "xai",
    "grok-4.7",
    json!({ "reasoningEffort": "medium" })
);
// Groq Provider (gpt-oss-20b via OpenAI Completions)
five_case_suite!(
    groq,
    "needs GROQ_API_KEY; run with --ignored",
    ["GROQ_API_KEY"],
    "groq",
    "openai/gpt-oss-20b",
    json!({ "reasoningEffort": "medium" })
);
// Cerebras Provider (gpt-oss-120b via OpenAI Completions)
five_case_suite!(
    cerebras,
    "needs CEREBRAS_API_KEY; run with --ignored",
    ["CEREBRAS_API_KEY"],
    "cerebras",
    "gpt-oss-120b",
    json!({ "reasoningEffort": "medium" })
);
// Cloudflare Workers AI Provider (Kimi K2.6 via OpenAI Completions)
five_case_suite!(
    cloudflare_workers_ai,
    "needs CLOUDFLARE_API_KEY and CLOUDFLARE_ACCOUNT_ID; run with --ignored",
    ["CLOUDFLARE_API_KEY", "CLOUDFLARE_ACCOUNT_ID"],
    "cloudflare-workers-ai",
    "@cf/moonshotai/kimi-k2.6",
    json!({ "reasoningEffort": "medium" })
);
// Cloudflare AI Gateway → Workers AI (Kimi K2.6 via /compat)
five_case_suite!(
    cloudflare_ai_gateway_workers_ai,
    "needs CLOUDFLARE_API_KEY, CLOUDFLARE_ACCOUNT_ID and CLOUDFLARE_GATEWAY_ID; run with --ignored",
    [
        "CLOUDFLARE_API_KEY",
        "CLOUDFLARE_ACCOUNT_ID",
        "CLOUDFLARE_GATEWAY_ID"
    ],
    "cloudflare-ai-gateway",
    "workers-ai/@cf/moonshotai/kimi-k2.6",
    json!({ "reasoningEffort": "medium" })
);

/// Cloudflare AI Gateway BYOK suites: the upstream key goes in `Authorization`.
macro_rules! gateway_byok {
    ($prefix:ident, $reason:literal, $key_var:literal, $model:literal, $effort:literal) => {
        mod $prefix {
            use super::*;

            fn byok(thinking: bool) -> ProviderStreamOptions {
                require_env(&["CLOUDFLARE_API_KEY", "CLOUDFLARE_ACCOUNT_ID", "CLOUDFLARE_GATEWAY_ID", $key_var]);
                let extra = if thinking {
                    json!({ "thinkingEnabled": true, "reasoningEffort": $effort })
                } else {
                    NO_OPTIONS
                };
                with_bearer(options(&extra), $key_var)
            }

            live!(should_complete_basic_text_generation, $reason, 3, async {
                basic_text_generation(model("cloudflare-ai-gateway", $model), byok(false)).await;
            });
            live!(should_handle_tool_calling, $reason, 3, async {
                handle_tool_call(model("cloudflare-ai-gateway", $model), byok(false)).await;
            });
            live!(should_handle_streaming, $reason, 3, async {
                handle_streaming(model("cloudflare-ai-gateway", $model), byok(false)).await;
            });
            live!(should_handle_thinking_mode, $reason, 3, async {
                handle_thinking(model("cloudflare-ai-gateway", $model), byok(true)).await;
            });
            live!(should_handle_multi_turn_with_thinking_and_tools, $reason, 3, async {
                multi_turn(model("cloudflare-ai-gateway", $model), byok(true)).await;
            });
        }
    };
}
// Cloudflare AI Gateway → OpenAI BYOK (gpt-5.1 via /openai responses)
gateway_byok!(
    cloudflare_ai_gateway_openai_byok,
    "needs CLOUDFLARE_API_KEY, CLOUDFLARE_ACCOUNT_ID, CLOUDFLARE_GATEWAY_ID and OPENAI_API_KEY; run with --ignored",
    "OPENAI_API_KEY",
    "gpt-5.1",
    "medium"
);
// Cloudflare AI Gateway → Anthropic BYOK (claude-sonnet-4-5 via /anthropic messages)
gateway_byok!(
    cloudflare_ai_gateway_anthropic_byok,
    "needs CLOUDFLARE_API_KEY, CLOUDFLARE_ACCOUNT_ID, CLOUDFLARE_GATEWAY_ID and ANTHROPIC_API_KEY; run with --ignored",
    "ANTHROPIC_API_KEY",
    "claude-sonnet-4-5",
    "high"
);

// Hugging Face Provider (Kimi-K2.5 via OpenAI Completions)
five_case_suite!(
    huggingface,
    "needs HF_TOKEN; run with --ignored",
    ["HF_TOKEN"],
    "huggingface",
    "moonshotai/Kimi-K2.5",
    json!({ "reasoningEffort": "medium" })
);

// Together AI Provider (Kimi-K3 via OpenAI Completions)
five_case_suite!(
    together,
    "needs TOGETHER_API_KEY; run with --ignored",
    ["TOGETHER_API_KEY"],
    "together",
    "moonshotai/Kimi-K3",
    json!({ "reasoningEffort": "high" })
);
keyed!(
    together_should_handle_image_input,
    "needs TOGETHER_API_KEY; run with --ignored",
    ["TOGETHER_API_KEY"],
    3,
    "together",
    "moonshotai/Kimi-K3",
    handle_image,
    NO_OPTIONS
);

// Baseten Provider (GLM 5.2 via OpenAI Completions): every case uses the options.
mod baseten {
    use super::*;
    macro_rules! baseten {
        ($name:ident, $scenario:ident) => {
            keyed!($name, "needs BASETEN_API_KEY; run with --ignored", ["BASETEN_API_KEY"], 3, "baseten", "zai-org/GLM-5.2", $scenario, json!({ "reasoningEffort": "high" }));
        };
    }
    baseten!(should_complete_basic_text_generation, basic_text_generation);
    baseten!(should_handle_tool_calling, handle_tool_call);
    baseten!(should_handle_streaming, handle_streaming);
    baseten!(should_handle_thinking_mode, handle_thinking);
    baseten!(should_handle_multi_turn_with_thinking_and_tools, multi_turn);
}

// NVIDIA NIM Provider (Nemotron 3 Ultra via OpenAI Completions)
five_case_suite!(
    nvidia,
    "needs NVIDIA_API_KEY; run with --ignored",
    ["NVIDIA_API_KEY"],
    "nvidia",
    "nvidia/nemotron-3-ultra-550b-a55b",
    json!({ "reasoningEffort": "high" })
);

// OpenRouter Provider (glm-4.5v via OpenAI Completions)
mod openrouter {
    use super::*;
    macro_rules! openrouter {
        ($name:ident, $attempts:literal, $scenario:ident, $extra:expr) => {
            keyed!(
                $name,
                "needs OPENROUTER_API_KEY; run with --ignored",
                ["OPENROUTER_API_KEY"],
                $attempts,
                "openrouter",
                "z-ai/glm-4.5v",
                $scenario,
                $extra
            );
        };
    }
    openrouter!(
        should_complete_basic_text_generation,
        3,
        basic_text_generation,
        NO_OPTIONS
    );
    openrouter!(should_handle_tool_calling, 3, handle_tool_call, NO_OPTIONS);
    openrouter!(should_handle_streaming, 3, handle_streaming, NO_OPTIONS);
    openrouter!(
        should_handle_thinking_mode,
        3,
        handle_thinking,
        json!({ "reasoningEffort": "medium" })
    );
    openrouter!(
        should_handle_multi_turn_with_thinking_and_tools,
        2,
        multi_turn,
        json!({ "reasoningEffort": "medium" })
    );
    openrouter!(should_handle_image_input, 3, handle_image, NO_OPTIONS);
}

/// Vercel AI Gateway suites (via Anthropic Messages).
macro_rules! vercel {
    ($prefix:ident, $model:literal) => {
        mod $prefix {
            use super::*;
            keyed!(
                should_complete_basic_text_generation,
                "needs AI_GATEWAY_API_KEY; run with --ignored",
                ["AI_GATEWAY_API_KEY"],
                3,
                "vercel-ai-gateway",
                $model,
                basic_text_generation,
                NO_OPTIONS
            );
            keyed!(
                should_handle_tool_calling,
                "needs AI_GATEWAY_API_KEY; run with --ignored",
                ["AI_GATEWAY_API_KEY"],
                3,
                "vercel-ai-gateway",
                $model,
                handle_tool_call,
                NO_OPTIONS
            );
            keyed!(
                should_handle_streaming,
                "needs AI_GATEWAY_API_KEY; run with --ignored",
                ["AI_GATEWAY_API_KEY"],
                3,
                "vercel-ai-gateway",
                $model,
                handle_streaming,
                NO_OPTIONS
            );
            keyed!(
                should_handle_image_input,
                "needs AI_GATEWAY_API_KEY; run with --ignored",
                ["AI_GATEWAY_API_KEY"],
                3,
                "vercel-ai-gateway",
                $model,
                handle_image,
                NO_OPTIONS
            );
            keyed!(
                should_handle_multi_turn_with_tools,
                "needs AI_GATEWAY_API_KEY; run with --ignored",
                ["AI_GATEWAY_API_KEY"],
                3,
                "vercel-ai-gateway",
                $model,
                multi_turn,
                NO_OPTIONS
            );
        }
    };
}
vercel!(
    vercel_ai_gateway_gemini_2_5_flash,
    "google/gemini-2.5-flash"
);
vercel!(
    vercel_ai_gateway_claude_opus_4_5,
    "anthropic/claude-opus-4.5"
);
vercel!(
    vercel_ai_gateway_gpt_5_1_codex_max,
    "openai/gpt-5.1-codex-max"
);

// zAI Provider (glm-5.2 via OpenAI Completions)
five_case_suite!(
    zai,
    "needs ZAI_API_KEY; run with --ignored",
    ["ZAI_API_KEY"],
    "zai",
    "glm-5.2",
    json!({ "reasoningEffort": "medium" })
);
keyed!(
    zai_should_handle_image_input,
    "needs ZAI_API_KEY; run with --ignored",
    ["ZAI_API_KEY"],
    3,
    "zai",
    "glm-5.2",
    handle_image,
    NO_OPTIONS
);

// Mistral Provider (devstral-medium-latest); thinking cases use mistral-small-2603.
mod mistral_devstral {
    use super::*;
    macro_rules! case {
        ($name:ident, $model:literal, $scenario:ident, $extra:expr) => {
            keyed!(
                $name,
                "needs MISTRAL_API_KEY; run with --ignored",
                ["MISTRAL_API_KEY"],
                3,
                "mistral",
                $model,
                $scenario,
                $extra
            );
        };
    }
    case!(
        should_complete_basic_text_generation,
        "devstral-medium-latest",
        basic_text_generation,
        NO_OPTIONS
    );
    case!(
        should_handle_tool_calling,
        "devstral-medium-latest",
        handle_tool_call,
        NO_OPTIONS
    );
    case!(
        should_handle_streaming,
        "devstral-medium-latest",
        handle_streaming,
        NO_OPTIONS
    );
    case!(
        should_handle_thinking_mode,
        "mistral-small-2603",
        handle_thinking,
        json!({ "reasoningEffort": "high" })
    );
    case!(
        should_handle_multi_turn_with_thinking_and_tools,
        "mistral-small-2603",
        multi_turn,
        json!({ "reasoningEffort": "high" })
    );
}

// Mistral Provider (pixtral-12b with image support)
mod mistral_pixtral {
    use super::*;
    macro_rules! case {
        ($name:ident, $scenario:ident) => {
            keyed!(
                $name,
                "needs MISTRAL_API_KEY; run with --ignored",
                ["MISTRAL_API_KEY"],
                3,
                "mistral",
                "pixtral-12b",
                $scenario,
                NO_OPTIONS
            );
        };
    }
    case!(should_complete_basic_text_generation, basic_text_generation);
    case!(should_handle_tool_calling, handle_tool_call);
    case!(should_handle_streaming, handle_streaming);
    case!(should_handle_image_input, handle_image);
}

// MiniMax Provider (MiniMax-M2.7 via Anthropic Messages)
five_case_suite!(
    minimax,
    "needs MINIMAX_API_KEY; run with --ignored",
    ["MINIMAX_API_KEY"],
    "minimax",
    "MiniMax-M2.7",
    json!({ "thinkingEnabled": true, "thinkingBudgetTokens": 2048 })
);
// Kimi For Coding Provider (kimi-for-coding via Anthropic Messages)
five_case_suite!(
    kimi_coding,
    "needs KIMI_API_KEY; run with --ignored",
    ["KIMI_API_KEY"],
    "kimi-coding",
    "kimi-for-coding",
    json!({ "thinkingEnabled": true, "thinkingBudgetTokens": 2048 })
);
// Meta Provider (muse-spark-1.3 via OpenAI Responses)
five_case_suite!(
    meta,
    "needs META_API_KEY; run with --ignored",
    ["META_API_KEY"],
    "meta",
    "muse-spark-1.3",
    json!({ "thinkingEnabled": true, "thinkingBudgetTokens": 2048 })
);
// Xiaomi MiMo (API billing) Provider (MiMo-V2.5-Pro via Anthropic Messages)
five_case_suite!(
    xiaomi,
    "needs XIAOMI_API_KEY; run with --ignored",
    ["XIAOMI_API_KEY"],
    "xiaomi",
    "mimo-v2.5-pro",
    json!({ "thinkingEnabled": true, "reasoningEffort": "high" })
);
// Xiaomi MiMo Token Plan Provider, CN region
five_case_suite!(
    xiaomi_token_plan_cn,
    "needs XIAOMI_TOKEN_PLAN_CN_API_KEY; run with --ignored",
    ["XIAOMI_TOKEN_PLAN_CN_API_KEY"],
    "xiaomi-token-plan-cn",
    "mimo-v2.5-pro",
    json!({ "thinkingEnabled": true, "reasoningEffort": "high" })
);
// Xiaomi MiMo Token Plan Provider, AMS region
five_case_suite!(
    xiaomi_token_plan_ams,
    "needs XIAOMI_TOKEN_PLAN_AMS_API_KEY; run with --ignored",
    ["XIAOMI_TOKEN_PLAN_AMS_API_KEY"],
    "xiaomi-token-plan-ams",
    "mimo-v2.5-pro",
    json!({ "thinkingEnabled": true, "reasoningEffort": "high" })
);
// Xiaomi MiMo Token Plan Provider, SGP region
five_case_suite!(
    xiaomi_token_plan_sgp,
    "needs XIAOMI_TOKEN_PLAN_SGP_API_KEY; run with --ignored",
    ["XIAOMI_TOKEN_PLAN_SGP_API_KEY"],
    "xiaomi-token-plan-sgp",
    "mimo-v2.5-pro",
    json!({ "thinkingEnabled": true, "reasoningEffort": "high" })
);
// Qwen Token Plan Provider (Qwen3.7-Max, international)
five_case_suite!(
    qwen_token_plan,
    "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored",
    ["QWEN_TOKEN_PLAN_API_KEY"],
    "qwen-token-plan",
    "qwen3.7-max",
    json!({ "thinkingEnabled": true, "reasoningEffort": "high" })
);
// Qwen Token Plan Individual Provider (Qwen3.8-Max, international)
five_case_suite!(
    qwen_token_plan_individual,
    "needs QWEN_TOKEN_PLAN_API_KEY; run with --ignored",
    ["QWEN_TOKEN_PLAN_API_KEY"],
    "qwen-token-plan-individual",
    "qwen3.8-max",
    json!({ "thinkingEnabled": true, "reasoningEffort": "high" })
);
// Qwen Token Plan Provider (Qwen3.7-Max, CN region)
five_case_suite!(
    qwen_token_plan_cn,
    "needs QWEN_TOKEN_PLAN_CN_API_KEY; run with --ignored",
    ["QWEN_TOKEN_PLAN_CN_API_KEY"],
    "qwen-token-plan-cn",
    "qwen3.7-max",
    json!({ "thinkingEnabled": true, "reasoningEffort": "high" })
);

// Ant Ling Provider (Ling 2.6 Flash via OpenAI Completions); thinking uses Ring-2.6-1T.
mod ant_ling {
    use super::*;
    macro_rules! case {
        ($name:ident, $model:literal, $scenario:ident, $extra:expr) => {
            keyed!(
                $name,
                "needs ANT_LING_API_KEY; run with --ignored",
                ["ANT_LING_API_KEY"],
                3,
                "ant-ling",
                $model,
                $scenario,
                $extra
            );
        };
    }
    case!(
        should_complete_basic_text_generation,
        "Ling-2.6-flash",
        basic_text_generation,
        NO_OPTIONS
    );
    case!(
        should_handle_tool_calling,
        "Ling-2.6-flash",
        handle_tool_call,
        NO_OPTIONS
    );
    case!(
        should_handle_streaming,
        "Ling-2.6-flash",
        handle_streaming,
        NO_OPTIONS
    );
    case!(
        should_handle_thinking_mode,
        "Ring-2.6-1T",
        handle_thinking,
        json!({ "reasoningEffort": "high" })
    );
}

// ---------------------------------------------------------------------------
// OAuth-based providers (TS `resolveApiKey`; here `PI_TEST_<PROVIDER>_TOKEN`)
// ---------------------------------------------------------------------------

/// A case authenticated with the OAuth token in `$var`.
macro_rules! oauth {
    ($name:ident, $reason:literal, $var:literal, $attempts:literal, $provider:literal, $model:literal, $scenario:ident, $extra:expr) => {
        live!($name, $reason, $attempts, async {
            let token = oauth_token($var);
            $scenario(
                model($provider, $model),
                with_api_key(options(&$extra), token),
            )
            .await;
        });
    };
}

// Anthropic OAuth Provider (claude-sonnet-4-6)
mod anthropic_oauth_sonnet_4_6 {
    use super::*;
    macro_rules! case {
        ($name:ident, $scenario:ident, $extra:expr) => {
            oauth!(
                $name,
                "needs PI_TEST_ANTHROPIC_TOKEN (Anthropic OAuth); run with --ignored",
                "PI_TEST_ANTHROPIC_TOKEN",
                3,
                "anthropic",
                "claude-sonnet-4-6",
                $scenario,
                $extra
            );
        };
    }
    case!(
        should_complete_basic_text_generation,
        basic_text_generation,
        NO_OPTIONS
    );
    case!(should_handle_tool_calling, handle_tool_call, NO_OPTIONS);
    case!(should_handle_streaming, handle_streaming, NO_OPTIONS);
    case!(
        should_handle_thinking,
        handle_thinking,
        json!({ "thinkingEnabled": true })
    );
    case!(
        should_handle_multi_turn_with_thinking_and_tools,
        multi_turn,
        json!({ "thinkingEnabled": true })
    );
    case!(should_handle_image_input, handle_image, NO_OPTIONS);
}

// Anthropic OAuth Provider (claude-opus-4-6 with adaptive thinking)
mod anthropic_oauth_opus_4_6 {
    use super::*;
    macro_rules! case {
        ($name:ident, $scenario:ident, $extra:expr) => {
            oauth!(
                $name,
                "needs PI_TEST_ANTHROPIC_TOKEN (Anthropic OAuth); run with --ignored",
                "PI_TEST_ANTHROPIC_TOKEN",
                3,
                "anthropic",
                "claude-opus-4-6",
                $scenario,
                $extra
            );
        };
    }
    case!(
        should_complete_basic_text_generation,
        basic_text_generation,
        NO_OPTIONS
    );
    case!(should_handle_tool_calling, handle_tool_call, NO_OPTIONS);
    case!(should_handle_streaming, handle_streaming, NO_OPTIONS);
    case!(
        should_handle_adaptive_thinking_with_effort_high,
        handle_thinking,
        json!({ "thinkingEnabled": true, "effort": "high" })
    );
    case!(
        should_handle_adaptive_thinking_with_effort_medium,
        handle_thinking,
        json!({ "thinkingEnabled": true, "effort": "medium" })
    );
    case!(
        should_handle_multi_turn_with_adaptive_thinking_and_tools,
        multi_turn,
        json!({ "thinkingEnabled": true, "effort": "high" })
    );
    case!(should_handle_image_input, handle_image, NO_OPTIONS);
}

// GitHub Copilot Provider (gpt-5.3-codex via OpenAI Completions); thinking uses gpt-5-mini.
mod github_copilot_gpt_5_3_codex {
    use super::*;
    macro_rules! case {
        ($name:ident, $attempts:literal, $model:literal, $scenario:ident, $extra:expr) => {
            oauth!(
                $name,
                "needs PI_TEST_GITHUB_COPILOT_TOKEN (GitHub Copilot OAuth); run with --ignored",
                "PI_TEST_GITHUB_COPILOT_TOKEN",
                $attempts,
                "github-copilot",
                $model,
                $scenario,
                $extra
            );
        };
    }
    case!(
        should_complete_basic_text_generation,
        3,
        "gpt-5.3-codex",
        basic_text_generation,
        NO_OPTIONS
    );
    case!(
        should_handle_tool_calling,
        3,
        "gpt-5.3-codex",
        handle_tool_call,
        NO_OPTIONS
    );
    case!(
        should_handle_streaming,
        3,
        "gpt-5.3-codex",
        handle_streaming,
        NO_OPTIONS
    );
    case!(
        should_handle_thinking,
        2,
        "gpt-5-mini",
        handle_thinking,
        json!({ "reasoningEffort": "high" })
    );
    case!(
        should_handle_multi_turn_with_thinking_and_tools,
        3,
        "gpt-5-mini",
        multi_turn,
        json!({ "reasoningEffort": "high" })
    );
    case!(
        should_handle_image_input,
        3,
        "gpt-5.3-codex",
        handle_image,
        NO_OPTIONS
    );
}

// GitHub Copilot Provider (claude-sonnet-4.6 via Anthropic Messages)
mod github_copilot_claude_sonnet_4_6 {
    use super::*;
    macro_rules! case {
        ($name:ident, $attempts:literal, $scenario:ident, $extra:expr) => {
            oauth!(
                $name,
                "needs PI_TEST_GITHUB_COPILOT_TOKEN (GitHub Copilot OAuth); run with --ignored",
                "PI_TEST_GITHUB_COPILOT_TOKEN",
                $attempts,
                "github-copilot",
                "claude-sonnet-4.6",
                $scenario,
                $extra
            );
        };
    }
    case!(
        should_complete_basic_text_generation,
        3,
        basic_text_generation,
        NO_OPTIONS
    );
    case!(should_handle_tool_calling, 3, handle_tool_call, NO_OPTIONS);
    case!(should_handle_streaming, 3, handle_streaming, NO_OPTIONS);
    case!(
        should_handle_thinking,
        2,
        handle_thinking,
        json!({ "thinkingEnabled": true })
    );
    case!(
        should_handle_multi_turn_with_thinking_and_tools,
        3,
        multi_turn,
        json!({ "thinkingEnabled": true })
    );
    case!(should_handle_image_input, 3, handle_image, NO_OPTIONS);
}

// OpenAI Codex Provider (gpt-5.5)
mod openai_codex {
    use super::*;
    macro_rules! case {
        ($name:ident, $scenario:ident, $extra:expr) => {
            oauth!(
                $name,
                "needs PI_TEST_OPENAI_CODEX_TOKEN (OpenAI Codex OAuth); run with --ignored",
                "PI_TEST_OPENAI_CODEX_TOKEN",
                3,
                "openai-codex",
                "gpt-5.5",
                $scenario,
                $extra
            );
        };
    }
    case!(
        should_complete_basic_text_generation,
        basic_text_generation,
        NO_OPTIONS
    );
    case!(should_handle_tool_calling, handle_tool_call, NO_OPTIONS);
    case!(should_handle_streaming, handle_streaming, NO_OPTIONS);
    case!(
        should_handle_thinking_with_reasoning_effort_xhigh,
        handle_thinking,
        json!({ "reasoningEffort": "xhigh" })
    );
    case!(
        should_handle_multi_turn_with_thinking_and_tools,
        multi_turn,
        json!({ "reasoningEffort": "xhigh" })
    );
    case!(should_handle_image_input, handle_image, NO_OPTIONS);
}

// OpenAI Codex Provider (gpt-5.5 via WebSocket)
mod openai_codex_websocket {
    use super::*;
    macro_rules! case {
        ($name:ident, $scenario:ident, $extra:expr) => {
            live!(
                $name,
                "needs PI_TEST_OPENAI_CODEX_TOKEN (OpenAI Codex OAuth); run with --ignored",
                3,
                async {
                    let token = oauth_token("PI_TEST_OPENAI_CODEX_TOKEN");
                    $scenario(model("openai-codex", "gpt-5.5"), websocket(token, &$extra)).await;
                }
            );
        };
    }
    case!(
        should_complete_basic_text_generation,
        basic_text_generation,
        NO_OPTIONS
    );
    case!(should_handle_tool_calling, handle_tool_call, NO_OPTIONS);
    case!(should_handle_streaming, handle_streaming, NO_OPTIONS);
    case!(
        should_handle_thinking_with_reasoning_effort_xhigh,
        handle_thinking,
        json!({ "reasoningEffort": "xhigh" })
    );
    case!(
        should_handle_multi_turn_with_thinking_and_tools,
        multi_turn,
        json!({ "reasoningEffort": "xhigh" })
    );
    case!(should_handle_image_input, handle_image, NO_OPTIONS);
}

// ---------------------------------------------------------------------------
// Amazon Bedrock
// ---------------------------------------------------------------------------

const BEDROCK_SONNET: &str = "global.anthropic.claude-sonnet-4-5-20250929-v1:0";

// Amazon Bedrock Provider (claude-sonnet-4-5)
mod bedrock_claude_sonnet_4_5 {
    use super::*;
    macro_rules! case {
        ($name:ident, $scenario:ident, $extra:expr) => {
            live!($name, "needs AWS_PROFILE, AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored", 3, async {
                require_bedrock_credentials();
                $scenario(model("amazon-bedrock", BEDROCK_SONNET), options(&$extra)).await;
            });
        };
    }
    case!(
        should_complete_basic_text_generation,
        basic_text_generation,
        NO_OPTIONS
    );
    case!(should_handle_tool_calling, handle_tool_call, NO_OPTIONS);
    case!(should_handle_streaming, handle_streaming, NO_OPTIONS);
    case!(
        should_handle_thinking,
        handle_thinking,
        json!({ "reasoning": "medium" })
    );
    case!(
        should_handle_multi_turn_with_thinking_and_tools,
        multi_turn,
        json!({ "reasoning": "high" })
    );
    case!(should_handle_image_input, handle_image, NO_OPTIONS);
}

/// Options whose `onPayload` records the provider payload.
fn capturing(extra: &JsonValue) -> (ProviderStreamOptions, Arc<Mutex<Option<JsonValue>>>) {
    let captured = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&captured);
    let mut options = options(extra);
    options.stream.request.on_payload = Some(Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async { Ok(None) })
    }));
    (options, captured)
}

fn captured_payload(captured: &Mutex<Option<JsonValue>>) -> JsonValue {
    captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("payload captured")
}

async fn say_hi(llm: &Model, options: ProviderStreamOptions) {
    let response = complete(
        llm,
        Context {
            system_prompt: None,
            messages: vec![user(&json!("Say hi."))],
            tools: None,
        },
        options,
    )
    .await
    .expect("complete");
    assert_ne!(
        response.stop_reason,
        StopReason::Error,
        "Error: {:?}",
        response.error_message
    );
}

// Amazon Bedrock Provider (claude-opus-4-6 interleaved thinking)
mod bedrock_claude_opus_4_6 {
    use super::*;

    live!(
        should_use_adaptive_thinking_without_anthropic_beta,
        "needs AWS_PROFILE, AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored",
        3,
        async {
            require_bedrock_credentials();
            let llm = model("amazon-bedrock", "global.anthropic.claude-opus-4-6-v1");
            let (options, captured) =
                capturing(&json!({ "reasoning": "xhigh", "interleavedThinking": true }));
            let response = complete(
                &llm,
                context(
                    "You are a helpful assistant that uses tools when asked.",
                    vec![user(&json!(
                        "Think first, then calculate 15 + 27 using the math_operation tool."
                    ))],
                    Some(vec![calculator_tool()]),
                ),
                options,
            )
            .await
            .expect("complete");

            assert_ne!(
                response.stop_reason,
                StopReason::Error,
                "Error: {:?}",
                response.error_message
            );
            let payload = captured_payload(&captured);
            let fields = &payload["additionalModelRequestFields"];
            assert_eq!(
                fields["thinking"],
                json!({ "type": "adaptive", "display": "summarized" })
            );
            assert_eq!(fields["output_config"], json!({ "effort": "max" }));
            assert!(fields.get("anthropic_beta").is_none());
        }
    );

    live!(
        should_pass_request_metadata_to_the_sdk_payload,
        "needs AWS_PROFILE, AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored",
        3,
        async {
            require_bedrock_credentials();
            let metadata = json!({ "app": "pi-test", "env": "ci" });
            let (options, captured) = capturing(&json!({ "requestMetadata": metadata }));
            say_hi(&model("amazon-bedrock", BEDROCK_SONNET), options).await;
            assert_eq!(captured_payload(&captured)["requestMetadata"], metadata);
        }
    );

    live!(
        should_omit_request_metadata_from_payload_when_not_provided,
        "needs AWS_PROFILE, AWS_ACCESS_KEY_ID + AWS_SECRET_ACCESS_KEY, or AWS_BEARER_TOKEN_BEDROCK; run with --ignored",
        3,
        async {
            require_bedrock_credentials();
            let (options, captured) = capturing(&NO_OPTIONS);
            say_hi(&model("amazon-bedrock", BEDROCK_SONNET), options).await;
            assert!(captured_payload(&captured).get("requestMetadata").is_none());
        }
    );
}

// ---------------------------------------------------------------------------
// Ollama Provider (gpt-oss-20b via OpenAI Completions)
// ---------------------------------------------------------------------------

mod ollama {
    use super::*;
    use std::process::{Child, Command, Stdio};

    /// TS `afterAll`: kills the `ollama serve` this case started.
    struct OllamaServer(Child);

    impl Drop for OllamaServer {
        fn drop(&mut self) {
            // The server may already have exited (e.g. one was already running);
            // there is nothing to clean up then.
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }

    /// TS `beforeAll`: requires `ollama` (and `PI_NO_LOCAL_LLM` unset), pulls
    /// `gpt-oss:20b` when missing, starts `ollama serve`, and waits until
    /// `/api/tags` answers.
    async fn start() -> (OllamaServer, Model) {
        assert!(
            env("PI_NO_LOCAL_LLM").is_none(),
            "PI_NO_LOCAL_LLM disables local LLM tests"
        );
        let installed = Command::new("which")
            .arg("ollama")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|status| status.success());
        assert!(installed, "ollama must be installed to run this test");

        let list = Command::new("ollama")
            .arg("list")
            .output()
            .expect("ollama list");
        if !String::from_utf8_lossy(&list.stdout).contains("gpt-oss:20b") {
            println!("Pulling gpt-oss:20b model for Ollama tests...");
            let pulled = Command::new("ollama")
                .args(["pull", "gpt-oss:20b"])
                .status()
                .is_ok_and(|status| status.success());
            assert!(pulled, "Failed to pull gpt-oss:20b model");
        }

        let server = OllamaServer(
            Command::new("ollama")
                .arg("serve")
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()
                .expect("spawn ollama serve"),
        );

        // Readiness poll of an external process (TS: first check after 1s, then every 500ms).
        let ready = async {
            tokio::time::sleep(std::time::Duration::from_secs(1)).await;
            loop {
                let ok = reqwest::get("http://localhost:11434/api/tags")
                    .await
                    .is_ok_and(|response| response.status().is_success());
                if ok {
                    break;
                }
                tokio::time::sleep(std::time::Duration::from_millis(500)).await;
            }
        };
        tokio::time::timeout(std::time::Duration::from_secs(30), ready)
            .await
            .expect("ollama ready within 30s");

        let llm: Model = serde_json::from_value(json!({
            "id": "gpt-oss:20b",
            "api": "openai-completions",
            "provider": "ollama",
            "baseUrl": "http://localhost:11434/v1",
            "reasoning": true,
            "input": ["text"],
            "contextWindow": 128_000,
            "maxTokens": 16_000,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
            "name": "Ollama GPT-OSS 20B",
        }))
        .expect("ollama model");
        (server, llm)
    }

    macro_rules! case {
        ($name:ident, $scenario:ident, $extra:expr) => {
            live!($name, "needs a local ollama install (gpt-oss:20b) and PI_NO_LOCAL_LLM unset; run with --ignored", 3, async {
                let (_server, llm) = start().await;
                $scenario(llm, with_api_key(options(&$extra), "test".to_owned())).await;
            });
        };
    }
    case!(
        should_complete_basic_text_generation,
        basic_text_generation,
        NO_OPTIONS
    );
    case!(should_handle_tool_calling, handle_tool_call, NO_OPTIONS);
    case!(should_handle_streaming, handle_streaming, NO_OPTIONS);
    case!(
        should_handle_thinking_mode,
        handle_thinking,
        json!({ "reasoningEffort": "medium" })
    );
    case!(
        should_handle_multi_turn_with_thinking_and_tools,
        multi_turn,
        json!({ "reasoningEffort": "medium" })
    );
}
