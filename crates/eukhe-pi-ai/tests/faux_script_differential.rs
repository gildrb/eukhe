//! eukhe addition: differential check of the faux-script format. For each
//! fixture script, the old `eukhe-ai` scripted faux provider and the
//! `eukhe-pi-ai` one stream the same content: the same event sequence (with
//! token-sized deltas merged, since chunk sizes are random), the same final
//! content blocks, stop reasons, error messages, and usage counts, and the
//! same scripted model.
//!
//! The old provider registers into a process-wide registry under the api
//! `faux`, so all fixtures run sequentially in this one test binary.
//!
//! Fixtures keep non-ASCII text inside the Basic Multilingual Plane: the old
//! provider estimated tokens from `char` counts, the port from UTF-16 code
//! units (TS `.length`), so astral-plane characters (emoji) count twice in
//! the port by design.

use eukhe_ai::faux::script as old_script;
use eukhe_ai::types as old;
use eukhe_pi_ai::providers::faux_script::{create_faux_script_models, parse_faux_script_value};
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{AssistantMessageEvent, Context, Message, UserContent, UserMessage};
use futures::StreamExt;
use serde_json::{json, Map, Value};

const SYSTEM_PROMPT: &str = "Be concise.";
const USER_TEXT: &str = "hi there";

fn fixtures() -> Vec<(&'static str, Value)> {
    vec![
        (
            "plain strings and text entries",
            json!({ "responses": ["hello world", { "text": "second" }, { "text": 1 }, { "content": 1 }] }),
        ),
        (
            "content blocks on a custom model",
            json!({
                "modelId": "faux-custom",
                "modelName": "Custom Faux",
                "reasoning": true,
                "contextWindow": 32_000,
                "maxTokens": 2048,
                "responses": [
                    {
                        "content": [
                            { "type": "thinking", "thinking": "Let me think about the request step by step." },
                            { "type": "text", "text": "Here is the answer, with some unicode: héllo wörld ✓." },
                        ],
                    },
                ],
            }),
        ),
        (
            "tool calls default to toolUse",
            json!({
                "responses": [
                    {
                        "content": [
                            { "type": "text", "text": "Running code." },
                            {
                                "type": "toolCall",
                                "name": "ipython",
                                "id": "call-1",
                                "arguments": { "code": "print('hi')\nx = [1, 2, {\"a\": null}]" },
                            },
                            { "type": "toolCall", "name": "noop", "id": "call-2" },
                        ],
                    },
                    "done",
                ],
            }),
        ),
        (
            "scripted stop reasons and error messages",
            json!({
                "responses": [
                    { "text": "partial", "stopReason": "error", "errorMessage": "prompt is too long: 300000 tokens > 200000 maximum" },
                    { "text": "cut short", "stopReason": "aborted" },
                    { "text": "truncated", "stopReason": "length" },
                    { "content": [{ "type": "toolCall", "name": "x", "id": "call-3" }], "stopReason": "stop" },
                ],
            }),
        ),
        (
            "paced and delayed responses",
            json!({
                "tokensPerSecond": 200,
                "responses": [
                    { "text": "after a hold", "delayMs": 40 },
                    "paced text that spans several chunks of tokens",
                ],
            }),
        ),
        (
            "repeat last response",
            json!({ "repeatLastResponse": true, "responses": ["first", "last"] }),
        ),
    ]
}

/// The event as JSON without its message snapshots. The `toolcall_end`
/// call drops its `type` tag: the old event type serialized the bare call
/// struct, the port the tagged content block (TS shape).
fn event_shape(mut event: Value) -> Value {
    if let Some(object) = event.as_object_mut() {
        for key in ["partial", "message", "error"] {
            object.remove(key);
        }
        if let Some(Value::Object(call)) = object.get_mut("toolCall") {
            call.remove("type");
        }
    }
    event
}

/// Merges runs of deltas of one type and content index into one delta.
fn merged_events(events: Vec<Value>) -> Vec<Value> {
    let mut merged: Vec<Value> = Vec::new();
    for event in events.into_iter().map(event_shape) {
        let is_delta = event["type"]
            .as_str()
            .is_some_and(|kind| kind.ends_with("_delta"));
        if is_delta {
            if let Some(previous) = merged.last_mut() {
                if previous["type"] == event["type"]
                    && previous["contentIndex"] == event["contentIndex"]
                {
                    let joined = format!(
                        "{}{}",
                        previous["delta"].as_str().unwrap_or_default(),
                        event["delta"].as_str().unwrap_or_default()
                    );
                    previous["delta"] = Value::String(joined);
                    continue;
                }
            }
        }
        merged.push(event);
    }
    merged
}

/// The final message fields both providers carry.
fn message_shape(message: &Value) -> Value {
    let usage = &message["usage"];
    json!({
        "content": message["content"],
        "api": message["api"],
        "provider": message["provider"],
        "model": message["model"],
        "stopReason": message["stopReason"],
        "errorMessage": message.get("errorMessage").cloned().unwrap_or(Value::Null),
        "usage": {
            "input": usage["input"],
            "output": usage["output"],
            "cacheRead": usage["cacheRead"],
            "cacheWrite": usage["cacheWrite"],
            "totalTokens": usage["totalTokens"],
        },
    })
}

/// The scripted model fields both providers carry.
fn model_shape(model: &Value) -> Value {
    let mut shape = Map::new();
    for key in [
        "id",
        "name",
        "api",
        "provider",
        "baseUrl",
        "reasoning",
        "input",
        "contextWindow",
        "maxTokens",
    ] {
        shape.insert(key.to_owned(), model[key].clone());
    }
    Value::Object(shape)
}

fn to_json<T: serde::Serialize>(value: &T) -> Value {
    serde_json::to_value(value).expect("serializable")
}

/// One call against the old provider: merged events and final message.
async fn old_call(model: &old::Model) -> (Vec<Value>, Value) {
    let context = old::Context {
        system_prompt: Some(SYSTEM_PROMPT.to_owned()),
        messages: vec![old::Message::User(old::UserMessage {
            content: old::UserMessageContent::Text(USER_TEXT.to_owned()),
            timestamp: 0,
            rest: Map::default(),
        })],
        tools: None,
    };
    let events: Vec<Value> = eukhe_ai::stream(model, &context, None)
        .expect("the faux api is registered")
        .collect()
        .await
        .iter()
        .map(to_json)
        .collect();
    let last = events.last().expect("the stream ends with an event");
    let message = last
        .get("message")
        .or_else(|| last.get("error"))
        .expect("the terminal event carries the message")
        .clone();
    (merged_events(events), message_shape(&message))
}

#[tokio::test(start_paused = true)]
async fn old_and_new_scripted_providers_stream_identical_messages() {
    for (name, script) in fixtures() {
        let old_parsed = old_script::parse_faux_script(&script).expect("old parser accepts");
        let old_registration = old_script::register_faux_provider_from_script(&old_parsed);
        let old_model = old_registration.get_model();

        let (models, faux) = create_faux_script_models(
            parse_faux_script_value(&script).expect("new parser accepts"),
        );
        let new_model = faux.get_model();
        assert_eq!(
            model_shape(&to_json(&new_model)),
            model_shape(&to_json(&old_model)),
            "{name}: scripted model"
        );

        // Every queued response, then two more calls (the exhaustion error
        // or the repeated last response).
        let calls = old_parsed.responses.len() + 2;
        for call in 0..calls {
            let (old_events, old_message) = old_call(&old_model).await;

            let stream = models.stream_simple(
                &new_model,
                Context {
                    system_prompt: Some(SYSTEM_PROMPT.to_owned()),
                    messages: vec![Message::User(UserMessage {
                        content: UserContent::Text(USER_TEXT.to_owned()),
                        timestamp: 0,
                    })],
                    tools: None,
                },
                SimpleStreamOptions::default().into(),
            );
            let new_events: Vec<AssistantMessageEvent> = stream.events().collect().await;
            let new_message = stream.result().await;

            assert_eq!(
                message_shape(&to_json(&new_message)),
                old_message,
                "{name}: call {call} final message"
            );
            assert_eq!(
                merged_events(new_events.iter().map(to_json).collect()),
                old_events,
                "{name}: call {call} events"
            );
        }
        assert_eq!(
            faux.call_count(),
            old_registration.call_count(),
            "{name}: call count"
        );
        old_registration.unregister();
    }
}
