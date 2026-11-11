//! Port of `test/anthropic-mid-conversation-effort.test.ts`, on Eukhe's
//! effort plan: the top-level effort is the first request's and
//! per-message controls carry only the changes.

mod anthropic_support;

use std::fmt::Write;

use anthropic_support::{
    builtin_model, capturing_on_payload, context, mock_fetch, model, take_payload, MockResponse,
};
use eukhe_ai::api::anthropic_messages::stream;
use eukhe_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{AssistantMessage, CacheRetention, JsonValue, Model, StopReason};
use serde_json::json;

fn managed_model(provider: &str) -> Model {
    managed_model_with(provider, &json!({}))
}

/// [`managed_model`] with `compat` entries added.
fn managed_model_with(provider: &str, compat: &JsonValue) -> Model {
    let mut all = json!({ "forceAdaptiveThinking": true, "supportsMidConvoEffort": true });
    for (key, value) in compat.as_object().expect("compat object") {
        all[key] = value.clone();
    }
    model(&json!({
        "id": "claude-fable-5-1",
        "name": "Claude Fable 5.1",
        "provider": provider,
        "baseUrl": "http://127.0.0.1:9",
        "reasoning": true,
        "thinkingLevelMap": { "off": null, "minimal": "low", "low": "low", "medium": "medium", "high": "high", "max": "max" },
        "contextWindow": 200_000,
        "maxTokens": 32000,
        "compat": all,
    }))
}

fn assistant(model: &Model, level: Option<&str>) -> JsonValue {
    let mut message = json!({
        "role": "assistant",
        "content": [
            { "type": "thinking", "thinking": "reasoning", "thinkingSignature": "signature" },
            { "type": "text", "text": "answer" },
        ],
        "api": "anthropic-messages",
        "provider": model.provider,
        "model": model.id,
    });
    if let Some(level) = level {
        message["providerThinkingLevel"] = json!(level);
    }
    let rest = json!({
        "usage": {
            "input": 0,
            "output": 0,
            "cacheRead": 0,
            "cacheWrite": 0,
            "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": "stop",
        "timestamp": 1,
    });
    for (key, value) in rest.as_object().expect("object") {
        message[key] = value.clone();
    }
    message
}

struct Captured {
    payload: JsonValue,
    message: AssistantMessage,
}

async fn capture(model: &Model, ctx: &JsonValue, effort: Option<&str>) -> Captured {
    capture_thinking(model, ctx, true, effort).await
}

/// One request through the real param path; `thinking_enabled` false is
/// thinking off.
async fn capture_thinking(
    model: &Model,
    ctx: &JsonValue,
    thinking_enabled: bool,
    effort: Option<&str>,
) -> Captured {
    let (on_payload, captured) = capturing_on_payload();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test-key".into());
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.on_payload = Some(on_payload);
    options
        .extra
        .insert("thinkingEnabled".into(), json!(thinking_enabled));
    if let Some(effort) = effort {
        options.extra.insert("effort".into(), json!(effort));
    }
    let message = stream(model, &context(ctx), options).result().await;
    Captured {
        payload: take_payload(&captured),
        message,
    }
}

fn user(text: &str, timestamp: u64) -> JsonValue {
    json!({ "role": "user", "content": text, "timestamp": timestamp })
}

fn effort_messages(payload: &JsonValue) -> Vec<JsonValue> {
    payload["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .filter(|message| message["role"] == "system")
        .cloned()
        .collect()
}

fn control(effort: &str) -> JsonValue {
    json!({ "role": "system", "content": [], "output_config": { "effort": effort } })
}

fn bound_adaptive() -> JsonValue {
    json!({
        "type": "adaptive",
        "display": "summarized",
        "block_binding": { "prefix_mismatch_behavior": "drop_block" },
    })
}

/// The first request sends its effort top-level; a later change keeps
/// the top-level effort byte-stable and goes as a control before the turn's
/// user message, so the earlier request's messages stay a prefix.
#[tokio::test]
async fn keeps_the_first_effort_top_level_and_sends_a_change_as_a_control() {
    let model = managed_model("anthropic");
    let first = capture(
        &model,
        &json!({ "messages": [user("one", 1)] }),
        Some("low"),
    )
    .await;
    let second = capture(
        &model,
        &json!({ "messages": [user("one", 1), assistant(&model, Some("low")), user("two", 2)] }),
        Some("high"),
    )
    .await;

    assert_eq!(
        first.payload["messages"],
        json!([{ "role": "user", "content": "one" }])
    );
    assert_eq!(
        first.payload.get("output_config"),
        Some(&json!({ "effort": "low" }))
    );
    assert_eq!(first.payload.get("thinking"), Some(&bound_adaptive()));
    assert_eq!(
        first.message.provider_thinking_level.as_deref(),
        Some("low")
    );
    let first_messages = first.payload["messages"].as_array().expect("messages");
    let second_messages = second.payload["messages"].as_array().expect("messages");
    assert_eq!(
        &second_messages[..first_messages.len()],
        first_messages.as_slice()
    );
    assert_eq!(second_messages.len(), 4, "{second_messages:?}");
    assert_eq!(second_messages[2], control("high"));
    assert_eq!(second_messages[3]["content"], "two");
    assert_eq!(
        second.payload.get("output_config"),
        Some(&json!({ "effort": "low" }))
    );
    assert_eq!(second.payload.get("thinking"), Some(&bound_adaptive()));
    assert_eq!(
        second.message.provider_thinking_level.as_deref(),
        Some("high")
    );
}

/// Each recorded change replays before the reply of the request that made
/// it; an unchanged effort sends no control.
#[tokio::test]
async fn replays_recorded_changes_and_skips_unchanged_efforts() {
    let model = managed_model("anthropic");
    let Captured { payload, message } = capture(
        &model,
        &json!({ "messages": [
            user("one", 1), assistant(&model, Some("low")),
            user("two", 2), assistant(&model, Some("low")),
            user("three", 3), assistant(&model, Some("max")),
            user("four", 4),
        ] }),
        Some("max"),
    )
    .await;
    let roles: Vec<JsonValue> = payload["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .map(|message| match message["role"].as_str() {
            Some("system") => message["output_config"]["effort"].clone(),
            _ => message["role"].clone(),
        })
        .collect();
    assert_eq!(
        roles,
        json!([
            "user",
            "assistant",
            "user",
            "assistant",
            "max",
            "user",
            "assistant",
            "user"
        ])
        .as_array()
        .expect("array")
        .clone()
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "low" }))
    );
    assert_eq!(message.provider_thinking_level.as_deref(), Some("max"));
}

async fn sends_the_requested_effort_top_level(effort: &str) {
    let model = managed_model("anthropic");
    let Captured { payload, message } = capture(
        &model,
        &json!({ "messages": [user("one", 1)] }),
        Some(effort),
    )
    .await;
    assert_eq!(effort_messages(&payload), Vec::<JsonValue>::new());
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": effort }))
    );
    assert_eq!(message.provider_thinking_level.as_deref(), Some(effort));
}

#[tokio::test]
async fn sends_the_requested_effort_top_level_low() {
    sends_the_requested_effort_top_level("low").await;
}

#[tokio::test]
async fn sends_the_requested_effort_top_level_medium() {
    sends_the_requested_effort_top_level("medium").await;
}

#[tokio::test]
async fn sends_the_requested_effort_top_level_high() {
    sends_the_requested_effort_top_level("high").await;
}

#[tokio::test]
async fn sends_the_requested_effort_top_level_xhigh() {
    sends_the_requested_effort_top_level("xhigh").await;
}

#[tokio::test]
async fn sends_the_requested_effort_top_level_max() {
    sends_the_requested_effort_top_level("max").await;
}

/// No effort named leaves the API's per-model default; the reply
/// records that none is in force.
#[tokio::test]
async fn an_omitted_effort_sends_none_and_still_enables_drop_block() {
    let Captured { payload, message } = capture(
        &managed_model("anthropic"),
        &json!({ "messages": [user("one", 1)] }),
        None,
    )
    .await;
    assert_eq!(effort_messages(&payload), Vec::<JsonValue>::new());
    assert_eq!(payload.get("output_config"), None);
    assert_eq!(
        payload["thinking"]["block_binding"]["prefix_mismatch_behavior"],
        "drop_block"
    );
    assert_eq!(message.provider_thinking_level.as_deref(), Some("none"));
}

#[tokio::test]
async fn does_not_invent_markers_for_legacy_or_other_provider_assistants() {
    let model = managed_model("anthropic");
    let legacy = assistant(&model, None);
    let mut other_provider = assistant(&model, Some("low"));
    other_provider["provider"] = json!("other-provider");
    let Captured { payload, .. } = capture(
        &model,
        &json!({ "messages": [user("one", 1), legacy, user("two", 2), other_provider, user("three", 3)] }),
        Some("medium"),
    )
    .await;
    assert_eq!(effort_messages(&payload), Vec::<JsonValue>::new());
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "medium" }))
    );
}

/// Haiku 5.5 turns thinking off
/// with `disabled`, no effort, no control.
#[tokio::test]
async fn off_sends_disabled_thinking_on_a_model_that_accepts_it() {
    let model = managed_model_with("anthropic", &json!({ "disabledThinking": "disabled" }));
    let Captured { payload, message } = capture_thinking(
        &model,
        &json!({ "messages": [user("one", 1)] }),
        false,
        None,
    )
    .await;
    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "disabled" }))
    );
    assert_eq!(payload.get("output_config"), None);
    assert_eq!(effort_messages(&payload), Vec::<JsonValue>::new());
    assert_eq!(message.provider_thinking_level.as_deref(), Some("none"));

    // One effort in force (no control): still `disabled`, the top-level
    // effort kept.
    let Captured { payload, .. } = capture_thinking(
        &model,
        &json!({ "messages": [
            user("one", 1), assistant(&model, Some("medium")),
            user("two", 2), assistant(&model, Some("medium")),
            user("three", 3),
        ] }),
        false,
        None,
    )
    .await;
    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "disabled" }))
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "medium" }))
    );
    assert_eq!(effort_messages(&payload), Vec::<JsonValue>::new());
}

/// Thinking `disabled` is a 400 above `high` and with a per-message control in
/// the history; off falls back to lowest-effort adaptive.
#[tokio::test]
async fn off_falls_back_to_the_lowest_adaptive_effort_when_the_history_forbids_disabled() {
    let model = managed_model_with("anthropic", &json!({ "disabledThinking": "disabled" }));
    let Captured { payload, message } = capture_thinking(
        &model,
        &json!({ "messages": [user("one", 1), assistant(&model, Some("xhigh")), user("two", 2)] }),
        false,
        None,
    )
    .await;
    assert_eq!(
        payload.get("thinking"),
        Some(
            &json!({ "type": "adaptive", "block_binding": { "prefix_mismatch_behavior": "drop_block" } })
        )
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "xhigh" }))
    );
    assert_eq!(effort_messages(&payload), vec![control("low")]);
    assert_eq!(message.provider_thinking_level.as_deref(), Some("low"));

    let Captured { payload, .. } = capture_thinking(
        &model,
        &json!({ "messages": [
            user("one", 1), assistant(&model, Some("medium")),
            user("two", 2), assistant(&model, Some("high")),
            user("three", 3),
        ] }),
        false,
        None,
    )
    .await;
    assert_eq!(payload["thinking"]["type"], "adaptive");
    assert_eq!(
        effort_messages(&payload),
        vec![control("high"), control("low")]
    );
}

/// An adaptive-only model (Fable, Opus 5.x) cannot turn thinking off;
/// off pins the lowest effort.
#[tokio::test]
async fn off_pins_the_lowest_effort_on_an_adaptive_only_model() {
    let Captured { payload, message } = capture_thinking(
        &managed_model("anthropic"),
        &json!({ "messages": [user("one", 1)] }),
        false,
        None,
    )
    .await;
    assert_eq!(
        payload.get("thinking"),
        Some(
            &json!({ "type": "adaptive", "block_binding": { "prefix_mismatch_behavior": "drop_block" } })
        )
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "low" }))
    );
    assert_eq!(message.provider_thinking_level.as_deref(), Some("low"));

    // Without the prefix binding (Opus 5): no `thinking` field at all.
    let unbound = managed_model_with(
        "anthropic",
        &json!({ "supportsThinkingBindingControls": false }),
    );
    let Captured { payload, .. } = capture_thinking(
        &unbound,
        &json!({ "messages": [user("one", 1)] }),
        false,
        None,
    )
    .await;
    assert_eq!(payload.get("thinking"), None);
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "low" }))
    );
    let Captured { payload, .. } = capture(
        &unbound,
        &json!({ "messages": [user("one", 1)] }),
        Some("medium"),
    )
    .await;
    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "adaptive", "display": "summarized" }))
    );
}

/// Sonnet 5.5 turns thinking off with `between_tools`, except while
/// an `xhigh`/`max` effort is in force (a 400 there).
#[tokio::test]
async fn off_sends_between_tools_on_a_model_that_has_it() {
    let model = managed_model_with("anthropic", &json!({ "disabledThinking": "between-tools" }));
    let Captured { payload, .. } = capture_thinking(
        &model,
        &json!({ "messages": [user("one", 1)] }),
        false,
        None,
    )
    .await;
    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "between_tools" }))
    );
    assert_eq!(payload.get("output_config"), None);
    let Captured { payload, .. } = capture_thinking(
        &model,
        &json!({ "messages": [user("one", 1), assistant(&model, Some("max")), user("two", 2)] }),
        false,
        None,
    )
    .await;
    assert_eq!(payload.get("thinking"), None);
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "max" }))
    );
}

/// A change in a tool loop goes at the
/// end, after the tool results, never between `tool_use` and `tool_result`.
#[tokio::test]
async fn a_change_in_a_tool_loop_goes_after_the_tool_results() {
    let model = managed_model("anthropic");
    let mut call = assistant(&model, Some("low"));
    call["content"] = json!([
        { "type": "toolCall", "id": "call_1", "name": "shot", "arguments": {} },
    ]);
    call["stopReason"] = json!("toolUse");
    let result = json!({
        "role": "toolResult",
        "toolCallId": "call_1",
        "toolName": "shot",
        "content": [{ "type": "text", "text": "done" }],
        "isError": false,
        "timestamp": 3,
    });
    let Captured { payload, .. } = capture(
        &model,
        &json!({ "messages": [user("one", 1), call, result] }),
        Some("high"),
    )
    .await;
    let messages = payload["messages"].as_array().expect("messages");
    assert_eq!(messages.len(), 4, "{messages:?}");
    assert_eq!(messages[2]["content"][0]["type"], "tool_result");
    assert_eq!(messages[3], control("high"));
}

/// The built-in models' first request at each `--thinking` level (against
/// a stub provider): Haiku 5.5 turns
/// thinking off with `disabled`, Fable 5.1 pins `low`, Sonnet 5.5 sends
/// `between_tools`, Opus 5 omits `thinking`; every other level sends its
/// own effort top-level. Regression: every level sent effort `high`
/// top-level with the level only in a trailing per-message control, and off
/// sent adaptive thinking at effort low.
#[tokio::test]
async fn builtin_models_send_the_requested_effort_like_omp() {
    let bound = |display: bool| {
        let mut thinking = json!({
            "type": "adaptive",
            "block_binding": { "prefix_mismatch_behavior": "drop_block" },
        });
        if display {
            thinking["display"] = json!("summarized");
        }
        thinking
    };
    let off_cases = [
        (
            "claude-haiku-5-5",
            Some(json!({ "type": "disabled" })),
            None,
        ),
        ("claude-fable-5-1", Some(bound(false)), Some("low")),
        (
            "claude-sonnet-5-5",
            Some(json!({ "type": "between_tools" })),
            None,
        ),
        ("claude-opus-5", None, Some("low")),
        ("claude-opus-5-5", Some(bound(false)), Some("low")),
    ];
    for (id, thinking, effort) in off_cases {
        let model = builtin_model("anthropic", id, &json!({}));
        let Captured { payload, .. } = capture_thinking(
            &model,
            &json!({ "messages": [user("one", 1)] }),
            false,
            None,
        )
        .await;
        assert_eq!(payload.get("thinking"), thinking.as_ref(), "{id} off");
        assert_eq!(
            payload.get("output_config"),
            effort.map(|effort| json!({ "effort": effort })).as_ref(),
            "{id} off"
        );
        assert_eq!(
            effort_messages(&payload),
            Vec::<JsonValue>::new(),
            "{id} off"
        );
    }
    for id in [
        "claude-haiku-5-5",
        "claude-fable-5-1",
        "claude-sonnet-5-5",
        "claude-opus-5-5",
    ] {
        let model = builtin_model("anthropic", id, &json!({}));
        for effort in ["low", "medium", "high", "xhigh", "max"] {
            let Captured { payload, .. } = capture(
                &model,
                &json!({ "messages": [user("one", 1)] }),
                Some(effort),
            )
            .await;
            assert_eq!(payload.get("thinking"), Some(&bound(true)), "{id} {effort}");
            assert_eq!(
                payload.get("output_config"),
                Some(&json!({ "effort": effort })),
                "{id} {effort}"
            );
            assert_eq!(
                effort_messages(&payload),
                Vec::<JsonValue>::new(),
                "{id} {effort}"
            );
        }
    }
}

#[tokio::test]
async fn leaves_unsupported_models_on_top_level_effort() {
    let mut value = serde_json::to_value(managed_model("anthropic")).expect("model json");
    value["compat"] = json!({ "forceAdaptiveThinking": true });
    let model: Model = serde_json::from_value(value).expect("model");
    let Captured { payload, message } = capture(
        &model,
        &json!({ "messages": [user("one", 1)] }),
        Some("low"),
    )
    .await;
    assert_eq!(
        payload["messages"],
        json!([{ "role": "user", "content": "one" }])
    );
    assert_eq!(
        payload.get("output_config"),
        Some(&json!({ "effort": "low" }))
    );
    assert_eq!(
        payload.get("thinking"),
        Some(&json!({ "type": "adaptive", "display": "summarized" }))
    );
    assert_eq!(message.provider_thinking_level, None);
}

#[tokio::test]
async fn sends_the_effort_and_binding_beta_headers() {
    let events = [
        json!({
            "type": "message_start",
            "message": {
                "id": "msg_test",
                "model": "claude-fable-5-1",
                "usage": { "input_tokens": 1, "output_tokens": 0 },
            },
        }),
        json!({
            "type": "message_delta",
            "delta": { "stop_reason": "end_turn" },
            "usage": { "input_tokens": 1, "output_tokens": 1 },
        }),
        json!({ "type": "message_stop" }),
    ];
    let mut body = String::new();
    for event in &events {
        let name = event["type"].as_str().unwrap_or("");
        write!(body, "event: {name}\ndata: {event}\n\n").expect("write to String");
    }
    let (fetch, captured) = mock_fetch(MockResponse::sse(body));
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test-key".into());
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.fetch = Some(fetch);
    let result = stream(
        &managed_model("anthropic"),
        &context(&json!({ "messages": [user("one", 1)] })),
        options,
    )
    .result()
    .await;

    assert_eq!(
        result.stop_reason,
        StopReason::Stop,
        "{:?}",
        result.error_message
    );
    let requests = anthropic_support::requests(&captured);
    let beta_header = requests
        .last()
        .and_then(|request| request.header("anthropic-beta"))
        .unwrap_or_default();
    assert!(
        beta_header.contains("mid-conversation-output-config-2026-07-01"),
        "{beta_header}"
    );
    assert!(
        beta_header.contains("thinking-binding-controls-2026-08-01"),
        "{beta_header}"
    );
}

fn as_json(model: &Model) -> JsonValue {
    serde_json::to_value(model).expect("model json")
}

#[test]
fn generates_exact_model_and_transport_gates() {
    let direct = as_json(&builtin_model("anthropic", "claude-fable-5-1", &json!({})));
    let open_router = as_json(&builtin_model(
        "openrouter",
        "anthropic/claude-fable-5.1",
        &json!({}),
    ));
    let unsupported = as_json(&builtin_model("anthropic", "claude-opus-4-8", &json!({})));
    assert_eq!(direct["compat"]["supportsMidConvoEffort"], true);
    assert_eq!(
        direct["thinkingLevelMap"].get("off"),
        Some(&JsonValue::Null)
    );
    assert_eq!(open_router["api"], "anthropic-messages");
    assert_eq!(open_router["baseUrl"], "https://openrouter.ai/api");
    assert_eq!(open_router["compat"]["supportsMidConvoEffort"], true);
    assert_eq!(unsupported["compat"].get("supportsMidConvoEffort"), None);
    // OpenRouter rejects configuration_update on Opus 5 but accepts it on Fable 5.1.
    assert_eq!(
        as_json(&builtin_model(
            "openrouter",
            "anthropic/claude-opus-5",
            &json!({})
        ))["compat"]
            .get("supportsMidConvoEffort"),
        None
    );
    assert_eq!(
        as_json(&builtin_model("anthropic", "claude-opus-5", &json!({})))["compat"]
            .get("allowedFallbackModels"),
        None
    );
}
