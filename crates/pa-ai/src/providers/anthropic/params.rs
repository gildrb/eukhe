//! Anthropic Messages request params assembly.
//! Section of the port of `packages/ai/src/providers/anthropic.ts`.

use serde_json::{json, Map, Value};

use crate::providers::anthropic::convert::{convert_messages, convert_tools};
use crate::providers::anthropic::{
    get_anthropic_compat, is_always_on_adaptive_thinking_model, supports_adaptive_thinking,
    AnthropicOptions, AnthropicThinkingDisplay, CacheControl,
};
use crate::providers::cache_breakpoints::CacheMarkBudget;
use crate::types::{Context, Model};
use crate::utils_inner::sanitize_unicode::sanitize_surrogates;

// Long by design (a 1:1 port of the upstream provider shape); refactoring is out of scope for the zero-behavior pedantic sweep.
#[allow(clippy::too_many_lines)]
pub(crate) fn build_params(
    model: &Model,
    context: &Context,
    is_oauth_token: bool,
    options: Option<&AnthropicOptions>,
    cache_control: Option<&CacheControl>,
) -> Value {
    let base = options
        .map(|options| options.base.clone())
        .unwrap_or_default();
    let messages = convert_messages(context, model, is_oauth_token, cache_control);
    // The message marks (the marked blocks and the end mark) are fixed. The
    // optional marks take the slots left, in priority order: system prompt,
    // last tool, OAuth identity block; only a mark the request carries spends
    // a slot. Without a marked block all of them fit, as before.
    let mut budget = CacheMarkBudget::after_message_marks(&messages, "cache_control");
    let has_tools = context
        .tools
        .as_ref()
        .is_some_and(|tools| !tools.is_empty());
    let system_mark = context.system_prompt.is_some() && budget.take();
    let tools_mark = has_tools && budget.take();
    let identity_mark = is_oauth_token && budget.take();
    let mut params = Map::new();
    params.insert("model".into(), json!(model.id));
    params.insert("messages".into(), json!(messages));
    params.insert(
        "max_tokens".into(),
        json!(base.max_tokens.unwrap_or(model.max_tokens / 3)),
    );
    params.insert("stream".into(), json!(true));

    // For OAuth tokens, we MUST include Claude Code identity.
    if is_oauth_token {
        let mut system = vec![json!({
            "type": "text",
            "text": "You are Claude Code, Anthropic's official CLI for Claude.",
        })];
        if let Some(cache_control) = cache_control.filter(|_| identity_mark) {
            system[0]
                .as_object_mut()
                .expect("system entry is an object")
                .insert("cache_control".into(), cache_control.to_json());
        }
        if let Some(system_prompt) = &context.system_prompt {
            let mut entry = json!({
                "type": "text",
                "text": sanitize_surrogates(system_prompt),
            });
            if let Some(cache_control) = cache_control.filter(|_| system_mark) {
                entry
                    .as_object_mut()
                    .expect("system entry is an object")
                    .insert("cache_control".into(), cache_control.to_json());
            }
            system.push(entry);
        }
        params.insert("system".into(), json!(system));
    } else if let Some(system_prompt) = &context.system_prompt {
        let mut entry = json!({
            "type": "text",
            "text": sanitize_surrogates(system_prompt),
        });
        if let Some(cache_control) = cache_control.filter(|_| system_mark) {
            entry
                .as_object_mut()
                .expect("system entry is an object")
                .insert("cache_control".into(), cache_control.to_json());
        }
        params.insert("system".into(), json!([entry]));
    }

    // Temperature is incompatible with extended thinking (adaptive or
    // budget-based), and always-on models reject sampling params outright.
    if let Some(temperature) = base.temperature {
        if options.map(|options| options.thinking_enabled) != Some(Some(true))
            && !is_always_on_adaptive_thinking_model(&model.id)
        {
            params.insert("temperature".into(), json!(temperature));
        }
    }

    if let Some(tools) = &context.tools {
        if !tools.is_empty() {
            params.insert(
                "tools".into(),
                json!(convert_tools(
                    tools,
                    is_oauth_token,
                    get_anthropic_compat(model).supports_eager_tool_input_streaming,
                    cache_control.filter(|_| tools_mark),
                )),
            );
        }
    }

    // Configure thinking mode: adaptive, budget-based, or explicitly disabled.
    if model.reasoning {
        if options.map(|options| options.thinking_enabled) == Some(Some(true)) {
            let display = options
                .and_then(|options| options.thinking_display)
                .unwrap_or(AnthropicThinkingDisplay::Summarized);
            if supports_adaptive_thinking(&model.id) {
                params.insert(
                    "thinking".into(),
                    json!({ "type": "adaptive", "display": display.as_str() }),
                );
                if let Some(effort) = options.and_then(|options| options.effort) {
                    params.insert("output_config".into(), json!({ "effort": effort.as_str() }));
                }
            } else {
                params.insert(
                    "thinking".into(),
                    json!({
                        "type": "enabled",
                        "budget_tokens": options.and_then(|options| options.thinking_budget_tokens).unwrap_or(1024),
                        "display": display.as_str(),
                    }),
                );
            }
        } else if options.map(|options| options.thinking_enabled) == Some(Some(false))
            && !is_always_on_adaptive_thinking_model(&model.id)
        {
            params.insert("thinking".into(), json!({ "type": "disabled" }));
        }
    }

    if let Some(metadata) = &base.metadata {
        if let Some(user_id) = metadata.get("user_id").and_then(|value| value.as_str()) {
            params.insert("metadata".into(), json!({ "user_id": user_id }));
        }
    }

    if let Some(tool_choice) = options.and_then(|options| options.tool_choice.as_ref()) {
        params.insert("tool_choice".into(), tool_choice.to_json());
    }

    Value::Object(params)
}

#[cfg(test)]
mod tests {
    use serde_json::{json, Value};

    use super::build_params;
    use crate::event_stream::AssistantMessageEventExt;
    use crate::providers::anthropic::{stream_anthropic, AnthropicOptions, CacheControl};
    use crate::types::{Context, Model, StreamOptions};

    fn model() -> Model {
        serde_json::from_value(json!({
            "id": "claude-sonnet-4-6", "name": "Claude Sonnet 4.6",
            "api": "anthropic-messages", "provider": "anthropic",
            "baseUrl": "https://api.anthropic.com", "reasoning": false, "input": ["text"],
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
            "contextWindow": 200_000, "maxTokens": 64_000
        }))
        .expect("model json")
    }

    /// An assistant row of the test model (the usage is irrelevant here).
    fn assistant(content: &Value, stop_reason: &str, timestamp: u64) -> Value {
        json!({
            "role": "assistant", "content": content,
            "api": "anthropic-messages", "provider": "anthropic", "model": "claude-sonnet-4-6",
            "usage": {
                "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 }
            },
            "stopReason": stop_reason, "timestamp": timestamp
        })
    }

    fn tools() -> Value {
        json!([
            {
                "name": "read", "description": "Read a file",
                "parameters": {
                    "type": "object",
                    "properties": { "path": { "type": "string" } },
                    "required": ["path"]
                }
            },
            {
                "name": "bash", "description": "Run a command",
                "parameters": {
                    "type": "object",
                    "properties": { "command": { "type": "string" } },
                    "required": ["command"]
                }
            }
        ])
    }

    fn text(text: &str) -> Value {
        json!({ "type": "text", "text": text })
    }

    /// A text block that carries a cache breakpoint (a chat-memory view piece).
    fn marked(text: &str) -> Value {
        json!({ "type": "text", "text": text, "cacheBreakpoint": "ephemeral" })
    }

    /// A system prompt, two tools, and one user message with `blocks`.
    fn context(blocks: &[Value]) -> Context {
        serde_json::from_value(json!({
            "systemPrompt": "You are a test.",
            "messages": [{ "role": "user", "content": blocks, "timestamp": 1 }],
            "tools": tools()
        }))
        .expect("context json")
    }

    /// Three view pieces, the first `marked_pieces` of them marked, then the
    /// new question (the end-mark block).
    fn view_context(marked_pieces: usize) -> Context {
        let mut blocks: Vec<Value> = (0..3)
            .map(|index| {
                let piece = format!("view piece {index}");
                if index < marked_pieces {
                    marked(&piece)
                } else {
                    text(&piece)
                }
            })
            .collect();
        blocks.push(text("question"));
        context(&blocks)
    }

    /// Where the request carries `cache_control`: tools and system entries
    /// by index, then message content blocks by message and block index.
    fn cache_marks(params: &Value) -> Vec<String> {
        let mut marks = Vec::new();
        for key in ["tools", "system"] {
            for (index, entry) in params[key].as_array().into_iter().flatten().enumerate() {
                if entry.get("cache_control").is_some() {
                    marks.push(format!("{key}[{index}]"));
                }
            }
        }
        let messages = params["messages"].as_array().into_iter().flatten();
        for (message_index, message) in messages.enumerate() {
            let blocks = message["content"].as_array().into_iter().flatten();
            for (block_index, block) in blocks.enumerate() {
                if block.get("cache_control").is_some() {
                    marks.push(format!("messages[{message_index}][{block_index}]"));
                }
            }
        }
        marks
    }

    /// How a request authenticates: OAuth adds the Claude Code identity block
    /// (and its mark) to the system prompt.
    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Auth {
        ApiKey,
        OAuth,
    }

    /// The marked blocks and the end mark always stay; the optional marks
    /// take the slots left within four, in priority order: system prompt,
    /// last tool, OAuth identity block. Without a marked block the request
    /// keeps today's marks.
    #[test]
    fn marked_blocks_take_the_optional_mark_slots_in_priority_order() {
        let cache_control = CacheControl { ttl: None };
        let cases: [(Auth, usize, &[&str]); 8] = [
            (
                Auth::ApiKey,
                0,
                &["tools[1]", "system[0]", "messages[0][3]"],
            ),
            (
                Auth::ApiKey,
                1,
                &["tools[1]", "system[0]", "messages[0][0]", "messages[0][3]"],
            ),
            (
                Auth::ApiKey,
                2,
                &[
                    "system[0]",
                    "messages[0][0]",
                    "messages[0][1]",
                    "messages[0][3]",
                ],
            ),
            (
                Auth::ApiKey,
                3,
                &[
                    "messages[0][0]",
                    "messages[0][1]",
                    "messages[0][2]",
                    "messages[0][3]",
                ],
            ),
            (
                Auth::OAuth,
                0,
                &["tools[1]", "system[0]", "system[1]", "messages[0][3]"],
            ),
            (
                Auth::OAuth,
                1,
                &["tools[1]", "system[1]", "messages[0][0]", "messages[0][3]"],
            ),
            (
                Auth::OAuth,
                2,
                &[
                    "system[1]",
                    "messages[0][0]",
                    "messages[0][1]",
                    "messages[0][3]",
                ],
            ),
            (
                Auth::OAuth,
                3,
                &[
                    "messages[0][0]",
                    "messages[0][1]",
                    "messages[0][2]",
                    "messages[0][3]",
                ],
            ),
        ];
        let actual: Vec<(Auth, usize, Vec<String>)> = cases
            .iter()
            .map(|&(auth, marked_pieces, _)| {
                let is_oauth_token = match auth {
                    Auth::ApiKey => false,
                    Auth::OAuth => true,
                };
                let params = build_params(
                    &model(),
                    &view_context(marked_pieces),
                    is_oauth_token,
                    None,
                    Some(&cache_control),
                );
                (auth, marked_pieces, cache_marks(&params))
            })
            .collect();
        let expected: Vec<(Auth, usize, Vec<String>)> = cases
            .iter()
            .map(|&(auth, marked_pieces, marks)| {
                let marks = marks.iter().map(ToString::to_string).collect();
                (auth, marked_pieces, marks)
            })
            .collect();
        assert_eq!(actual, expected);
    }

    /// A marked block that ends the request is the end mark too: it counts
    /// once, so three marked blocks still leave the system prompt a slot.
    #[test]
    fn a_marked_last_block_counts_once() {
        let context = context(&[marked("piece 0"), marked("piece 1"), marked("piece 2")]);
        let params = build_params(
            &model(),
            &context,
            /*is_oauth_token*/ false,
            None,
            Some(&CacheControl { ttl: None }),
        );
        assert_eq!(
            cache_marks(&params),
            [
                "system[0]",
                "messages[0][0]",
                "messages[0][1]",
                "messages[0][2]"
            ]
        );
    }

    /// A marked block carries the request's `cache_control`, TTL included.
    #[test]
    fn a_marked_block_carries_the_request_cache_control() {
        let params = build_params(
            &model(),
            &view_context(1),
            /*is_oauth_token*/ false,
            None,
            Some(&CacheControl { ttl: Some("1h") }),
        );
        assert_eq!(
            params["messages"][0]["content"][0],
            json!({
                "type": "text",
                "text": "view piece 0",
                "cache_control": { "type": "ephemeral", "ttl": "1h" }
            })
        );
    }

    /// Without a cache retention the request carries no mark at all, the
    /// marked blocks included.
    #[test]
    fn no_cache_control_means_no_marks() {
        let params = build_params(
            &model(),
            &view_context(3),
            /*is_oauth_token*/ true,
            None,
            None,
        );
        assert_eq!(cache_marks(&params), Vec::<String>::new());
    }

    /// A fourth marked block is a caller bug: the request fails before it is
    /// built or sent, instead of dropping a mark.
    #[tokio::test]
    async fn a_fourth_marked_block_fails_the_request() {
        let context = context(&[
            marked("piece 0"),
            marked("piece 1"),
            marked("piece 2"),
            marked("question"),
        ]);
        // A closed local port: a request that slips through fails to connect.
        let model = Model {
            base_url: "http://127.0.0.1:9".into(),
            ..model()
        };
        let options = AnthropicOptions::from_base(StreamOptions {
            api_key: Some("sk-ant-api-test".into()),
            ..Default::default()
        });
        let events = stream_anthropic(&model, &context, Some(&options))
            .collect()
            .await;
        let outcome: Vec<(&str, Option<&str>)> = events
            .iter()
            .map(|event| (event.event_type(), event.partial().error_message.as_deref()))
            .collect();
        assert_eq!(
            outcome,
            [(
                "error",
                Some(
                    "Too many cache breakpoints: the request marks 4 blocks, at most 3 are allowed"
                )
            )]
        );
    }

    /// A conversation with no marked block: a question, a tool round trip,
    /// and a last user message of two text blocks.
    fn unmarked_history() -> Context {
        serde_json::from_value(json!({
            "systemPrompt": "You are a test.",
            "messages": [
                { "role": "user", "content": "first question", "timestamp": 1 },
                assistant(
                    &json!([
                        { "type": "text", "text": "Let me look." },
                        { "type": "toolCall", "id": "call_1", "name": "read",
                          "arguments": { "path": "a.txt" } }
                    ]),
                    "toolUse",
                    2,
                ),
                {
                    "role": "toolResult", "toolCallId": "call_1", "toolName": "read",
                    "content": [{ "type": "text", "text": "file body" }],
                    "isError": false, "timestamp": 3
                },
                assistant(&json!([{ "type": "text", "text": "Done." }]), "stop", 4),
                {
                    "role": "user",
                    "content": [
                        { "type": "text", "text": "view piece" },
                        { "type": "text", "text": "second question" }
                    ],
                    "timestamp": 5
                }
            ],
            "tools": tools()
        }))
        .expect("context json")
    }

    /// The serialized request for [`unmarked_history`] with today's marks:
    /// the last tool and the last user block, plus the given `system` array.
    /// `read` and `bash` are the tool names as sent (OAuth sends the Claude
    /// Code names).
    fn unmarked_request(read: &str, bash: &str, system: &Value) -> String {
        json!({
            "model": "claude-sonnet-4-6",
            "messages": [
                { "role": "user", "content": "first question" },
                {
                    "role": "assistant",
                    "content": [
                        { "type": "text", "text": "Let me look." },
                        { "type": "tool_use", "id": "call_1", "name": read,
                          "input": { "path": "a.txt" } }
                    ]
                },
                {
                    "role": "user",
                    "content": [{
                        "type": "tool_result", "tool_use_id": "call_1",
                        "content": "file body", "is_error": false
                    }]
                },
                { "role": "assistant", "content": [{ "type": "text", "text": "Done." }] },
                {
                    "role": "user",
                    "content": [
                        { "type": "text", "text": "view piece" },
                        { "type": "text", "text": "second question",
                          "cache_control": { "type": "ephemeral" } }
                    ]
                }
            ],
            "max_tokens": 21_333,
            "stream": true,
            "system": system,
            "tools": [
                {
                    "name": read, "description": "Read a file", "eager_input_streaming": true,
                    "input_schema": {
                        "type": "object",
                        "properties": { "path": { "type": "string" } },
                        "required": ["path"]
                    }
                },
                {
                    "name": bash, "description": "Run a command", "eager_input_streaming": true,
                    "input_schema": {
                        "type": "object",
                        "properties": { "command": { "type": "string" } },
                        "required": ["command"]
                    },
                    "cache_control": { "type": "ephemeral" }
                }
            ]
        })
        .to_string()
    }

    /// An API-key request with no marked block keeps today's marks byte for
    /// byte: the last tool, the system prompt, and the last user block.
    #[test]
    fn unmarked_api_key_requests_keep_the_existing_marks_byte_for_byte() {
        let params = build_params(
            &model(),
            &unmarked_history(),
            /*is_oauth_token*/ false,
            None,
            Some(&CacheControl { ttl: None }),
        );
        let system = json!([{
            "type": "text", "text": "You are a test.",
            "cache_control": { "type": "ephemeral" }
        }]);
        assert_eq!(
            params.to_string(),
            unmarked_request("read", "bash", &system)
        );
    }

    /// An OAuth request with no marked block keeps today's four marks byte
    /// for byte: the last tool, both system entries, and the last user block.
    #[test]
    fn unmarked_oauth_requests_keep_the_existing_marks_byte_for_byte() {
        let params = build_params(
            &model(),
            &unmarked_history(),
            /*is_oauth_token*/ true,
            None,
            Some(&CacheControl { ttl: None }),
        );
        let system = json!([
            {
                "type": "text",
                "text": "You are Claude Code, Anthropic's official CLI for Claude.",
                "cache_control": { "type": "ephemeral" }
            },
            {
                "type": "text", "text": "You are a test.",
                "cache_control": { "type": "ephemeral" }
            }
        ]);
        assert_eq!(
            params.to_string(),
            unmarked_request("Read", "Bash", &system)
        );
    }
}
