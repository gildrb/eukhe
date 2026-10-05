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
