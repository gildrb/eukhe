//! Request building: body, headers, account id, endpoint URLs, and the
//! service-tier pricing hooks. Section of the port of
//! `api/openai-codex-responses.ts`.

use base64::alphabet;
use base64::engine::general_purpose::{GeneralPurpose, GeneralPurposeConfig};
use base64::engine::DecodePaddingMode;
use base64::Engine as _;
use eukhe_types::pi_ai::IndexMap;
use eukhe_types::pi_ai::{
    JsonObject, JsonValue, Model, ModelThinkingLevel, ProviderHeaders, TranscriptContext, Usage,
};
use reqwest::header::{HeaderMap, HeaderName, HeaderValue};
use serde_json::json;

use crate::api::openai_responses_shared::{
    convert_responses_messages, convert_responses_tools, ConvertResponsesMessagesOptions,
    ConvertResponsesToolsOptions,
};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::js::js_to_string;
use crate::utils::pi_user_agent::get_pi_user_agent;
use crate::utils::text::get_system_message_text;
use crate::utils::transcript::{get_initial_system_message, resolve_transcript_tools};

use super::{responses_compat, CodexOptions, CODEX_TOOL_CALL_PROVIDERS};

const DEFAULT_CODEX_BASE_URL: &str = "https://chatgpt.com/backend-api";
const JWT_CLAIM_PATH: &str = "https://api.openai.com/auth";
/// The WebSocket beta header value.
pub(crate) const OPENAI_BETA_RESPONSES_WEBSOCKETS: &str = "responses_websockets=2026-02-06";

/// TS `buildRequestBody`.
#[allow(clippy::too_many_lines)] // One TS function; its field order is the wire order.
pub(crate) fn build_request_body(
    model: &Model,
    context: &TranscriptContext,
    options: &CodexOptions,
    cache_session_id: Option<&str>,
    grammar_tool_input_properties: &IndexMap<String, String>,
) -> Result<JsonValue, Thrown> {
    let compat = responses_compat(model);
    let supports_strict_mode = compat
        .and_then(|compat| compat.supports_strict_mode)
        .unwrap_or(true);
    let supports_openai_grammar_tools = compat
        .and_then(|compat| compat.supports_openai_grammar_tools)
        .unwrap_or(false);
    let supports_additional_tools = compat
        .and_then(|compat| compat.supports_additional_tools)
        .unwrap_or(false);
    let supports_tool_search = compat
        .and_then(|compat| compat.supports_tool_search)
        .unwrap_or(false);
    let transcript_tools = resolve_transcript_tools(
        context.messages(),
        supports_additional_tools || supports_tool_search,
    );
    let tool_options = ConvertResponsesToolsOptions {
        strict: Some(None),
        supports_strict_mode: Some(supports_strict_mode),
        supports_openai_grammar_tools: Some(supports_openai_grammar_tools),
        ..ConvertResponsesToolsOptions::default()
    };
    let messages = convert_responses_messages(
        model,
        context,
        CODEX_TOOL_CALL_PROVIDERS,
        &ConvertResponsesMessagesOptions {
            include_system_prompt: Some(false),
            grammar_tool_input_properties: Some(grammar_tool_input_properties.clone()),
            supports_mid_convo_system_messages: Some(
                compat
                    .and_then(|compat| compat.supports_mid_convo_system_messages)
                    .unwrap_or(false),
            ),
            supports_additional_tools: Some(supports_additional_tools),
            supports_tool_search: Some(supports_tool_search),
            tool_options: Some(tool_options),
            // Like the old eukhe port: the ChatGPT backend's acceptance of
            // `prompt_cache_breakpoint` is unverified, so marks are not sent.
            explicit_cache_breakpoints: false,
        },
    )?;

    let instructions = get_initial_system_message(context.messages())
        .map(get_system_message_text)
        .unwrap_or_default();
    let mut body = JsonObject::new();
    body.insert("model".into(), json!(model.id));
    body.insert("store".into(), json!(false));
    body.insert("stream".into(), json!(true));
    body.insert(
        "instructions".into(),
        json!(if instructions.is_empty() {
            "You are a helpful assistant."
        } else {
            instructions.as_str()
        }),
    );
    body.insert("input".into(), JsonValue::Array(messages));
    body.insert(
        "text".into(),
        json!({ "verbosity": or_default(options.text_verbosity.as_ref(), "low") }),
    );
    body.insert("include".into(), json!(["reasoning.encrypted_content"]));
    if let Some(cache_session_id) = cache_session_id {
        body.insert("prompt_cache_key".into(), json!(cache_session_id));
    }
    body.insert(
        "tool_choice".into(),
        nullish_or(options.tool_choice.as_ref(), json!("auto")),
    );
    body.insert("parallel_tool_calls".into(), json!(true));

    if let Some(temperature) = options.temperature {
        body.insert(
            "temperature".into(),
            crate::utils::js::js_number_value(temperature),
        );
    }

    if let Some(service_tier) = &options.service_tier {
        body.insert("service_tier".into(), service_tier.clone());
    }

    if !transcript_tools.request_tools.is_empty() {
        body.insert(
            "tools".into(),
            JsonValue::Array(convert_responses_tools(
                &transcript_tools.request_tools,
                &tool_options,
            )?),
        );
    }

    let off_mapping = model
        .thinking_level_map
        .as_ref()
        .and_then(|map| map.get(&ModelThinkingLevel::Off));
    if let Some(reasoning_effort) = &options.reasoning_effort {
        let effort: JsonValue = if reasoning_effort.as_str() == Some("none") {
            match off_mapping {
                None => json!("none"),
                Some(mapped) => mapped
                    .as_ref()
                    .map_or(JsonValue::Null, |mapped| json!(mapped)),
            }
        } else {
            // `model.thinkingLevelMap?.[effort] ?? effort`.
            reasoning_effort
                .as_str()
                .and_then(ModelThinkingLevel::parse)
                .and_then(|level| {
                    model
                        .thinking_level_map
                        .as_ref()?
                        .get(&level)
                        .cloned()
                        .flatten()
                })
                .map_or_else(|| reasoning_effort.clone(), JsonValue::String)
        };
        if !effort.is_null() {
            body.insert(
                "reasoning".into(),
                json!({
                    "effort": effort,
                    "summary": nullish_or(options.reasoning_summary.as_ref(), json!("auto")),
                }),
            );
        }
    } else if model.reasoning && !matches!(off_mapping, Some(None)) {
        let effort = off_mapping
            .cloned()
            .flatten()
            .unwrap_or_else(|| "none".to_owned());
        body.insert("reasoning".into(), json!({ "effort": effort }));
    }

    Ok(JsonValue::Object(body))
}

/// `value || fallback` for an option that may be any JSON value.
fn or_default(value: Option<&JsonValue>, fallback: &str) -> JsonValue {
    match value {
        Some(JsonValue::String(text)) if !text.is_empty() => JsonValue::String(text.clone()),
        Some(value @ (JsonValue::Array(_) | JsonValue::Object(_))) => value.clone(),
        Some(JsonValue::Bool(true)) => JsonValue::Bool(true),
        Some(JsonValue::Number(number)) if number.as_f64().is_some_and(|n| n != 0.0) => {
            JsonValue::Number(number.clone())
        }
        Some(_) | None => json!(fallback),
    }
}

/// `value ?? fallback` (JSON `null` counts as nullish).
fn nullish_or(value: Option<&JsonValue>, fallback: JsonValue) -> JsonValue {
    match value {
        Some(value) if !value.is_null() => value.clone(),
        Some(_) | None => fallback,
    }
}

/// TS `getServiceTierCostMultiplier`.
fn get_service_tier_cost_multiplier(model_id: &str, service_tier: Option<&str>) -> f64 {
    match service_tier {
        Some("flex") => 0.5,
        Some("priority") => {
            if model_id == "gpt-5.5" {
                2.5
            } else {
                2.0
            }
        }
        _ => 1.0,
    }
}

/// TS `applyServiceTierPricing`.
pub(crate) fn apply_service_tier_pricing(
    usage: &mut Usage,
    service_tier: Option<&str>,
    model_id: &str,
) {
    let multiplier = get_service_tier_cost_multiplier(model_id, service_tier);
    // The multiplier table is discrete; equality with 1 is the TS no-op check.
    #[allow(clippy::float_cmp)]
    if multiplier == 1.0 {
        return;
    }

    usage.cost.input *= multiplier;
    usage.cost.output *= multiplier;
    usage.cost.cache_read *= multiplier;
    usage.cost.cache_write *= multiplier;
    usage.cost.total =
        usage.cost.input + usage.cost.output + usage.cost.cache_read + usage.cost.cache_write;
}

/// TS `resolveCodexServiceTier`.
pub(crate) fn resolve_codex_service_tier(
    response_service_tier: Option<&str>,
    request_service_tier: Option<&str>,
) -> Option<String> {
    if response_service_tier == Some("default")
        && matches!(request_service_tier, Some("flex" | "priority"))
    {
        return request_service_tier.map(str::to_owned);
    }
    response_service_tier
        .or(request_service_tier)
        .map(str::to_owned)
}

/// TS `resolveCodexUrl`.
pub(crate) fn resolve_codex_url(base_url: Option<&str>) -> String {
    let raw = match base_url {
        Some(base_url) if !base_url.trim().is_empty() => base_url,
        _ => DEFAULT_CODEX_BASE_URL,
    };
    let normalized = raw.trim_end_matches('/');
    if normalized.ends_with("/codex/responses") {
        return normalized.to_owned();
    }
    if normalized.ends_with("/codex") {
        return format!("{normalized}/responses");
    }
    format!("{normalized}/codex/responses")
}

/// TS `resolveCodexWebSocketUrl`.
pub(crate) fn resolve_codex_websocket_url(base_url: Option<&str>) -> Result<String, Thrown> {
    let mut url = url::Url::parse(&resolve_codex_url(base_url)).map_err(|error| {
        ErrorObject::named("TypeError", format!("Invalid URL: {error}")).thrown()
    })?;
    let scheme = match url.scheme() {
        "https" => Some("wss"),
        "http" => Some("ws"),
        _ => None,
    };
    if let Some(scheme) = scheme {
        // `https`↔`wss` and `http`↔`ws` are both special schemes, so the switch succeeds.
        let _ = url.set_scheme(scheme);
    }
    Ok(url.to_string())
}

/// TS `extractAccountId`.
pub(crate) fn extract_account_id(token: &str) -> Result<String, Thrown> {
    let failed = || ErrorObject::new("Failed to extract accountId from token").thrown();
    let parts: Vec<&str> = token.split('.').collect();
    if parts.len() != 3 {
        return Err(failed());
    }
    // `atob`: forgiving base64 (padding optional, ASCII whitespace ignored).
    let engine = GeneralPurpose::new(
        &alphabet::STANDARD,
        GeneralPurposeConfig::new()
            .with_decode_padding_mode(DecodePaddingMode::Indifferent)
            .with_decode_allow_trailing_bits(true),
    );
    let compact: String = parts[1]
        .chars()
        .filter(|c| !matches!(c, '\t' | '\n' | '\u{c}' | '\r' | ' '))
        .collect();
    let bytes = engine.decode(compact).map_err(|_| failed())?;
    // `atob` yields a binary string: one Latin-1 char per byte.
    let text: String = bytes.iter().map(|&byte| char::from(byte)).collect();
    let payload: JsonValue = serde_json::from_str(&text).map_err(|_| failed())?;
    let account_id = payload
        .get(JWT_CLAIM_PATH)
        .and_then(|claim| claim.get("chatgpt_account_id"))
        .filter(|value| match value {
            JsonValue::Null => false,
            JsonValue::Bool(flag) => *flag,
            JsonValue::Number(number) => number.as_f64().is_some_and(|n| n != 0.0),
            JsonValue::String(text) => !text.is_empty(),
            JsonValue::Array(_) | JsonValue::Object(_) => true,
        })
        .ok_or_else(failed)?;
    Ok(js_to_string(account_id))
}

fn header_name(name: &str) -> Result<HeaderName, Thrown> {
    HeaderName::from_bytes(name.as_bytes()).map_err(|_| {
        ErrorObject::named("TypeError", format!("Invalid header name: \"{name}\"")).thrown()
    })
}

fn header_value(value: &str) -> Result<HeaderValue, Thrown> {
    HeaderValue::from_str(value).map_err(|_| {
        ErrorObject::named("TypeError", format!("Invalid header value: \"{value}\"")).thrown()
    })
}

/// `headers.set(name, value)`.
pub(crate) fn set_header(headers: &mut HeaderMap, name: &str, value: &str) -> Result<(), Thrown> {
    headers.insert(header_name(name)?, header_value(value)?);
    Ok(())
}

/// TS `buildBaseCodexHeaders`.
fn build_base_codex_headers(
    init_headers: Option<&IndexMap<String, String>>,
    additional_headers: Option<&ProviderHeaders>,
    account_id: &str,
    token: &str,
) -> Result<HeaderMap, Thrown> {
    let mut headers = HeaderMap::new();
    for (name, value) in init_headers.into_iter().flatten() {
        // `new Headers(init)` appends.
        headers.append(header_name(name)?, header_value(value)?);
    }
    for (name, value) in additional_headers.into_iter().flatten() {
        match value {
            None => {
                headers.remove(header_name(name)?);
            }
            Some(value) => set_header(&mut headers, name, value)?,
        }
    }
    set_header(&mut headers, "Authorization", &format!("Bearer {token}"))?;
    set_header(&mut headers, "chatgpt-account-id", account_id)?;
    set_header(&mut headers, "originator", "pi")?;
    set_header(&mut headers, "User-Agent", get_pi_user_agent())?;
    Ok(headers)
}

/// TS `buildSSEHeaders`.
pub(crate) fn build_sse_headers(
    init_headers: Option<&IndexMap<String, String>>,
    additional_headers: Option<&ProviderHeaders>,
    account_id: &str,
    token: &str,
    session_id: Option<&str>,
) -> Result<HeaderMap, Thrown> {
    let mut headers =
        build_base_codex_headers(init_headers, additional_headers, account_id, token)?;
    set_header(&mut headers, "OpenAI-Beta", "responses=experimental")?;
    set_header(&mut headers, "accept", "text/event-stream")?;
    set_header(&mut headers, "content-type", "application/json")?;

    if let Some(session_id) = session_id.filter(|session_id| !session_id.is_empty()) {
        set_header(&mut headers, "session-id", session_id)?;
        set_header(&mut headers, "x-client-request-id", session_id)?;
    }

    Ok(headers)
}

/// TS `buildWebSocketHeaders`.
pub(crate) fn build_websocket_headers(
    init_headers: Option<&IndexMap<String, String>>,
    additional_headers: Option<&ProviderHeaders>,
    account_id: &str,
    token: &str,
    request_id: &str,
) -> Result<HeaderMap, Thrown> {
    let mut headers =
        build_base_codex_headers(init_headers, additional_headers, account_id, token)?;
    headers.remove("accept");
    headers.remove("content-type");
    headers.remove("openai-beta");
    set_header(
        &mut headers,
        "OpenAI-Beta",
        OPENAI_BETA_RESPONSES_WEBSOCKETS,
    )?;
    set_header(&mut headers, "x-client-request-id", request_id)?;
    set_header(&mut headers, "session-id", request_id)?;
    Ok(headers)
}
