//! The `azure-openai-responses` wire API. Port of
//! `api/azure-openai-responses.ts`.
//!
//! API-specific options (TS `AzureOpenAIResponsesOptions`) are read from
//! [`ProviderStreamOptions::extra`]: `reasoningEffort`, `reasoningSummary`,
//! `toolChoice`, and the Azure endpoint keys of
//! [`AzureEndpointOptions::from_extra`].

use std::sync::Arc;

use serde_json::json;

use super::azure_openai_config::{
    resolve_azure_config, resolve_deployment_name, AzureEndpointOptions,
};
use super::constrained_sampling::create_grammar_tool_input_properties;
use super::openai_prompt_cache::clamp_openai_prompt_cache_key;
use super::openai_responses::{
    fail_stream, finish_checks, insert_reasoning, insert_reasoning_off, reasoning_effort_of,
    OpenAIResponsesOptions, OPENAI_RESPONSES_MIN_OUTPUT_TOKENS,
};
use super::openai_responses_shared::{
    apply_reasoning_context, convert_responses_messages, convert_responses_tools,
    process_responses_stream, ConvertResponsesMessagesOptions, ConvertResponsesToolsOptions,
    GrammarToolInputProperties, OpenAIResponsesStreamOptions,
};
use super::openai_sdk::{OpenAiClient, OpenAiClientConfig, OpenAiClientKind, OpenAiRequestOptions};
use super::simple_options::{build_base_options, resolve_sampling_params};
use super::ProviderStreams;
use crate::api::lazy::lazy_stream;
use crate::models::clamp_thinking_level;
use crate::types::{
    AssistantMessage, AssistantMessageEvent, DoneReason, JsonObject, JsonValue, Model,
    ModelThinkingLevel, OpenAIResponsesCompat, ProviderHeaders, ProviderResponse,
    ProviderStreamOptions, SimpleStreamOptions, StopReason, TranscriptContext, Usage,
};
use crate::utils::diagnostics::{thrown, ErrorObject, Thrown};
use crate::utils::error_body::{format_provider_error, normalize_provider_error};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::headers::headers_to_record;
use crate::utils::now_ms;
use crate::utils::pi_user_agent::get_pi_user_agent;
use crate::utils::provider_retry::{retry_provider_request, ProviderRetryOptions};
use crate::utils::transcript::{get_declared_tools, resolve_transcript, resolve_transcript_tools};

const AZURE_TOOL_CALL_PROVIDERS: &[&str] = &["openai", "openai-codex", "opencode", "azure"];

fn format_azure_openai_error(error: &Thrown) -> String {
    format_provider_error(
        &normalize_provider_error(error),
        Some("Azure OpenAI API error"),
    )
}

fn compat(model: &Model) -> Option<&OpenAIResponsesCompat> {
    model
        .compat
        .as_ref()
        .and_then(crate::types::ModelCompat::as_openai_responses)
}

fn compat_flag(model: &Model, read: fn(&OpenAIResponsesCompat) -> Option<bool>) -> Option<bool> {
    compat(model).and_then(read)
}

fn create_client(
    model: &Model,
    api_key: &str,
    options: &ProviderStreamOptions,
    azure: &AzureEndpointOptions,
) -> Result<OpenAiClient, Thrown> {
    let mut headers: ProviderHeaders = ProviderHeaders::new();
    headers.insert(
        "User-Agent".to_owned(),
        Some(get_pi_user_agent().to_owned()),
    );
    for (name, value) in model.headers.iter().flatten() {
        headers.insert(name.clone(), Some(value.clone()));
    }
    for (name, value) in options.stream.request.headers.iter().flatten() {
        headers.insert(name.clone(), value.clone());
    }
    let config = resolve_azure_config(&model.base_url, azure, options.stream.request.env.as_ref())
        .map_err(thrown)?;
    if config.api_version.is_empty() {
        return Err(ErrorObject::new(
            "The OPENAI_API_VERSION environment variable is missing or empty; either provide it, or instantiate the AzureOpenAI client with an apiVersion option, like new AzureOpenAI({ apiVersion: 'My API Version' }).",
        )
        .thrown());
    }
    Ok(OpenAiClient::new(OpenAiClientConfig {
        kind: OpenAiClientKind::AzureOpenAI,
        api_key: api_key.to_owned(),
        base_url: config.base_url,
        default_headers: headers,
        default_query: vec![("api-version".to_owned(), config.api_version)],
        fetch: options.stream.request.fetch.clone(),
    }))
}

fn build_params(
    model: &Model,
    context: &TranscriptContext,
    options: &ProviderStreamOptions,
    api: &OpenAIResponsesOptions,
    deployment_name: &str,
    grammar: &GrammarToolInputProperties,
) -> Result<JsonValue, Thrown> {
    let supports_additional_tools =
        compat_flag(model, |compat| compat.supports_additional_tools).unwrap_or(false);
    let supports_tool_search =
        compat_flag(model, |compat| compat.supports_tool_search).unwrap_or(false);
    let supports_strict_mode =
        compat_flag(model, |compat| compat.supports_strict_mode).unwrap_or(true);
    let supports_openai_grammar_tools =
        compat_flag(model, |compat| compat.supports_openai_grammar_tools).unwrap_or(false);
    let transcript_tools = resolve_transcript_tools(
        context.messages(),
        supports_additional_tools || supports_tool_search,
    );
    let tool_options = ConvertResponsesToolsOptions {
        strict: None,
        supports_strict_mode: Some(supports_strict_mode),
        supports_openai_grammar_tools: Some(supports_openai_grammar_tools),
        tool_search_result: None,
    };
    let messages = convert_responses_messages(
        model,
        context,
        AZURE_TOOL_CALL_PROVIDERS,
        &ConvertResponsesMessagesOptions {
            include_system_prompt: None,
            grammar_tool_input_properties: Some(grammar.clone()),
            supports_mid_convo_system_messages: Some(
                compat_flag(model, |compat| compat.supports_mid_convo_system_messages)
                    .unwrap_or(false),
            ),
            supports_additional_tools: Some(supports_additional_tools),
            supports_tool_search: Some(supports_tool_search),
            tool_options: Some(tool_options),
            explicit_cache_breakpoints: true,
        },
    )?;

    let stream_options = &options.stream;
    let mut params = JsonObject::new();
    params.insert("model".to_owned(), json!(deployment_name));
    params.insert("input".to_owned(), JsonValue::Array(messages));
    params.insert("stream".to_owned(), json!(true));
    if let Some(key) = clamp_openai_prompt_cache_key(stream_options.session_id.as_deref()) {
        params.insert("prompt_cache_key".to_owned(), json!(key));
    }
    params.insert("store".to_owned(), json!(false));

    if let Some(max_tokens) = stream_options.max_tokens.filter(|tokens| *tokens != 0) {
        params.insert(
            "max_output_tokens".to_owned(),
            json!(max_tokens.max(OPENAI_RESPONSES_MIN_OUTPUT_TOKENS)),
        );
    }
    if let Some(temperature) = stream_options.temperature {
        params.insert("temperature".to_owned(), json!(temperature));
    }
    if !transcript_tools.request_tools.is_empty() {
        params.insert(
            "tools".to_owned(),
            JsonValue::Array(convert_responses_tools(
                &transcript_tools.request_tools,
                &tool_options,
            )?),
        );
    }
    if let Some(tool_choice) = &api.tool_choice {
        params.insert("tool_choice".to_owned(), tool_choice.clone());
    }

    let reasoning_effort = reasoning_effort_of(api);
    if model.reasoning {
        if let Some(effort) = reasoning_effort {
            insert_reasoning(model, api, effort, &mut params);
        } else {
            insert_reasoning_off(model, &mut params);
        }
    }

    // Last so model and request sampling parameters override named request fields.
    let sampling_level = reasoning_effort.map_or(ModelThinkingLevel::Off, ModelThinkingLevel::from);
    if let Some(sampling_params) = resolve_sampling_params(
        model,
        sampling_level,
        stream_options.sampling_params.as_ref(),
    ) {
        params.extend(sampling_params);
    }
    // eukhe addition: keep earlier turns' reasoning in the cached prefix.
    apply_reasoning_context(model, &mut params);

    Ok(JsonValue::Object(params))
}

fn new_output(model: &Model) -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: "azure-openai-responses".to_owned(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: StopReason::Pending,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now_ms(),
    }
}

async fn run(
    model: &Model,
    context: &TranscriptContext,
    options: &ProviderStreamOptions,
    deployment_name: &str,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    request_id: &mut Option<String>,
) -> Result<DoneReason, Thrown> {
    let request = &options.stream.request;
    let api = OpenAIResponsesOptions::from_extra(&options.extra);
    let azure = AzureEndpointOptions::from_extra(&options.extra);
    let Some(api_key) = request.api_key.as_deref().filter(|key| !key.is_empty()) else {
        return Err(
            ErrorObject::new(format!("No API key for provider: {}", model.provider)).thrown(),
        );
    };
    let client = create_client(model, api_key, options, &azure)?;
    let grammar = create_grammar_tool_input_properties(
        Some(&get_declared_tools(context.messages())),
        compat_flag(model, |compat| compat.supports_openai_grammar_tools).unwrap_or(false),
    )?;
    let mut params = build_params(model, context, options, &api, deployment_name, &grammar)?;
    if let Some(on_payload) = &request.on_payload {
        if let Some(next) = on_payload(params.clone(), model).await? {
            params = next;
        }
    }
    let request_options = OpenAiRequestOptions {
        signal: request.signal.clone(),
        timeout_ms: request.timeout_ms,
    };
    let response = retry_provider_request(
        || client.post_stream("/responses", &params, &request_options),
        &ProviderRetryOptions {
            max_retries: request.max_retries,
            max_retry_delay_ms: request.max_retry_delay_ms,
            signal: request.signal.clone(),
        },
    )
    .await?;
    *request_id = response
        .headers
        .get("x-request-id")
        .and_then(|value| value.to_str().ok())
        .map(str::to_owned);
    if let Some(on_response) = &request.on_response {
        on_response(
            ProviderResponse {
                status: response.status,
                headers: headers_to_record(&response.headers),
            },
            model,
        )
        .await?;
    }
    stream.push(AssistantMessageEvent::Start {
        partial: output.clone(),
    });

    let stream_options = OpenAIResponsesStreamOptions {
        on_provider_stream_event: options.stream.on_provider_stream_event.clone(),
        service_tier: None,
        grammar_tool_input_properties: Some(grammar),
        resolve_service_tier: None,
        apply_service_tier_pricing: None,
    };
    process_responses_stream(response.events, output, stream, model, &stream_options).await?;

    let aborted = request
        .signal
        .as_ref()
        .is_some_and(eukhe_chord::context::AbortSignal::aborted);
    finish_checks(
        output,
        aborted,
        "Azure OpenAI Responses stream ended without a stop reason",
    )
}

/// TS `stream`: the `azure-openai-responses` stream function.
#[must_use]
pub fn stream(
    model: &Model,
    context: &TranscriptContext,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    let stream = AssistantMessageEventStream::new();
    let normalized_context = resolve_transcript(
        context.clone(),
        compat_flag(model, |compat| compat.supports_mid_convo_system_messages),
    );
    let model = model.clone();
    let target = stream.clone();
    tokio::spawn(async move {
        let deployment_name = resolve_deployment_name(
            &model.id,
            &AzureEndpointOptions::from_extra(&options.extra),
            options.stream.request.env.as_ref(),
        );
        let mut output = new_output(&model);
        let mut request_id = None;
        let result = run(
            &model,
            &normalized_context,
            &options,
            &deployment_name,
            &mut output,
            &target,
            &mut request_id,
        )
        .await;
        match result {
            Ok(reason) => {
                target.push(AssistantMessageEvent::Done {
                    reason,
                    message: output.clone(),
                });
                target.end(Some(output));
            }
            Err(error) => {
                let aborted = options
                    .stream
                    .request
                    .signal
                    .as_ref()
                    .is_some_and(eukhe_chord::context::AbortSignal::aborted);
                let error_message = format_azure_openai_error(&error);
                fail_stream(
                    &target,
                    output,
                    &error,
                    aborted,
                    error_message,
                    request_id.as_deref(),
                );
            }
        }
    });
    stream
}

/// TS `streamSimple`.
#[must_use]
#[allow(clippy::needless_pass_by_value)] // Signature fixed by `StreamSimpleFn`.
pub fn stream_simple(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> AssistantMessageEventStream {
    let Some(api_key) = options
        .stream
        .request
        .api_key
        .clone()
        .filter(|key| !key.is_empty())
    else {
        // TS throws synchronously; the stream contract encodes it.
        let error =
            ErrorObject::new(format!("No API key for provider: {}", model.provider)).thrown();
        return lazy_stream(model, async move { Err(error) });
    };
    let base = build_base_options(model, context, Some(&options), Some(&api_key));
    let mut extra = JsonObject::new();
    if let Some(tool_choice) = options.tool_choice {
        extra.insert("toolChoice".to_owned(), json!(tool_choice.as_str()));
    }
    if let Some(reasoning) = options.reasoning {
        let clamped = clamp_thinking_level(model, ModelThinkingLevel::from(reasoning));
        if clamped != ModelThinkingLevel::Off {
            extra.insert("reasoningEffort".to_owned(), json!(clamped.as_str()));
        }
    }
    stream(
        model,
        context,
        ProviderStreamOptions {
            stream: base,
            extra,
        },
    )
}

/// The `azure-openai-responses` module: TS exports `stream` and `streamSimple`.
#[must_use]
pub fn streams() -> ProviderStreams {
    ProviderStreams {
        stream: Arc::new(stream),
        stream_simple: Arc::new(stream_simple),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}
