//! Image generation over `OpenRouter`'s chat completions endpoint (port of
//! `src/api/openrouter-images.ts`), sent through the `openai` SDK request
//! path ([`super::openai_sdk`]) with SDK retries disabled.

use std::sync::{Arc, LazyLock};

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    AssistantImages, ImageContent, ImageModel, ImagesContext, ImagesStopReason, JsonValue,
    Modality, ProviderHeaders, ProviderResponse, TextContent, Usage, UsageCost, UserContentBlock,
};
use serde_json::json;

use super::openai_sdk::{
    js_truthy, OpenAiClient, OpenAiClientConfig, OpenAiClientKind, OpenAiRequestOptions,
};
use super::ProviderImages;
use crate::types::{FetchFunction, ImagesOptions};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::error_body::{format_provider_error, normalize_provider_error};
use crate::utils::headers::{headers_to_record, provider_headers_to_record};
use crate::utils::provider_retry::{retry_provider_request, ProviderRetryOptions};
use crate::utils::sanitize_unicode::sanitize_surrogates;

/// Image generation over `OpenRouter`'s chat completions endpoint. Never fails:
/// errors become a result with `stopReason` `"error"` (or `"aborted"`).
pub async fn generate_images(
    model: ImageModel,
    context: ImagesContext,
    options: ImagesOptions,
) -> AssistantImages {
    let mut output = AssistantImages {
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        output: Vec::new(),
        response_id: None,
        usage: None,
        stop_reason: ImagesStopReason::Stop,
        error_message: None,
        timestamp: crate::utils::now_ms(),
    };
    if let Err(error) = run(&model, &context, &options, &mut output).await {
        output.stop_reason = if options
            .request
            .signal
            .as_ref()
            .is_some_and(AbortSignal::aborted)
        {
            ImagesStopReason::Aborted
        } else {
            ImagesStopReason::Error
        };
        output.error_message = Some(format_provider_error(
            &normalize_provider_error(&error),
            None,
        ));
    }
    output
}

async fn run(
    model: &ImageModel,
    context: &ImagesContext,
    options: &ImagesOptions,
    output: &mut AssistantImages,
) -> Result<(), Thrown> {
    let request = &options.request;
    let Some(api_key) = request.api_key.as_deref().filter(|key| !key.is_empty()) else {
        return Err(
            ErrorObject::new(format!("No API key for provider: {}", model.provider)).thrown(),
        );
    };
    let client = create_client(
        model,
        api_key,
        request.headers.as_ref(),
        request.fetch.clone(),
    );
    let mut params = build_params(model, context);
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
        || client.post_json("/chat/completions", &params, &request_options),
        &ProviderRetryOptions {
            max_retries: request.max_retries,
            max_retry_delay_ms: request.max_retry_delay_ms,
            signal: request.signal.clone(),
        },
    )
    .await?;
    if let Some(on_response) = &request.on_response {
        let raw_response = ProviderResponse {
            status: response.status,
            headers: headers_to_record(&response.headers),
        };
        on_response(raw_response, model).await?;
    }

    let Some(response) = response.data.as_object() else {
        return Ok(());
    };
    output.response_id = response
        .get("id")
        .and_then(JsonValue::as_str)
        .map(str::to_owned);
    if let Some(usage) = response.get("usage").filter(|usage| js_truthy(usage)) {
        output.usage = Some(parse_usage(usage, model));
    }

    let choice = response
        .get("choices")
        .and_then(JsonValue::as_array)
        .and_then(|choices| choices.first());
    if let Some(message) = choice
        .and_then(JsonValue::as_object)
        .and_then(|choice| choice.get("message"))
        .and_then(JsonValue::as_object)
    {
        if let Some(content) = message
            .get("content")
            .and_then(JsonValue::as_str)
            .filter(|content| !content.is_empty())
        {
            output
                .output
                .push(UserContentBlock::Text(TextContent::new(content)));
        }
        let images = message
            .get("images")
            .and_then(JsonValue::as_array)
            .map(Vec::as_slice)
            .unwrap_or_default();
        for image in images {
            let image_url = match image.get("image_url") {
                Some(JsonValue::String(url)) => Some(url.as_str()),
                Some(JsonValue::Object(object)) => object.get("url").and_then(JsonValue::as_str),
                _ => None,
            };
            let Some(image_url) = image_url.filter(|url| url.starts_with("data:")) else {
                continue;
            };
            let Some(captures) = DATA_URL.captures(image_url) else {
                continue;
            };
            output.output.push(UserContentBlock::Image(ImageContent {
                mime_type: captures[1].to_owned(),
                data: captures[2].to_owned(),
            }));
        }
    }
    Ok(())
}

/// TS `/^data:([^;]+);base64,(.+)$/` (JS `.` excludes line terminators).
static DATA_URL: LazyLock<regex::Regex> = LazyLock::new(|| {
    regex::Regex::new(r"^data:([^;]+);base64,([^\n\r\u{2028}\u{2029}]+)$")
        .unwrap_or_else(|error| unreachable!("static regex: {error}"))
});

/// `new OpenAI({ apiKey, baseURL, fetch, defaultHeaders })` with
/// `defaultHeaders: providerHeadersToRecord({ ...model.headers, ...optionsHeaders })`.
fn create_client(
    model: &ImageModel,
    api_key: &str,
    options_headers: Option<&ProviderHeaders>,
    fetch: Option<FetchFunction>,
) -> OpenAiClient {
    // JS object spread: an overridden key keeps its first position.
    let mut spread: ProviderHeaders = model
        .headers
        .iter()
        .flatten()
        .map(|(name, value)| (name.clone(), Some(value.clone())))
        .collect();
    for (name, value) in options_headers.into_iter().flatten() {
        spread.insert(name.clone(), value.clone());
    }
    let default_headers: ProviderHeaders = provider_headers_to_record(&[Some(&spread)])
        .into_iter()
        .flatten()
        .map(|(name, value)| (name, Some(value)))
        .collect();
    OpenAiClient::new(OpenAiClientConfig {
        kind: OpenAiClientKind::OpenAI,
        api_key: api_key.to_owned(),
        base_url: model.base_url.clone(),
        default_headers,
        default_query: Vec::new(),
        fetch,
    })
}

fn build_params(model: &ImageModel, context: &ImagesContext) -> JsonValue {
    let parts: Vec<JsonValue> = context
        .input
        .iter()
        .map(|item| match item {
            UserContentBlock::Text(text) => json!({
                "type": "text",
                "text": sanitize_surrogates(&text.text),
            }),
            UserContentBlock::Image(image) => json!({
                "type": "image_url",
                "image_url": { "url": format!("data:{};base64,{}", image.mime_type, image.data) },
            }),
        })
        .collect();
    let modalities = if model.output.contains(&Modality::Text) {
        json!(["image", "text"])
    } else {
        json!(["image"])
    };
    json!({
        "model": model.id,
        "messages": [{ "role": "user", "content": parts }],
        "stream": false,
        "modalities": modalities,
    })
}

/// `value || 0` for a token count.
fn count(value: Option<&JsonValue>) -> f64 {
    value
        .and_then(JsonValue::as_f64)
        .filter(|number| !number.is_nan())
        .unwrap_or(0.0)
}

/// A token count as `Usage` stores it. Counts are integers in practice; a
/// fractional count is truncated.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // non-negative, below 2^53
fn tokens(value: f64) -> u64 {
    value.max(0.0) as u64
}

fn parse_usage(raw: &JsonValue, model: &ImageModel) -> Usage {
    let details = raw.get("prompt_tokens_details");
    let prompt_tokens = count(raw.get("prompt_tokens"));
    let reported_cached_tokens = count(details.and_then(|details| details.get("cached_tokens")));
    let cache_write_tokens = count(details.and_then(|details| details.get("cache_write_tokens")));
    let cache_read_tokens = if cache_write_tokens > 0.0 {
        (reported_cached_tokens - cache_write_tokens).max(0.0)
    } else {
        reported_cached_tokens
    };
    let input = (prompt_tokens - cache_read_tokens - cache_write_tokens).max(0.0);
    let output = count(raw.get("completion_tokens"));
    let mut cost = UsageCost {
        input: (model.cost.input / 1_000_000.0) * input,
        output: (model.cost.output / 1_000_000.0) * output,
        cache_read: (model.cost.cache_read / 1_000_000.0) * cache_read_tokens,
        cache_write: (model.cost.cache_write / 1_000_000.0) * cache_write_tokens,
        total: 0.0,
    };
    cost.total = cost.input + cost.output + cost.cache_read + cost.cache_write;
    Usage {
        input: tokens(input),
        output: tokens(output),
        cache_read: tokens(cache_read_tokens),
        cache_write: tokens(cache_write_tokens),
        cache_write_1h: None,
        reasoning: None,
        total_tokens: tokens(input + output + cache_read_tokens + cache_write_tokens),
        cost,
    }
}

/// The `OpenRouter` image API module.
#[must_use]
pub fn images() -> ProviderImages {
    ProviderImages {
        generate_images: Arc::new(|model, context, options| {
            Box::pin(generate_images(model.clone(), context.clone(), options))
        }),
    }
}

#[cfg(test)]
#[path = "openrouter_images_tests.rs"]
mod tests;
