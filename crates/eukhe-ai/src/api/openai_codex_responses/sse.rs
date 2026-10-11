//! The SSE transport: zstd request compression, the fetch retry loop, and
//! response processing. Section of the port of
//! `api/openai-codex-responses.ts`.

use std::sync::{Arc, LazyLock};

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::IndexMap;
use eukhe_types::pi_ai::{AssistantMessage, Model, ProviderEnv, ProviderResponse};
use futures::StreamExt;
use reqwest::header::HeaderMap;

use crate::api::openai_responses_shared::process_responses_stream;
use crate::types::FetchFunction;
use crate::utils::diagnostics::{thrown, ErrorObject, Thrown, ThrownValue};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::headers::headers_to_record;
use crate::utils::js::number_to_js_string;
use crate::utils::node_http_proxy::reqwest_proxy_for_target;
use crate::utils::sleep::timer_duration;
use crate::utils::stream_failure::{
    ConnectionErrorKind, ConnectionErrorProfile, ProviderConnectionError, ProviderError,
};

use super::errors::{
    aborted_error, get_retry_after_delay_ms, is_abort_error, is_retryable_error,
    parse_error_response, validate_retry_delay_ms, CodexHttpError, RetryDelayExceededError,
};
use super::events::{map_codex_events, parse_sse, OutputEffects, StartEmitter};
use super::request::{resolve_codex_url, set_header};
use super::{responses_stream_options, CodexOptions};

const DEFAULT_MAX_RETRIES: u32 = 0;
const BASE_DELAY_MS: f64 = 1000.0;
// The Codex backend accepts zstd-compressed request bodies on the SSE responses
// endpoint (the same endpoint the official Codex client compresses against).
const REQUEST_COMPRESSION_ZSTD_LEVEL: i32 = 3;

/// TS `compressRequestBodyZstd`: the zstd-compressed body, or `None` when
/// compression fails (the caller then sends the uncompressed JSON).
pub(crate) fn compress_request_body_zstd(body_json: &str) -> Option<Vec<u8>> {
    zstd::bulk::compress(body_json.as_bytes(), REQUEST_COMPRESSION_ZSTD_LEVEL).ok()
}

static DEFAULT_CLIENT: LazyLock<reqwest::Client> = LazyLock::new(reqwest::Client::new);

/// The platform `fetch` with the provider environment's proxy: one request
/// on a pooled client, or on a proxied client when `env` configures a proxy
/// for `url` (the process proxy environment is honored by reqwest itself).
async fn default_fetch(
    request: reqwest::Request,
    env: Option<ProviderEnv>,
) -> Result<reqwest::Response, Thrown> {
    let proxy = match &env {
        Some(env) => reqwest_proxy_for_target(request.url().as_str(), Some(env)).map_err(thrown)?,
        None => None,
    };
    let client = match proxy {
        Some(proxy) => reqwest::Client::builder()
            .proxy(proxy)
            .build()
            .map_err(|error| fetch_error(&error))?,
        None => DEFAULT_CLIENT.clone(),
    };
    client
        .execute(request)
        .await
        .map_err(|error| fetch_error(&error))
}

/// A failed `fetch` as the runtime reports it (eukhe stream-failure
/// connection profile).
fn fetch_error(error: &reqwest::Error) -> Thrown {
    use std::error::Error as _;
    let mut cause = error.to_string();
    let mut source = error.source();
    while let Some(inner) = source {
        cause = format!("{cause}: {inner}");
        source = inner.source();
    }
    let kind = if error.is_timeout() {
        ConnectionErrorKind::Timeout
    } else if error.is_connect() {
        ConnectionErrorKind::Connect
    } else {
        ConnectionErrorKind::Reset
    };
    thrown(ProviderError::Connection(ProviderConnectionError {
        kind,
        profile: ConnectionErrorProfile::RawFetch,
        cause,
    }))
}

async fn abort_wait(signal: Option<&AbortSignal>) {
    match signal {
        Some(signal) => signal.cancellation_token().cancelled_owned().await,
        None => std::future::pending().await,
    }
}

/// TS `sleep(ms, signal)`: rejects with `Request was aborted`.
async fn sleep(ms: f64, signal: Option<&AbortSignal>) -> Result<(), Thrown> {
    if signal.is_some_and(AbortSignal::aborted) {
        return Err(aborted_error());
    }
    tokio::select! {
        () = tokio::time::sleep(timer_duration(ms)) => Ok(()),
        () = abort_wait(signal) => Err(aborted_error()),
    }
}

/// One SSE request (TS: the fetch-with-retry block of `stream`).
pub(crate) struct SseRequest<'a> {
    pub model: &'a Model,
    pub headers: HeaderMap,
    pub body_json: &'a str,
    pub http_timeout_ms: Option<f64>,
    pub grammar_tool_input_properties: &'a IndexMap<String, String>,
    pub options: &'a CodexOptions,
}

enum Attempt {
    Done(reqwest::Response),
    Retry,
}

/// The SSE transport: send with retries, then process the event stream.
pub(crate) async fn process_sse(
    request: SseRequest<'_>,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    start: &StartEmitter,
) -> Result<(), Thrown> {
    let SseRequest {
        model,
        mut headers,
        body_json,
        http_timeout_ms,
        grammar_tool_input_properties,
        options,
    } = request;
    // Compress the request body once for the SSE path. The Codex backend
    // decodes Content-Encoding: zstd; the WebSocket transport sends the
    // uncompressed JSON frame, matching the official Codex client.
    let compressed_body = compress_request_body_zstd(body_json);
    if compressed_body.is_some() {
        set_header(&mut headers, "content-encoding", "zstd")?;
    }
    let sse_body: Vec<u8> = compressed_body.unwrap_or_else(|| body_json.as_bytes().to_vec());
    let url = resolve_codex_url(Some(&model.base_url));

    let signal = options.stream.request.signal.as_ref();
    let max_retries = options
        .stream
        .request
        .max_retries
        .unwrap_or(DEFAULT_MAX_RETRIES);
    let mut response: Option<reqwest::Response> = None;
    let mut last_error: Option<Thrown> = None;

    for attempt in 0..=max_retries {
        if signal.is_some_and(AbortSignal::aborted) {
            return Err(aborted_error());
        }

        let outcome = send_attempt(
            &url,
            &headers,
            &sse_body,
            http_timeout_ms,
            attempt,
            max_retries,
            model,
            options,
        )
        .await;
        match outcome {
            Ok(Attempt::Done(ok)) => {
                response = Some(ok);
                break;
            }
            Ok(Attempt::Retry) => {}
            Err(error) => {
                if is_abort_error(&error) {
                    return Err(aborted_error());
                }
                let error = match error.downcast_ref::<ThrownValue>() {
                    Some(value) => ErrorObject::new(value.to_string()).thrown(),
                    None => error,
                };
                // Network errors are retryable.
                if attempt < max_retries
                    && !error.is::<RetryDelayExceededError>()
                    && !error.to_string().contains("usage limit")
                {
                    last_error = Some(error);
                    sleep(BASE_DELAY_MS * 2f64.powf(f64::from(attempt)), signal).await?;
                    continue;
                }
                return Err(error);
            }
        }
    }

    let Some(response) = response else {
        return Err(last_error.unwrap_or_else(|| ErrorObject::new("Failed after retries").thrown()));
    };

    start.emit(output);
    process_stream(
        response,
        output,
        stream,
        model,
        grammar_tool_input_properties,
        options,
    )
    .await
}

/// The `try` block of one retry-loop iteration.
#[allow(clippy::too_many_arguments)] // Mirrors the TS closure scope of the loop body.
async fn send_attempt(
    url: &str,
    headers: &HeaderMap,
    body: &[u8],
    http_timeout_ms: Option<f64>,
    attempt: u32,
    max_retries: u32,
    model: &Model,
    options: &CodexOptions,
) -> Result<Attempt, Thrown> {
    let signal = options.stream.request.signal.as_ref();
    let mut request = reqwest::Request::new(
        reqwest::Method::POST,
        reqwest::Url::parse(url)
            .map_err(|error| ErrorObject::named("TypeError", error.to_string()).thrown())?,
    );
    *request.headers_mut() = headers.clone();
    *request.body_mut() = Some(reqwest::Body::from(body.to_vec()));

    let fetch: Option<FetchFunction> = options.stream.request.fetch.clone();
    let env = options.stream.request.env.clone();
    let send = async move {
        match fetch {
            Some(fetch) => fetch(request).await,
            None => default_fetch(request, env).await,
        }
    };
    let header_timeout_ms = http_timeout_ms.filter(|ms| *ms > 0.0);
    let header_timeout = async {
        match header_timeout_ms {
            Some(ms) => tokio::time::sleep(timer_duration(ms)).await,
            None => std::future::pending().await,
        }
    };
    let response = tokio::select! {
        biased;
        () = abort_wait(signal) => return Err(aborted_error()),
        () = header_timeout => {
            return Err(ErrorObject::new(format!(
                "Codex SSE response headers timed out after {}ms",
                number_to_js_string(header_timeout_ms.unwrap_or_default())
            ))
            .thrown());
        }
        response = send => response?,
    };

    if let Some(on_response) = &options.stream.request.on_response {
        on_response(
            ProviderResponse {
                status: response.status().as_u16(),
                headers: headers_to_record(response.headers()),
            },
            model,
        )
        .await?;
    }

    if response.status().is_success() {
        return Ok(Attempt::Done(response));
    }

    let status = response.status().as_u16();
    let response_headers = response.headers().clone();
    let error_text = response.text().await.map_err(|error| fetch_error(&error))?;
    if attempt < max_retries && is_retryable_error(status, &error_text) {
        let delay_ms = match get_retry_after_delay_ms(&response_headers) {
            None => BASE_DELAY_MS * 2f64.powf(f64::from(attempt)),
            Some(retry_after_delay_ms) => validate_retry_delay_ms(
                retry_after_delay_ms,
                options.stream.request.max_retry_delay_ms,
            )?,
        };

        sleep(delay_ms, signal).await?;
        return Ok(Attempt::Retry);
    }

    // Parse error for friendly message on final attempt or non-retryable error.
    // `statusText` is empty: the HTTP/2 Codex backend sends no reason phrase.
    let info = parse_error_response(&error_text, status, "");
    Err(thrown(CodexHttpError {
        message: info.friendly_message.unwrap_or(info.message),
        status,
        code: info.code,
        retry_after_ms: get_retry_after_delay_ms(&response_headers),
    }))
}

/// TS `processStream`.
async fn process_stream(
    response: reqwest::Response,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    model: &Model,
    grammar_tool_input_properties: &IndexMap<String, String>,
    options: &CodexOptions,
) -> Result<(), Thrown> {
    let signal = options.stream.request.signal.clone();
    let body = response
        .bytes_stream()
        .map(|chunk| chunk.map_err(|error| fetch_error(&error)));
    let effects = Arc::new(OutputEffects::default());
    let events = map_codex_events(
        parse_sse(body, signal),
        model,
        options.stream.on_provider_stream_event.clone(),
        Arc::clone(&effects),
    );
    let result = process_responses_stream(
        events,
        output,
        stream,
        model,
        &responses_stream_options(model, options, grammar_tool_input_properties),
    )
    .await;
    effects.apply(output);
    result
}
