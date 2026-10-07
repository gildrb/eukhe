//! Session-scoped WebSocket connection cache, continuation state, debug
//! stats, and the WebSocket request path. Section of the port of
//! `api/openai-codex-responses.ts`.
//!
//! The old eukhe port's connection cache keyed by session id is the TS
//! `websocketSessionCache` here (keyed by session id, then account id), so
//! the eukhe addition and v1.0.4 coincide.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, LazyLock, Mutex, MutexGuard, Once, PoisonError};

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::IndexMap;
use eukhe_types::pi_ai::{
    AssistantMessage, Context, JsonValue, Message, Model, ProviderEnv, Transport,
};
use reqwest::header::HeaderMap;
use serde::Serialize;
use serde_json::json;

use crate::api::openai_responses_shared::{
    convert_responses_messages, process_responses_stream, ConvertResponsesMessagesOptions,
};
use crate::session_resources::register_session_resource_cleanup;
use crate::utils::diagnostics::{format_thrown_value, Thrown};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::js::json_stringify;
use crate::utils::transcript::normalize_context;

use super::events::{map_codex_events, start_output_on_first_event, OutputEffects, StartEmitter};
use super::websocket::{
    close_websocket_silently, connect_websocket, is_websocket_reusable, parse_websocket,
    WebSocketLike,
};
use super::{clock_ms, responses_stream_options, CodexOptions, CODEX_TOOL_CALL_PROVIDERS};

const SESSION_WEBSOCKET_CACHE_TTL_MS: f64 = 5.0 * 60.0 * 1000.0;
const SESSION_WEBSOCKET_MAX_AGE_MS: f64 = 55.0 * 60.0 * 1000.0;

/// TS `OpenAICodexWebSocketDebugStats`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OpenAICodexWebSocketDebugStats {
    pub requests: u64,
    pub connections_created: u64,
    pub connections_reused: u64,
    pub cached_context_requests: u64,
    pub store_true_requests: u64,
    pub full_context_requests: u64,
    pub delta_requests: u64,
    pub last_input_items: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_delta_input_items: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_previous_response_id: Option<String>,
    pub websocket_failures: u64,
    pub sse_fallbacks: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub websocket_fallback_active: Option<bool>,
    #[serde(rename = "lastWebSocketError", skip_serializing_if = "Option::is_none")]
    pub last_websocket_error: Option<String>,
}

/// TS `CachedWebSocketContinuationState`.
#[derive(Debug, Clone)]
#[allow(clippy::struct_field_names)] // The TS field names.
struct ContinuationState {
    last_request_body: JsonValue,
    last_response_id: String,
    last_response_items: Vec<JsonValue>,
}

#[derive(Default)]
struct EntryState {
    busy: bool,
    idle_timer: Option<tokio::task::AbortHandle>,
    continuation: Option<ContinuationState>,
}

/// TS `CachedWebSocketConnection`.
struct CachedWebSocketConnection {
    socket: Arc<dyn WebSocketLike>,
    created_at: f64,
    state: Mutex<EntryState>,
}

impl CachedWebSocketConnection {
    fn state(&self) -> MutexGuard<'_, EntryState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn clear_idle_timer(&self) {
        if let Some(timer) = self.state().idle_timer.take() {
            timer.abort();
        }
    }
}

type SessionCache = HashMap<String, IndexMap<String, Arc<CachedWebSocketConnection>>>;

static WEBSOCKET_SESSION_CACHE: LazyLock<Mutex<SessionCache>> = LazyLock::new(Mutex::default);
static WEBSOCKET_DEBUG_STATS: LazyLock<Mutex<HashMap<String, OpenAICodexWebSocketDebugStats>>> =
    LazyLock::new(Mutex::default);
static WEBSOCKET_SSE_FALLBACK_SESSIONS: LazyLock<Mutex<HashSet<String>>> =
    LazyLock::new(Mutex::default);

fn session_cache() -> MutexGuard<'static, SessionCache> {
    WEBSOCKET_SESSION_CACHE
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
}

fn debug_stats() -> MutexGuard<'static, HashMap<String, OpenAICodexWebSocketDebugStats>> {
    WEBSOCKET_DEBUG_STATS
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
}

fn fallback_sessions() -> MutexGuard<'static, HashSet<String>> {
    WEBSOCKET_SSE_FALLBACK_SESSIONS
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
}

/// TS `registerSessionResourceCleanup(closeOpenAICodexWebSocketSessions)`
/// at module load: runs once, when the module is first used.
pub(crate) fn register_session_cleanup() {
    static REGISTERED: Once = Once::new();
    REGISTERED.call_once(|| {
        // The registration lives for the process, like the TS module-level call.
        let _unregister = register_session_resource_cleanup(Arc::new(|session_id| {
            close_openai_codex_websocket_sessions(session_id);
            Ok(())
        }));
    });
}

/// TS `getOrCreateWebSocketDebugStats` with an update applied.
fn update_debug_stats(session_id: &str, update: impl FnOnce(&mut OpenAICodexWebSocketDebugStats)) {
    let mut stats = debug_stats();
    update(stats.entry(session_id.to_owned()).or_default());
}

/// A copy of the WebSocket debug stats of `session_id`: TS
/// `getOpenAICodexWebSocketDebugStats`.
#[must_use]
pub fn get_openai_codex_websocket_debug_stats(
    session_id: &str,
) -> Option<OpenAICodexWebSocketDebugStats> {
    debug_stats().get(session_id).cloned()
}

/// Forget the debug stats and SSE fallback of one session, or of every
/// session: TS `resetOpenAICodexWebSocketDebugStats`.
pub fn reset_openai_codex_websocket_debug_stats(session_id: Option<&str>) {
    if let Some(session_id) = session_id.filter(|session_id| !session_id.is_empty()) {
        debug_stats().remove(session_id);
        fallback_sessions().remove(session_id);
        return;
    }
    debug_stats().clear();
    fallback_sessions().clear();
}

/// Close the cached sockets of one session, or of every session: TS
/// `closeOpenAICodexWebSocketSessions`.
pub fn close_openai_codex_websocket_sessions(session_id: Option<&str>) {
    let close_entry = |entry: &CachedWebSocketConnection| {
        entry.clear_idle_timer();
        close_websocket_silently(entry.socket.as_ref(), 1000, "debug_close");
    };
    let removed: Vec<Arc<CachedWebSocketConnection>> = {
        let mut cache = session_cache();
        match session_id.filter(|session_id| !session_id.is_empty()) {
            Some(session_id) => cache
                .remove(session_id)
                .map(|entries| entries.into_values().collect())
                .unwrap_or_default(),
            None => cache
                .drain()
                .flat_map(|(_, entries)| entries.into_values())
                .collect(),
        }
    };
    for entry in &removed {
        close_entry(entry);
    }
}

/// TS `isWebSocketSseFallbackActive`.
pub(crate) fn is_websocket_sse_fallback_active(session_id: Option<&str>) -> bool {
    session_id.is_some_and(|session_id| {
        !session_id.is_empty() && fallback_sessions().contains(session_id)
    })
}

/// TS `recordWebSocketSseFallback`.
pub(crate) fn record_websocket_sse_fallback(session_id: Option<&str>) {
    let Some(session_id) = session_id.filter(|session_id| !session_id.is_empty()) else {
        return;
    };
    let active = is_websocket_sse_fallback_active(Some(session_id));
    update_debug_stats(session_id, |stats| {
        stats.sse_fallbacks += 1;
        stats.websocket_fallback_active = Some(active);
    });
}

/// TS `recordWebSocketFailure`.
pub(crate) fn record_websocket_failure(session_id: Option<&str>, error: &Thrown) {
    let Some(session_id) = session_id.filter(|session_id| !session_id.is_empty()) else {
        return;
    };
    fallback_sessions().insert(session_id.to_owned());
    let message = format_thrown_value(error);
    update_debug_stats(session_id, |stats| {
        stats.websocket_failures += 1;
        stats.last_websocket_error = Some(message);
        stats.websocket_fallback_active = Some(true);
    });
}

/// TS `isWebSocketSessionExpired`.
fn is_websocket_session_expired(entry: &CachedWebSocketConnection) -> bool {
    clock_ms() - entry.created_at >= SESSION_WEBSOCKET_MAX_AGE_MS
}

/// Remove `entry` from the cache when it is still the account's entry.
fn remove_cached_entry(session_id: &str, account_id: &str, entry: &Arc<CachedWebSocketConnection>) {
    let mut cache = session_cache();
    if let Some(account_entries) = cache.get_mut(session_id) {
        if account_entries
            .get(account_id)
            .is_some_and(|current| Arc::ptr_eq(current, entry))
        {
            account_entries.shift_remove(account_id);
        }
        if account_entries.is_empty() {
            cache.remove(session_id);
        }
    }
}

/// TS `scheduleSessionWebSocketExpiry`.
fn schedule_session_websocket_expiry(
    session_id: &str,
    account_id: &str,
    entry: &Arc<CachedWebSocketConnection>,
) {
    entry.clear_idle_timer();
    let session_id = session_id.to_owned();
    let account_id = account_id.to_owned();
    let timer_entry = Arc::clone(entry);
    let timer = tokio::spawn(async move {
        tokio::time::sleep(crate::utils::sleep::timer_duration(
            SESSION_WEBSOCKET_CACHE_TTL_MS,
        ))
        .await;
        if timer_entry.state().busy {
            return;
        }
        close_websocket_silently(timer_entry.socket.as_ref(), 1000, "idle_timeout");
        remove_cached_entry(&session_id, &account_id, &timer_entry);
    });
    entry.state().idle_timer = Some(timer.abort_handle());
}

/// How an acquired socket is given back (TS `release`).
enum Release {
    /// A one-shot socket: always closed.
    Close,
    /// A cached socket of `session_id`/`account_id`.
    Cached {
        session_id: String,
        account_id: String,
    },
}

/// TS `acquireWebSocket` result.
struct AcquiredWebSocket {
    socket: Arc<dyn WebSocketLike>,
    entry: Option<Arc<CachedWebSocketConnection>>,
    reused: bool,
    release: Release,
}

impl AcquiredWebSocket {
    /// TS `release({ keep })`.
    fn release(self, keep: bool) {
        match (self.release, self.entry) {
            (
                Release::Cached {
                    session_id,
                    account_id,
                },
                Some(entry),
            ) => {
                if !keep || !is_websocket_reusable(entry.socket.as_ref()) {
                    close_websocket_silently(entry.socket.as_ref(), 1000, "done");
                    entry.clear_idle_timer();
                    remove_cached_entry(&session_id, &account_id, &entry);
                    return;
                }
                entry.state().busy = false;
                schedule_session_websocket_expiry(&session_id, &account_id, &entry);
            }
            (Release::Close | Release::Cached { .. }, _) => {
                close_websocket_silently(self.socket.as_ref(), 1000, "done");
            }
        }
    }
}

/// Socket connection parameters.
struct ConnectParams<'a> {
    url: &'a str,
    headers: &'a HeaderMap,
    signal: Option<&'a AbortSignal>,
    connect_timeout_ms: Option<f64>,
    env: Option<&'a ProviderEnv>,
}

impl ConnectParams<'_> {
    async fn connect(&self) -> Result<Arc<dyn WebSocketLike>, Thrown> {
        connect_websocket(
            self.url,
            self.headers,
            self.signal,
            self.connect_timeout_ms,
            self.env,
        )
        .await
    }
}

/// TS `acquireWebSocket`.
async fn acquire_websocket(
    params: &ConnectParams<'_>,
    session_id: Option<&str>,
    account_id: &str,
) -> Result<AcquiredWebSocket, Thrown> {
    let Some(session_id) = session_id.filter(|session_id| !session_id.is_empty()) else {
        let socket = params.connect().await?;
        return Ok(AcquiredWebSocket {
            socket,
            entry: None,
            reused: false,
            release: Release::Close,
        });
    };
    register_session_cleanup();
    let cached_release = || Release::Cached {
        session_id: session_id.to_owned(),
        account_id: account_id.to_owned(),
    };

    let cached = session_cache()
        .get(session_id)
        .and_then(|entries| entries.get(account_id))
        .cloned();
    if let Some(cached) = cached {
        cached.clear_idle_timer();
        let busy = cached.state().busy;
        if !busy && is_websocket_session_expired(&cached) {
            close_websocket_silently(cached.socket.as_ref(), 1000, "connection_age_limit");
            remove_cached_entry(session_id, account_id, &cached);
        } else if !busy && is_websocket_reusable(cached.socket.as_ref()) {
            cached.state().busy = true;
            return Ok(AcquiredWebSocket {
                socket: Arc::clone(&cached.socket),
                entry: Some(cached),
                reused: true,
                release: cached_release(),
            });
        }
        if busy {
            let socket = params.connect().await?;
            return Ok(AcquiredWebSocket {
                socket,
                entry: None,
                reused: false,
                release: Release::Close,
            });
        }
        if !is_websocket_reusable(cached.socket.as_ref()) {
            close_websocket_silently(cached.socket.as_ref(), 1000, "done");
            remove_cached_entry(session_id, account_id, &cached);
        }
    }

    let socket = params.connect().await?;
    let entry = Arc::new(CachedWebSocketConnection {
        socket: Arc::clone(&socket),
        created_at: clock_ms(),
        state: Mutex::new(EntryState {
            busy: true,
            ..EntryState::default()
        }),
    });
    session_cache()
        .entry(session_id.to_owned())
        .or_default()
        .insert(account_id.to_owned(), Arc::clone(&entry));
    Ok(AcquiredWebSocket {
        socket,
        entry: Some(entry),
        reused: false,
        release: cached_release(),
    })
}

/// TS `requestBodyWithoutInput` serialized.
fn request_body_without_input(body: &JsonValue) -> String {
    let mut rest = body.as_object().cloned().unwrap_or_default();
    rest.shift_remove("input");
    rest.shift_remove("previous_response_id");
    json_stringify(&JsonValue::Object(rest))
}

fn body_input(body: &JsonValue) -> &[JsonValue] {
    body.get("input")
        .and_then(JsonValue::as_array)
        .map_or(&[], Vec::as_slice)
}

/// TS `getCachedWebSocketInputDelta`.
fn get_cached_websocket_input_delta(
    body: &JsonValue,
    continuation: &ContinuationState,
) -> Option<Vec<JsonValue>> {
    if request_body_without_input(body)
        != request_body_without_input(&continuation.last_request_body)
    {
        return None;
    }

    let current_input = body_input(body);
    let baseline: Vec<JsonValue> = body_input(&continuation.last_request_body)
        .iter()
        .chain(&continuation.last_response_items)
        .cloned()
        .collect();
    if current_input.len() < baseline.len() {
        return None;
    }

    let prefix = &current_input[..baseline.len()];
    if json_stringify(&JsonValue::Array(prefix.to_vec()))
        != json_stringify(&JsonValue::Array(baseline))
    {
        return None;
    }

    Some(current_input[prefix.len()..].to_vec())
}

/// TS `buildCachedWebSocketRequestBody`.
fn build_cached_websocket_request_body(
    entry: &CachedWebSocketConnection,
    body: &JsonValue,
) -> JsonValue {
    let mut state = entry.state();
    let Some(continuation) = &state.continuation else {
        return body.clone();
    };

    let delta = get_cached_websocket_input_delta(body, continuation);
    let (Some(delta), false) = (delta, continuation.last_response_id.is_empty()) else {
        state.continuation = None;
        return body.clone();
    };

    let mut next = body.as_object().cloned().unwrap_or_default();
    next.insert(
        "previous_response_id".into(),
        JsonValue::String(continuation.last_response_id.clone()),
    );
    next.insert("input".into(), JsonValue::Array(delta));
    JsonValue::Object(next)
}

/// Parameters of one WebSocket request (TS `processWebSocketStream`).
pub(crate) struct WebSocketRequest<'a> {
    pub url: &'a str,
    pub body: &'a JsonValue,
    pub headers: &'a HeaderMap,
    pub model: &'a Model,
    pub idle_timeout_ms: Option<f64>,
    pub connect_timeout_ms: Option<f64>,
    pub cache_session_id: Option<&'a str>,
    pub account_id: &'a str,
    pub grammar_tool_input_properties: &'a IndexMap<String, String>,
    pub options: &'a CodexOptions,
}

/// TS `processWebSocketStream`. `on_start` runs when the first event is
/// handed to the Responses processor (TS `startWebSocketOutputOnFirstEvent`).
pub(crate) async fn process_websocket_stream(
    request: &WebSocketRequest<'_>,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    start: &StartEmitter,
    on_start: impl FnOnce() + Send + 'static,
) -> Result<(), Thrown> {
    let options = request.options;
    let signal = options.stream.request.signal.as_ref();
    let acquired = acquire_websocket(
        &ConnectParams {
            url: request.url,
            headers: request.headers,
            signal,
            connect_timeout_ms: request.connect_timeout_ms,
            env: options.stream.request.env.as_ref(),
        },
        request.cache_session_id,
        request.account_id,
    )
    .await?;
    let use_cached_context = matches!(
        options.stream.transport,
        Some(Transport::WebsocketCached | Transport::Auto)
    );
    // ChatGPT Codex Responses rejects `store: true` ("Store must be set to false").
    // WebSocket continuation still works via connection-scoped previous_response_id state.
    let full_body = request.body;
    let request_body = match (&acquired.entry, use_cached_context) {
        (Some(entry), true) => build_cached_websocket_request_body(entry, full_body),
        _ => full_body.clone(),
    };
    if let Some(session_id) = request
        .cache_session_id
        .filter(|session_id| !session_id.is_empty())
    {
        let input_items = body_input(&request_body).len() as u64;
        let previous_response_id = request_body
            .get("previous_response_id")
            .and_then(JsonValue::as_str)
            .filter(|id| !id.is_empty())
            .map(str::to_owned);
        let store_true = request_body.get("store") == Some(&JsonValue::Bool(true));
        update_debug_stats(session_id, |stats| {
            stats.requests += 1;
            if acquired.reused {
                stats.connections_reused += 1;
            } else {
                stats.connections_created += 1;
            }
            if use_cached_context {
                stats.cached_context_requests += 1;
            }
            if store_true {
                stats.store_true_requests += 1;
            }
            stats.last_input_items = input_items;
            if let Some(previous_response_id) = previous_response_id {
                stats.delta_requests += 1;
                stats.last_delta_input_items = Some(input_items);
                stats.last_previous_response_id = Some(previous_response_id);
            } else {
                stats.full_context_requests += 1;
                stats.last_delta_input_items = None;
                stats.last_previous_response_id = None;
            }
        });
    }

    let mut result = run_websocket_request(
        request,
        &acquired,
        &request_body,
        output,
        stream,
        start,
        on_start,
    )
    .await;
    if result.is_ok() && !signal.is_some_and(AbortSignal::aborted) {
        if let (Some(entry), true, Some(response_id)) = (
            &acquired.entry,
            use_cached_context,
            output.response_id.clone().filter(|id| !id.is_empty()),
        ) {
            match response_items(request.model, output, request.grammar_tool_input_properties) {
                Ok(response_items) => {
                    entry.state().continuation = Some(ContinuationState {
                        last_request_body: full_body.clone(),
                        last_response_id: response_id,
                        last_response_items: response_items,
                    });
                }
                Err(error) => result = Err(error),
            }
        }
    }
    let keep = if result.is_ok() {
        !signal.is_some_and(AbortSignal::aborted)
    } else {
        if let Some(entry) = &acquired.entry {
            entry.state().continuation = None;
        }
        false
    };
    acquired.release(keep);
    result
}

async fn run_websocket_request(
    request: &WebSocketRequest<'_>,
    acquired: &AcquiredWebSocket,
    request_body: &JsonValue,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    start: &StartEmitter,
    on_start: impl FnOnce() + Send + 'static,
) -> Result<(), Thrown> {
    let options = request.options;
    let signal = options.stream.request.signal.clone();
    let mut frame = serde_json::Map::new();
    frame.insert("type".into(), json!("response.create"));
    if let Some(body) = request_body.as_object() {
        for (key, value) in body {
            frame.insert(key.clone(), value.clone());
        }
    }
    let events = parse_websocket(
        Arc::clone(&acquired.socket),
        signal,
        request.idle_timeout_ms,
    );
    acquired
        .socket
        .send(json_stringify(&JsonValue::Object(frame)))?;

    let effects = Arc::new(OutputEffects::default());
    let snapshot = output.clone();
    let start = start.clone();
    let events = start_output_on_first_event(
        map_codex_events(
            events,
            request.model,
            options.stream.on_provider_stream_event.clone(),
            Arc::clone(&effects),
        ),
        move || {
            on_start();
            start.emit(&snapshot);
        },
    );
    let result = process_responses_stream(
        events,
        output,
        stream,
        request.model,
        &responses_stream_options(
            request.model,
            options,
            request.grammar_tool_input_properties,
        ),
    )
    .await;
    effects.apply(output);
    result
}

/// The assistant output as Responses input items for the continuation
/// baseline (tool outputs excluded).
fn response_items(
    model: &Model,
    output: &AssistantMessage,
    grammar_tool_input_properties: &IndexMap<String, String>,
) -> Result<Vec<JsonValue>, Thrown> {
    let context = normalize_context(Context {
        system_prompt: None,
        messages: vec![Message::Assistant(output.clone())],
        tools: None,
    });
    let items = convert_responses_messages(
        model,
        &context,
        CODEX_TOOL_CALL_PROVIDERS,
        &ConvertResponsesMessagesOptions {
            include_system_prompt: Some(false),
            grammar_tool_input_properties: Some(grammar_tool_input_properties.clone()),
            ..ConvertResponsesMessagesOptions::default()
        },
    )?;
    Ok(items
        .into_iter()
        .filter(|item| {
            !matches!(
                item.get("type").and_then(JsonValue::as_str),
                Some("function_call_output" | "custom_tool_call_output")
            )
        })
        .collect())
}
