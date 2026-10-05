//! Real-provider stream adapter: eukhe-ai completion streaming bridged into the
//! eukhe-agent loop's `StreamFn`/`ModelStream`, crossing the crate boundary by
//! wire-shape (JSON) round-trip. Shared by eukhe-cli (print/json modes) and
//! eukhe-daemon (session workers).

use std::sync::Arc;

use eukhe_agent::stream::{LlmContext, ModelStream, StreamFn, StreamRequestOptions};
use eukhe_agent::types::{Model as AgentModel, ThinkingLevel};
use eukhe_types::ai::Model;

/// Wire-shape conversion at the eukhe-agent/eukhe-ai boundary: both sides serialize
/// to the same camelCase wire shapes.
pub fn json_round_trip<T, U>(value: &T) -> Option<U>
where
    T: serde::Serialize,
    U: serde::de::DeserializeOwned,
{
    serde_json::to_value(value)
        .ok()
        .and_then(|value| serde_json::from_value(value).ok())
}

/// Thinking-level mapping across the two crates.
#[must_use]
pub fn map_thinking_level(level: eukhe_types::ai::ModelThinkingLevel) -> ThinkingLevel {
    match level {
        eukhe_types::ai::ModelThinkingLevel::Off => ThinkingLevel::Off,
        eukhe_types::ai::ModelThinkingLevel::Minimal => ThinkingLevel::Minimal,
        eukhe_types::ai::ModelThinkingLevel::Low => ThinkingLevel::Low,
        eukhe_types::ai::ModelThinkingLevel::Medium => ThinkingLevel::Medium,
        eukhe_types::ai::ModelThinkingLevel::High => ThinkingLevel::High,
        eukhe_types::ai::ModelThinkingLevel::Xhigh => ThinkingLevel::Xhigh,
        eukhe_types::ai::ModelThinkingLevel::Max => ThinkingLevel::Max,
    }
}

/// The inverse of [`map_thinking_level`]: the eukhe-types view of the agent
/// state's thinking level.
#[must_use]
pub fn model_thinking_level(level: ThinkingLevel) -> eukhe_types::ai::ModelThinkingLevel {
    match level {
        ThinkingLevel::Off => eukhe_types::ai::ModelThinkingLevel::Off,
        ThinkingLevel::Minimal => eukhe_types::ai::ModelThinkingLevel::Minimal,
        ThinkingLevel::Low => eukhe_types::ai::ModelThinkingLevel::Low,
        ThinkingLevel::Medium => eukhe_types::ai::ModelThinkingLevel::Medium,
        ThinkingLevel::High => eukhe_types::ai::ModelThinkingLevel::High,
        ThinkingLevel::Xhigh => eukhe_types::ai::ModelThinkingLevel::Xhigh,
        ThinkingLevel::Max => eukhe_types::ai::ModelThinkingLevel::Max,
    }
}

/// Adapt the loop-level payload hook to the eukhe-ai hook shape: the two
/// crates' `Model` values cross by the shared wire shape. A model that
/// fails the round-trip (a wire-shape mismatch bug) keeps the payload
/// unchanged — hooks are advisory and must never fail the request.
fn agent_payload_hook_to_ai(
    hook: eukhe_agent::stream::OnPayloadHook,
) -> eukhe_ai::types::OnPayloadHook {
    std::sync::Arc::new(move |payload: serde_json::Value, model: &Model| {
        match json_round_trip::<_, eukhe_agent::types::Model>(model) {
            Some(agent_model) => hook(payload, &agent_model),
            None => Some(payload),
        }
    })
}

/// Adapt the loop-level response hook to the eukhe-ai hook shape. The
/// `{status, headers}` response converts field-by-field; a model that
/// fails the round-trip drops the hook call (advisory, never fatal).
fn agent_response_hook_to_ai(
    hook: eukhe_agent::stream::OnResponseHook,
) -> eukhe_ai::types::OnResponseHook {
    std::sync::Arc::new(
        move |response: eukhe_ai::types::ProviderResponse, model: &Model| {
            let agent_response = eukhe_agent::stream::ProviderResponse {
                status: response.status,
                headers: response.headers,
            };
            if let Some(agent_model) = json_round_trip::<_, eukhe_agent::types::Model>(model) {
                hook(agent_response, &agent_model);
            }
        },
    )
}

/// The mutable provider target a live session's stream reads per call:
/// daemon `set_model` swaps it without rebuilding the session, and the
/// provider-failover switch swaps it for the switched-to provider. The
/// request auth is not part of it: the stream resolves the target model's
/// key and headers on every request ([`RequestAuthFn`]).
#[derive(Debug, Clone)]
pub struct ProviderTarget {
    pub model: Model,
    pub service_tier: Option<eukhe_types::ai::ServiceTier>,
}

/// Request auth for one provider request (TS `streamFn`'s
/// `getApiKeyAndHeaders`): the key and merged headers for the request's
/// model, resolved when the request is issued, so an expired OAuth token
/// refreshes mid-session and a failed refresh fails that request with its
/// reason. Implementations read auth storage and may refresh a token over
/// the network; the stream calls them off the async workers.
pub type RequestAuthFn = Arc<dyn Fn(&Model) -> crate::models::ResolvedRequestAuth + Send + Sync>;

/// A real eukhe-ai provider stream adapter for the agent loop, reading its
/// target from a shared slot the host can swap live (`set_model`, provider
/// failover) and resolving each request's auth through `request_auth`.
/// The slot is `None` only before the host sets the build-time target;
/// the adapter never runs before that.
///
/// # Panics
///
/// Panics at stream time if the provider target lock is poisoned, or if the
/// target slot was never set before the first stream.
pub fn switchable_stream_fn(
    target: Arc<std::sync::RwLock<Option<ProviderTarget>>>,
    request_auth: RequestAuthFn,
) -> StreamFn {
    Arc::new(
        move |_requested: AgentModel, context: LlmContext, options: StreamRequestOptions| {
            let ProviderTarget {
                model,
                service_tier,
            } = target
                .read()
                .expect("provider target lock")
                .clone()
                .expect("provider target set before the first stream");
            let request_auth = Arc::clone(&request_auth);
            Box::pin(async move {
                let auth_model = model.clone();
                let auth = tokio::task::spawn_blocking(move || request_auth(&auth_model)).await?;
                stream_with_auth(&model, service_tier, auth, context, options)
            })
        },
    )
}

/// Stream one completion against `model` with its resolved request auth
/// (the per-request tail the switchable seam and the CLI's
/// route-authoritative variant share). An unresolved auth (`ok: false`: a
/// token refresh that failed, a required key missing) settles the request
/// as the error turn TS produces: its `streamFn` throws `auth.error`, and
/// the agent's `handleRunFailure` settles the throw as an assistant error
/// tagged `agent_lifecycle_failure`. The tag keeps it out of the provider
/// retry ladder (TS `_isRetryableError`): re-sending cannot fix missing
/// credentials, and the failure surfaces at once.
///
/// # Errors
///
/// Returns the provider stream's error when the request fails (the
/// per-attempt failures the retry driver classifies).
pub fn stream_with_auth(
    model: &Model,
    service_tier: Option<eukhe_types::ai::ServiceTier>,
    auth: crate::models::ResolvedRequestAuth,
    context: LlmContext,
    options: StreamRequestOptions,
) -> anyhow::Result<Box<dyn ModelStream>> {
    if !auth.ok {
        let error_message = auth.error.unwrap_or_else(|| {
            format!("No request credentials resolved for \"{}\"", model.provider)
        });
        let failure = eukhe_agent::types::AssistantMessage {
            content: Vec::new(),
            api: model.api.clone(),
            provider: model.provider.clone(),
            model: model.id.clone(),
            response_model: None,
            response_id: None,
            diagnostics: Some(vec![eukhe_agent::types::assistant_message_diagnostic(
                "agent_lifecycle_failure",
                &anyhow::anyhow!(error_message.clone()),
                Some(serde_json::json!({ "source": "request_auth" })),
            )]),
            usage: eukhe_agent::types::Usage::zero(),
            stop_reason: eukhe_agent::types::StopReason::Error,
            stop_reason_raw: None,
            error_message: Some(error_message),
            timestamp: eukhe_agent::now_ms(),
        };
        let (handle, stream) = eukhe_agent::stream::event_stream();
        handle.push(eukhe_agent::stream::AssistantMessageEvent::Error {
            reason: eukhe_agent::types::StopReason::Error,
            error: failure.clone(),
        });
        handle.end(Some(failure));
        return Ok(Box::new(stream));
    }
    let crate::models::ResolvedRequestAuth {
        api_key, headers, ..
    } = auth;
    let messages: Vec<eukhe_types::ai::Message> = context
        .messages
        .iter()
        .filter_map(json_round_trip)
        .collect();
    let tools: Vec<eukhe_types::ai::Tool> =
        context.tools.iter().filter_map(json_round_trip).collect();
    let ai_context = eukhe_types::ai::Context {
        system_prompt: context.system_prompt,
        messages,
        tools: Some(tools),
    };
    // The turn's abort signal reaches the transport (TS passes the run's
    // AbortController signal into the stream options, so the fetch itself
    // cancels): the in-flight request races this token, and the loop's
    // abort paths fire it through [`ModelStream::close`] (TS
    // `closeIterator`) or the stream's drop, long before the response
    // would settle on its own.
    let cancel = tokio_util::sync::CancellationToken::new();
    let stream_options = eukhe_ai::types::SimpleStreamOptions {
        base: eukhe_ai::types::StreamOptions {
            temperature: options.temperature,
            max_tokens: options.max_tokens,
            signal: Some(cancel.clone()),
            api_key,
            transport: None,
            service_tier,
            cache_retention: None,
            session_id: options.session_id.clone(),
            // The loop-level request hooks (TS `onPayload`/`onResponse`
            // riding `SimpleStreamOptions` into the provider client) cross
            // the crate boundary here: the payload hook may replace the
            // wire payload, the response hook observes the headers.
            on_payload: options.on_payload.map(agent_payload_hook_to_ai),
            on_response: options.on_response.map(agent_response_hook_to_ai),
            // StreamOptions carries a plain map; the target's ordered
            // (BTreeMap) resolution converts here, with the request's own
            // headers (the semantic request id) merged over it — TS
            // providers' `mergeHeaders(..., optionsHeaders)` order, the
            // options win.
            headers: {
                let mut merged = headers;
                if let Some(request_headers) = options.headers.clone() {
                    merged
                        .get_or_insert_with(std::collections::BTreeMap::new)
                        .extend(request_headers);
                }
                merged.map(|headers| headers.into_iter().collect())
            },
            metadata: None,
            timeout_ms: None,
        },
        reasoning: Some(model_thinking_level(options.reasoning)),
        thinking_budgets: None,
    };
    let stream = eukhe_ai::stream_simple(model, &ai_context, Some(stream_options))
        .map_err(|error| anyhow::anyhow!("{error:?}"))?;
    // Pump eukhe-ai events into a eukhe-agent event stream (the loop's
    // ModelStream): each provider event is forwarded verbatim.
    let (handle, consumer) = eukhe_agent::stream::event_stream();
    let forwarder = tokio::spawn(async move {
        let mut stream = stream;
        while let Some(event) = stream.next_event().await {
            if let Some(converted) = convert_stream_event(&event) {
                handle.push(converted);
            }
        }
        let result = stream.result().await;
        if let Some(converted) = json_round_trip::<_, eukhe_agent::types::AssistantMessage>(&result)
        {
            handle.end(Some(converted));
        } else {
            handle.end(None);
        }
    });
    // Keep the pump task alive as long as the stream lives.
    let (forwarder, consumer) = (forwarder, consumer);
    Ok(consumer_pump(forwarder, consumer, cancel))
}

/// A stream adapter pinned to one target and one key (verification
/// harnesses and embedded hosts that resolve their auth up front): the
/// slot never changes, and every request sends `api_key` with no headers.
#[must_use]
pub fn real_stream_fn(api_key: Option<String>, model: Model) -> StreamFn {
    switchable_stream_fn(
        Arc::new(std::sync::RwLock::new(Some(ProviderTarget {
            model,
            service_tier: None,
        }))),
        Arc::new(move |_model| crate::models::ResolvedRequestAuth {
            ok: true,
            api_key: api_key.clone(),
            headers: None,
            error: None,
        }),
    )
}

/// Convert one eukhe-ai stream event into the eukhe-agent loop's event enum.
/// Payloads cross the boundary by wire-shape (JSON) round-trip.
///
/// # Panics
///
/// Panics when an assistant message cannot round-trip across the two
/// crates' wire shapes (a structural shape-mismatch bug).
#[must_use]
pub fn convert_stream_event(
    event: &eukhe_types::ai::AssistantMessageEvent,
) -> Option<eukhe_agent::stream::AssistantMessageEvent> {
    use eukhe_agent::stream::AssistantMessageEvent as Out;
    use eukhe_types::ai::AssistantMessageEvent as In;
    fn convert_partial(
        message: &eukhe_types::ai::AssistantMessage,
    ) -> eukhe_agent::types::AssistantMessage {
        json_round_trip(message).expect("assistant wire shapes match")
    }
    Some(match event {
        In::Start { partial } => Out::Start {
            partial: convert_partial(partial),
        },
        In::TextStart {
            content_index,
            partial,
        } => Out::TextStart {
            content_index: *content_index as usize,
            partial: convert_partial(partial),
        },
        In::TextDelta {
            content_index,
            delta,
            partial,
        } => Out::TextDelta {
            content_index: *content_index as usize,
            delta: delta.clone(),
            partial: convert_partial(partial),
        },
        In::TextEnd {
            content_index,
            content,
            partial,
        } => Out::TextEnd {
            content_index: *content_index as usize,
            content: content.clone(),
            partial: convert_partial(partial),
        },
        In::ThinkingStart {
            content_index,
            partial,
        } => Out::ThinkingStart {
            content_index: *content_index as usize,
            partial: convert_partial(partial),
        },
        In::ThinkingDelta {
            content_index,
            delta,
            partial,
        } => Out::ThinkingDelta {
            content_index: *content_index as usize,
            delta: delta.clone(),
            partial: convert_partial(partial),
        },
        In::ThinkingEnd {
            content_index,
            partial,
            ..
        } => Out::ThinkingEnd {
            content_index: *content_index as usize,
            partial: convert_partial(partial),
        },
        In::ToolcallStart {
            content_index,
            partial,
        } => Out::ToolCallStart {
            content_index: *content_index as usize,
            partial: convert_partial(partial),
        },
        In::ToolcallDelta {
            content_index,
            delta,
            partial,
        } => Out::ToolCallDelta {
            content_index: *content_index as usize,
            delta: delta.clone(),
            partial: convert_partial(partial),
        },
        In::ToolcallEnd {
            content_index,
            tool_call,
            partial,
        } => Out::ToolCallEnd {
            content_index: *content_index as usize,
            tool_call: json_round_trip(tool_call).expect("tool call wire shapes match"),
            partial: convert_partial(partial),
        },
        In::Done { reason, message } => Out::Done {
            reason: json_round_trip(reason).expect("stop reason wire shapes match"),
            message: convert_partial(message),
        },
        In::Error { reason, error } => Out::Error {
            reason: json_round_trip(reason).expect("stop reason wire shapes match"),
            error: convert_partial(error),
        },
    })
}

/// Wrap the consumer so the pump task is aborted when the stream drops.
fn consumer_pump(
    forwarder: tokio::task::JoinHandle<()>,
    consumer: eukhe_agent::stream::AssistantMessageEventStream,
    cancel: tokio_util::sync::CancellationToken,
) -> Box<dyn ModelStream> {
    Box::new(PumpedStream {
        _forwarder: forwarder,
        stream: consumer,
        cancel,
    })
}

/// A `ModelStream` whose lifetime keeps the eukhe-ai pump task alive and owns
/// the fetch's cancellation token (the transport half of the turn-abort:
/// the token cancels the in-flight request exactly where TS's fetch
/// `AbortSignal` fires).
struct PumpedStream {
    _forwarder: tokio::task::JoinHandle<()>,
    stream: eukhe_agent::stream::AssistantMessageEventStream,
    cancel: tokio_util::sync::CancellationToken,
}

impl Drop for PumpedStream {
    fn drop(&mut self) {
        // A dropped consumer stops reading events, so the in-flight fetch
        // behind the pump cancels instead of running to completion
        // detached (TS: the fetch dies with its iterator).
        self.cancel.cancel();
    }
}

impl ModelStream for PumpedStream {
    fn next_event(
        &mut self,
    ) -> eukhe_agent::BoxFut<'_, Option<eukhe_agent::stream::AssistantMessageEvent>> {
        self.stream.next_event()
    }

    fn result(
        &mut self,
    ) -> eukhe_agent::BoxFut<'_, anyhow::Result<eukhe_agent::types::AssistantMessage>> {
        self.stream.result()
    }

    /// Close/cancel the underlying stream (TS `iterator.return()` passed as
    /// `closeIterator` to the abort race): the in-flight fetch cancels
    /// immediately. Idempotent — the token's cancelled state is sticky.
    fn close(&mut self) {
        self.cancel.cancel();
    }
}

#[cfg(test)]
mod tests {
    //! Regression guard for the eukhe-agent -> eukhe-ai message boundary: the wire
    //! round-trip must keep user messages. `UserPart` must stay `type`-tagged
    //! like the TS wire format; an untagged variant serializes parts without
    //! `"type"`, the eukhe-ai shape rejects them, and `real_stream_fn` silently
    //! dropped every prompt admitted via `AgentPromptInput::Text` (content
    //! parts), leaving the provider with a system prompt only.

    use super::*;

    #[tokio::test]
    async fn live_target_service_tier_reaches_provider_and_reset() {
        let registration =
            eukhe_ai::faux::register_faux_provider(eukhe_ai::faux::RegisterFauxProviderOptions {
                api: Some("restored-service-tier-test".to_owned()),
                ..Default::default()
            });
        let received = Arc::new(std::sync::Mutex::new(Vec::new()));
        let captured = received.clone();
        let factory =
            eukhe_ai::faux::FauxResponseStep::Factory(Arc::new(move |_, options, _, model| {
                captured.lock().unwrap().push((
                    model.id.clone(),
                    options.and_then(|options| options.service_tier),
                ));
                Ok(eukhe_ai::faux::faux_assistant_text_message(
                    "ok",
                    eukhe_ai::faux::FauxAssistantMessageOptions::default(),
                ))
            }));
        registration.set_responses(vec![factory.clone(), factory]);
        let model = registration.get_model();
        let target = Arc::new(std::sync::RwLock::new(Some(ProviderTarget {
            model: model.clone(),
            service_tier: Some(eukhe_types::ai::ServiceTier::Priority),
        })));
        let stream_fn = switchable_stream_fn(
            target.clone(),
            Arc::new(|_model| crate::models::ResolvedRequestAuth {
                ok: true,
                ..Default::default()
            }),
        );
        for tier in [Some(eukhe_types::ai::ServiceTier::Priority), None] {
            target.write().unwrap().as_mut().unwrap().service_tier = tier;
            let mut stream = stream_fn(
                AgentModel::unknown(),
                LlmContext::default(),
                StreamRequestOptions::default(),
            )
            .await
            .unwrap();
            stream.result().await.unwrap();
        }
        assert_eq!(
            *received.lock().unwrap(),
            vec![
                (
                    model.id.clone(),
                    Some(eukhe_types::ai::ServiceTier::Priority)
                ),
                (model.id, None),
            ]
        );
        registration.unregister();
    }

    #[test]
    fn prompt_text_message_round_trips() {
        let message = eukhe_agent::types::AgentMessage::Standard(
            eukhe_agent::types::Message::User(eukhe_agent::types::UserMessage {
                content: eukhe_agent::types::UserContent::Parts(vec![
                    eukhe_agent::types::UserPart::Text(eukhe_agent::types::TextContent {
                        text: "reply with ok".into(),
                        text_signature: None,
                        cache_breakpoint: None,
                    }),
                ]),
                timestamp: 1,
            }),
        );
        let converted: Option<eukhe_types::ai::Message> = json_round_trip(&message);
        assert_eq!(
            converted,
            Some(eukhe_types::ai::Message::User(
                eukhe_types::ai::UserMessage {
                    content: eukhe_types::ai::UserContent::Blocks(vec![
                        eukhe_types::ai::UserContentBlock::Text(eukhe_types::ai::TextContent {
                            text: "reply with ok".into(),
                            text_signature: None,
                            rest: serde_json::Map::default(),
                            cache_breakpoint: None,
                        }),
                    ]),
                    timestamp: 1,
                    rest: serde_json::Map::default(),
                }
            ))
        );
    }

    /// Regression guard for the eukhe-ai -> eukhe-agent boundary: provider
    /// signatures (`thinkingSignature`, `thoughtSignature`, `textSignature`)
    /// must survive the wire-shape round-trip. eukhe-agent has no catch-all
    /// field, so a key-casing mismatch silently dropped them — an
    /// unsigned thinking block degraded to plain text in the next
    /// provider request (see the anthropic convert), and a Rust-written
    /// session lost the signature TS-written ones carry.
    #[test]
    fn provider_signatures_round_trip_both_directions() {
        let thinking = eukhe_types::ai::ThinkingContent {
            thinking: "trace".into(),
            thinking_signature: Some("sig-1".into()),
            redacted: None,
            rest: serde_json::Map::default(),
        };
        let wire = serde_json::to_value(&thinking).unwrap();
        assert_eq!(
            wire.get("thinkingSignature").and_then(|v| v.as_str()),
            Some("sig-1"),
            "the TS wire key is camelCase: {wire}"
        );
        // eukhe-ai stream output -> the eukhe-agent loop's message form.
        let agent_thinking: eukhe_agent::types::ThinkingContent =
            serde_json::from_value(wire).unwrap();
        assert_eq!(agent_thinking.thinking_signature.as_deref(), Some("sig-1"));
        // The loop's message -> the provider-facing eukhe-ai form again.
        let back: eukhe_types::ai::ThinkingContent =
            serde_json::from_value(serde_json::to_value(&agent_thinking).unwrap()).unwrap();
        assert_eq!(back.thinking_signature.as_deref(), Some("sig-1"));
        // The tool-call thought signature (Google) rides the same boundary.
        let tool_call = eukhe_types::ai::ToolCall {
            id: "toolu_1".into(),
            name: "bash".into(),
            arguments: serde_json::Map::new(),
            thought_signature: Some("sig-2".into()),
            rest: serde_json::Map::default(),
        };
        let wire = serde_json::to_value(&tool_call).unwrap();
        assert_eq!(
            wire.get("thoughtSignature").and_then(|v| v.as_str()),
            Some("sig-2"),
            "the TS wire key is camelCase: {wire}"
        );
        let agent_tool_call: eukhe_agent::types::ToolCall = serde_json::from_value(wire).unwrap();
        assert_eq!(agent_tool_call.thought_signature.as_deref(), Some("sig-2"));
    }

    /// The turn-abort cancels the in-flight fetch at the seam: a delayed
    /// faux response holds the request mid-wait; `ModelStream::close`
    /// (the loop's `closeIterator` abort callback, fired the moment the
    /// run's signal aborts) cancels the fetch NOW, so the stream settles
    /// on the aborted message instead of waiting out the provider hold.
    #[tokio::test]
    async fn closing_the_stream_cancels_a_held_fetch_immediately() {
        let registration =
            eukhe_ai::faux::register_faux_provider(eukhe_ai::faux::RegisterFauxProviderOptions {
                api: Some("held-fetch-close-test".to_string()),
                ..Default::default()
            });
        let model = registration.get_model();
        registration.set_responses(vec![eukhe_ai::faux::FauxResponseStep::Delayed {
            message: eukhe_ai::faux::faux_assistant_text_message(
                "held reply",
                eukhe_ai::faux::FauxAssistantMessageOptions::default(),
            ),
            delay_ms: 60_000,
        }]);
        let target = Arc::new(std::sync::RwLock::new(Some(ProviderTarget {
            model: model.clone(),
            service_tier: None,
        })));
        let stream_fn = switchable_stream_fn(
            target,
            Arc::new(|_model| crate::models::ResolvedRequestAuth {
                ok: true,
                ..Default::default()
            }),
        );
        let mut stream = stream_fn(
            eukhe_agent::types::Model::unknown(),
            LlmContext::default(),
            StreamRequestOptions::default(),
        )
        .await
        .expect("stream start");
        // The hold keeps the response pending; abort the turn (the agent
        // loop's close-on-abort path) mid-wait.
        stream.close();
        let settled = tokio::time::timeout(std::time::Duration::from_secs(5), stream.result())
            .await
            .expect("the closed stream settles immediately, not after the 60s hold")
            .expect("stream result");
        assert_eq!(settled.stop_reason, eukhe_agent::types::StopReason::Aborted);
        assert_eq!(
            settled.error_message.as_deref(),
            Some("Request was aborted")
        );
        // The aborted turn records no usage (TS EMPTY_USAGE on a mid-wait
        // abort: no partial message ever streamed).
        let usage = settled.usage;
        assert_eq!(usage.total_tokens, 0);
        assert_eq!(usage.input, 0);
        assert_eq!(usage.output, 0);
        assert_eq!(usage.cost.total, 0.0);
        registration.unregister();
    }
}
