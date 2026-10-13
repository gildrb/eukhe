//! Streams whose setup runs asynchronously behind them, and lazily resolved
//! API modules. Port of `api/lazy.ts`.

use std::future::Future;
use std::sync::Arc;

use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, ErrorReason, Model, StopReason, Usage,
};
use futures::future::BoxFuture;
use futures::StreamExt;

use super::ProviderStreams;
use crate::utils::diagnostics::Thrown;
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::now_ms;
use crate::utils::stream_failure::record_stream_failure;
use crate::utils::stream_idle::StreamIdle;

fn create_error_message(model: &Model, error_message: String, timestamp: u64) -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: StopReason::Error,
        deferred: None,
        error_message: Some(error_message),
        raw_stop_reason: None,
        end_turn: None,
        timestamp,
        duration_ms: None,
    }
}

fn end_with_error(target: &AssistantMessageEventStream, message: AssistantMessage) {
    target.push(AssistantMessageEvent::Error {
        reason: ErrorReason::Error,
        error: message.clone(),
    });
    target.end(Some(message));
}

async fn forward_stream(
    target: &AssistantMessageEventStream,
    source: AssistantMessageEventStream,
    idle: Option<&StreamIdle>,
) {
    let mut events = source.events();
    while let Some(event) = events.next().await {
        if let Some(idle) = idle {
            idle.touch();
        }
        target.push(event);
    }
    target.end(Some(source.result().await));
}

async fn run_setup<F>(
    target: &AssistantMessageEventStream,
    model: &Model,
    setup: F,
    started_at: u64,
    idle: Option<&StreamIdle>,
) where
    F: Future<Output = Result<AssistantMessageEventStream, Thrown>>,
{
    match setup.await {
        Ok(inner) => forward_stream(target, inner, idle).await,
        Err(error) => end_with_error(
            target,
            create_error_message(model, error.to_string(), started_at),
        ),
    }
}

/// Returns a stream synchronously while running async setup (auth
/// resolution, lazy module loading) behind it on a spawned task. Setup
/// failures terminate the stream with an error event.
///
/// Must be called inside a tokio runtime.
pub fn lazy_stream<F>(model: &Model, setup: F) -> AssistantMessageEventStream
where
    F: Future<Output = Result<AssistantMessageEventStream, Thrown>> + Send + 'static,
{
    watched_lazy_stream(model, None, setup)
}

/// [`lazy_stream`] under the stream-idle deadline `idle`: when neither the
/// setup nor the stream shows life for the deadline, the request is aborted
/// and the stream ends with a retryable `stream_stalled` error.
pub(crate) fn watched_lazy_stream<F>(
    model: &Model,
    idle: Option<StreamIdle>,
    setup: F,
) -> AssistantMessageEventStream
where
    F: Future<Output = Result<AssistantMessageEventStream, Thrown>> + Send + 'static,
{
    let started_at = now_ms();
    let outer = AssistantMessageEventStream::new();
    let target = outer.clone();
    let model = model.clone();
    tokio::spawn(async move {
        let Some(idle) = idle else {
            run_setup(&target, &model, setup, started_at, None).await;
            return;
        };
        let finished = idle
            .within(run_setup(&target, &model, setup, started_at, Some(&idle)))
            .await;
        if finished.is_none() {
            let failure = idle.stall();
            let mut message = create_error_message(&model, failure.to_string(), started_at);
            record_stream_failure(
                (&model.provider, &model.id, &model.api),
                &mut message,
                &failure,
            );
            end_with_error(&target, message);
        }
    });
    outer
}

/// Deferred-response capabilities a lazily loaded chat API declares before
/// it loads: TS `LazyApiCapabilities`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LazyApiCapabilities {
    pub fetch_deferred: bool,
    pub cancel_deferred: bool,
}

/// Loads an API module: the TS dynamic `import()`.
pub type LoadApi =
    Arc<dyn Fn() -> BoxFuture<'static, Result<ProviderStreams, Thrown>> + Send + Sync>;

/// Missing deferred support on a loaded module whose lazy wrapper declared it.
#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum LazyApiError {
    #[error("API does not support deferred responses")]
    FetchDeferredUnsupported,
    #[error("API cannot cancel deferred responses")]
    CancelDeferredUnsupported,
}

/// Wraps a lazily loaded API implementation as [`ProviderStreams`]. The
/// module loads on every call through `load` (which caches as it sees fit);
/// load failures terminate the returned stream with an error event.
#[must_use]
pub fn lazy_api(load: LoadApi, capabilities: LazyApiCapabilities) -> ProviderStreams {
    let stream_load = Arc::clone(&load);
    let simple_load = Arc::clone(&load);
    let mut api = ProviderStreams {
        stream: Arc::new(move |model, context, options| {
            let load = Arc::clone(&stream_load);
            let (request_model, context) = (model.clone(), context.clone());
            lazy_stream(model, async move {
                Ok((load().await?.stream)(&request_model, &context, options))
            })
        }),
        stream_simple: Arc::new(move |model, context, options| {
            let load = Arc::clone(&simple_load);
            let (request_model, context) = (model.clone(), context.clone());
            lazy_stream(model, async move {
                Ok((load().await?.stream_simple)(
                    &request_model,
                    &context,
                    options,
                ))
            })
        }),
        fetch_deferred: None,
        cancel_deferred: None,
    };

    if capabilities.fetch_deferred {
        let load = Arc::clone(&load);
        api.fetch_deferred = Some(Arc::new(move |model, handle, options| {
            let load = Arc::clone(&load);
            let (request_model, handle) = (model.clone(), handle.clone());
            lazy_stream(model, async move {
                let implementation = load().await?;
                let fetch = implementation
                    .fetch_deferred
                    .ok_or_else(|| Arc::new(LazyApiError::FetchDeferredUnsupported) as Thrown)?;
                Ok(fetch(&request_model, &handle, options))
            })
        }));
    }
    if capabilities.cancel_deferred {
        api.cancel_deferred = Some(Arc::new(move |model, handle, options| {
            let load = Arc::clone(&load);
            let (model, handle) = (model.clone(), handle.clone());
            Box::pin(async move {
                let implementation = load().await?;
                let cancel = implementation
                    .cancel_deferred
                    .ok_or_else(|| Arc::new(LazyApiError::CancelDeferredUnsupported) as Thrown)?;
                cancel(&model, &handle, options).await
            })
        }));
    }

    api
}
