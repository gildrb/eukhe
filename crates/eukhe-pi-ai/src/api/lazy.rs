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

fn create_setup_error_message(model: &Model, error: &Thrown) -> AssistantMessage {
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
        error_message: Some(error.to_string()),
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now_ms(),
    }
}

async fn forward_stream(target: &AssistantMessageEventStream, source: AssistantMessageEventStream) {
    let mut events = source.events();
    while let Some(event) = events.next().await {
        target.push(event);
    }
    target.end(Some(source.result().await));
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
    let outer = AssistantMessageEventStream::new();
    let target = outer.clone();
    let model = model.clone();
    tokio::spawn(async move {
        match setup.await {
            Ok(inner) => forward_stream(&target, inner).await,
            Err(error) => {
                let message = create_setup_error_message(&model, &error);
                target.push(AssistantMessageEvent::Error {
                    reason: ErrorReason::Error,
                    error: message.clone(),
                });
                target.end(Some(message));
            }
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
