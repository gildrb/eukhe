//! The provider runtime of a durable eukhe session: the eukhe provider
//! behaviors the generic Harness cannot own, wrapped around every
//! provider's stream functions so the durable generation only ever sees the
//! `Models` collection.
//!
//! - Image-model routing ([`super::image_route`]): a request attaching
//!   image blocks on a text-only session model routes to
//!   `settings.imageModel`, or fails with an actionable
//!   refusal.
//! - Provider failover ([`super::failover`]): after a retryable provider
//!   failure the request re-routes to the next configured provider serving
//!   the same model id, immediately (the TS backup-model retry's
//!   `delayMs: 0`), bounded by the old whole-episode ceiling. The Harness's
//!   own durable retries stay the per-provider quick-retry budget; this
//!   wrapper adds the sibling move it lacks. Every switch emits the old
//!   wire vocabulary (`auto_retry_start` with `reason: "backup"` and
//!   `backupModel`; a successful switch reports the restored primary as
//!   `restoredModel` in `auto_retry_end`) on [`ProviderRuntime::subscribe`].
//! - Quota park ([`super::park`]): a quota failure whose provider-reported
//!   reset exceeds the bounded wait parks the session — the durable
//!   `eukhe.quota_park` document on the root conversation, the park/resume
//!   transcript rows, a one-shot wake job through the scheduled-jobs (cron)
//!   path, and [`ProviderRuntime::quota_park`] for the session
//!   summary. A successful model call while parked resumes (cancelling the
//!   wake); an early resume queues the resume marker.
//! - Request timing ([`super::timing`]): per-request phase entries in the
//!   shared JSONL diagnostic log.
//!
//! Wrapping happens once per collection at session open
//! ([`ProviderRuntime::install`]), on the session's own collection; the
//! daemon's faux-script sessions share one collection across workers and
//! stay unwrapped: faux-script sessions get no failover.

use crate::cron::JobSource;
use eukhe_ai::api::lazy::lazy_stream;
use eukhe_ai::api::{StreamFn, StreamSimpleFn};
use eukhe_ai::auth::{AuthOperationOptions, AuthResolutionOverrides};
use eukhe_ai::models::Models;
use eukhe_ai::types::{
    ProviderRequestOptions, ProviderStreamOptions, SimpleStreamOptions, StreamOptions,
};
use eukhe_ai::utils::event_stream::{
    create_assistant_message_event_stream, AssistantMessageEventStream,
};
use eukhe_ai::utils::retry::{
    is_retryable_assistant_error, server_retry_after_ms, QUOTA_PARK_DIAGNOSTIC,
};
use eukhe_ai::utils::stream_idle::StreamClock;
use eukhe_chord::context::AbortSignal;
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::delta::Draft;
use eukhe_chord::json::{from_json, to_json};
use eukhe_durable::harness::json::assign_json;
use eukhe_durable::harness::types::InputSubmissionDraft;
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::types::{ConversationId, TypedEntryDraft};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageDiagnostic, AssistantMessageEvent, DoneReason, ErrorReason,
    Message, Model, PromptProgress, StopReason, TranscriptContext, Usage, UserContent,
    UserContentBlock,
};
use futures::{FutureExt, StreamExt};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;
use tokio::sync::broadcast;

use eukhe_bend::rules::retry::{Switch, Tried};

use super::failover::{failover_candidates, model_reference, next_switch, ProviderFailoverPolicy};
use super::image_route::{self, ImageRoute};
use super::park::{
    is_quota_block_failure, park_entry_data, provider_park_decision,
    quota_already_parked_final_error, quota_failure_reset_ms, quota_parked_final_error,
    resume_entry_data, NoParkReason, ParkDocState, ProviderParkDecision, ProviderParkPolicy,
    DEFAULT_PROVIDER_PARK_POLICY, PARK_DOC, PROVIDER_QUOTA_PARK_ENTRY, PROVIDER_QUOTA_RESUME_ENTRY,
    QUOTA_RESUME_CRON_LABEL, QUOTA_RESUME_MARKER_TEXT,
};
use super::timing::{self, RequestTiming};
use crate::cron::rlm_heartbeat::{RlmHeartbeatMutation, SessionBinding};
use crate::cron::store::{AgentCronJobStore, CreateAgentCronJobInput};
use crate::cron::JobStatus;
use crate::durable::entries::{CustomStateData, CUSTOM_STATE_ENTRY};
use crate::durable::rlm::now_millis;
use crate::durable::HostDeps;
use crate::settings::SettingsManager;

/// The provider runtime's wire events the durable Harness does not emit
/// (the backup-switch `auto_retry_*` vocabulary and the serving server's
/// prompt progress): broadcast to every subscriber; the daemon worker
/// translates them onto the wire.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProviderWireEvent {
    /// The failed request re-routes to `backup_model` ("provider/model-id")
    /// immediately.
    AutoRetryStart {
        attempt: u32,
        max_attempts: u32,
        delay_ms: u64,
        error_message: String,
        backup_model: String,
    },
    /// A failover episode ended: `restored_model` is the
    /// "provider/model-id" primary a successful switch restored.
    AutoRetryEnd {
        success: bool,
        attempt: u32,
        final_error: Option<String>,
        restored_model: Option<String>,
    },
    /// The serving request's server reported prompt progress (llama.cpp
    /// `prompt_progress`, before the first token).
    PromptProgress(PromptProgress),
}

/// One underlying provider dispatch of the wrapped chain: the provider's
/// original stream function with this request's options bound.
type OriginalDispatch =
    Arc<dyn Fn(&Model, &TranscriptContext) -> AssistantMessageEventStream + Send + Sync>;

/// What a failover attempt keeps of the caller's request options: the
/// abort signal, and the stream clock whose idle deadline an admission
/// queue holds (a queued fallback is not a stalled stream). Everything else
/// is per-provider and rebuilt for the sibling.
#[derive(Clone, Default)]
struct CarriedOptions {
    signal: Option<AbortSignal>,
    stream_clock: Option<StreamClock>,
}

impl CarriedOptions {
    fn of(request: &ProviderRequestOptions) -> Self {
        Self {
            signal: request.signal.clone(),
            stream_clock: request.stream_clock.clone(),
        }
    }
}

/// The context a remote provider may see: pseudonyms for the personal
/// classes (`privacy.anonymizeRemote`, `eukhe_ai::privacy`). Every wrapped
/// stream and the failover re-dispatch pass through here, so no caller
/// (turns, the compactor, branch summaries, side questions) can send raw
/// text to a remote endpoint. Loopback models see the raw text.
fn scrub_remote(
    settings: &Arc<crate::durable::EukheSettings>,
    model: &Model,
    context: &TranscriptContext,
) -> TranscriptContext {
    let manager = settings.manager();
    if manager.get_privacy_anonymize_remote() && !eukhe_ai::privacy::is_local(&model.base_url) {
        let scrubber = eukhe_ai::privacy::Scrubber::new(&manager.get_privacy_terms());
        TranscriptContext::from_normalized_messages(
            scrubber.scrub_messages(context.clone().into_messages()),
        )
    } else {
        context.clone()
    }
}

/// The installed provider runtime of one session.
pub struct ProviderRuntime {
    inner: Arc<Inner>,
}

struct Inner {
    models: Models,
    deps: Arc<HostDeps>,
    events: broadcast::Sender<ProviderWireEvent>,
    park: Mutex<Option<ParkDocState>>,
    timing: Arc<timing::RequestTimingWiring>,
    /// Every provider's original (unwrapped) stream functions, keyed by
    /// provider id: a failover re-dispatch must bypass the wrappers.
    originals: Mutex<HashMap<String, (StreamFn, StreamSimpleFn)>>,
}

impl ProviderRuntime {
    /// Wrap every provider of `models` with the eukhe provider behaviors,
    /// register the runtime on `deps` (`HostDeps::provider_runtime`), and
    /// start the open-time service that restores a persisted park.
    #[must_use]
    pub fn install(models: &Models, deps: &Arc<HostDeps>) -> Arc<ProviderRuntime> {
        let (events, _) = broadcast::channel(64);
        let runtime = Arc::new(ProviderRuntime {
            inner: Arc::new(Inner {
                models: models.clone(),
                deps: Arc::clone(deps),
                events,
                park: Mutex::new(None),
                timing: Arc::new(timing::RequestTimingWiring::new(&deps.agent_dir)),
                originals: Mutex::new(HashMap::new()),
            }),
        });
        for provider in models.get_providers() {
            let mut provider = (*provider).clone();
            let original_stream = provider.stream.clone();
            let original_simple = provider.stream_simple.clone();
            runtime
                .inner
                .originals
                .lock()
                .unwrap_or_else(poisoned)
                .insert(
                    provider.id.clone(),
                    (original_stream.clone(), original_simple.clone()),
                );
            let weak = Arc::downgrade(&runtime.inner);
            provider.stream = Arc::new(move |model, context, options| {
                let Some(inner) = weak.upgrade() else {
                    return original_stream(model, context, options);
                };
                let context = scrub_remote(&inner.deps.settings, model, context);
                let carried = CarriedOptions::of(&options.stream.request);
                let dispatch: OriginalDispatch = {
                    let original = original_stream.clone();
                    let options = options;
                    Arc::new(move |model, context| original(model, context, options.clone()))
                };
                dispatch_request(inner, model.clone(), context, dispatch, carried, false)
            });
            let weak = Arc::downgrade(&runtime.inner);
            provider.stream_simple = Arc::new(move |model, context, options| {
                let Some(inner) = weak.upgrade() else {
                    return original_simple(model, context, options);
                };
                let context = scrub_remote(&inner.deps.settings, model, context);
                let carried = CarriedOptions::of(&options.stream.request);
                let dispatch: OriginalDispatch = {
                    let original = original_simple.clone();
                    let options = options;
                    Arc::new(move |model, context| original(model, context, options.clone()))
                };
                dispatch_request(inner, model.clone(), context, dispatch, carried, true)
            });
            models.set_provider(provider);
        }
        let _first_install_wins = deps.provider_runtime.set(Arc::clone(&runtime));
        let service = Arc::clone(&runtime.inner);
        deps.add_service(Box::new(move |opened| {
            let inner = Arc::clone(&service);
            async move {
                restore_park(&inner, opened.root.id()).await;
                Ok(None)
            }
            .boxed()
        }));
        runtime
    }

    /// The runtime's wire events (the `auto_retry_*` failover
    /// vocabulary and prompt progress); a late subscriber sees only later
    /// events.
    #[must_use]
    pub fn subscribe(&self) -> broadcast::Receiver<ProviderWireEvent> {
        self.inner.events.subscribe()
    }

    /// The live quota park (its wake time and provider), `None` unparked
    /// (TS `session.isQuotaParked`): the session summary carries it so a
    /// client names the wake time.
    #[must_use]
    pub fn quota_park(&self) -> Option<ParkDocState> {
        self.inner.park.lock().unwrap_or_else(poisoned).clone()
    }
}

fn poisoned<T>(error: std::sync::PoisonError<T>) -> T {
    error.into_inner()
}

/// Drive one provider request through the eukhe behaviors: image routing,
/// request timing, the failover chain, and the quota park at its give-up.
/// Events of the serving attempt stream out live; the terminal event is the
/// chain's outcome.
fn dispatch_request(
    inner: Arc<Inner>,
    model: Model,
    context: TranscriptContext,
    original: OriginalDispatch,
    carried: CarriedOptions,
    simple: bool,
) -> AssistantMessageEventStream {
    let out = create_assistant_message_event_stream();
    let output = out.clone();
    tokio::spawn(async move {
        run_request(inner, model, context, original, carried, simple, output).await;
    });
    out
}

/// The wrapped request's driver.
async fn run_request(
    inner: Arc<Inner>,
    model: Model,
    context: TranscriptContext,
    original: OriginalDispatch,
    carried: CarriedOptions,
    simple: bool,
    out: AssistantMessageEventStream,
) {
    let settings = inner.deps.settings.manager();
    // Image-model routing: images on a text-only session model route to
    // `settings.imageModel` or fail with the actionable refusal.
    let mut serving = match image_route::resolve(
        context_has_images(&context),
        &model,
        settings.get_image_model().as_deref(),
        &inner.models,
    ) {
        ImageRoute::None => model,
        ImageRoute::Route(routed) => routed,
        ImageRoute::Refuse(text) => {
            let message = refuted_message(&model, &text);
            out.push(AssistantMessageEvent::Error {
                reason: ErrorReason::Error,
                error: message,
            });
            out.end(None);
            return;
        }
    };
    let mut timing_clock = timing::RequestTimingWiring::enabled(request_timing_flag(&settings))
        .then(|| timing::start(Arc::clone(&inner.timing), &model_reference(&serving)));
    if let Some(clock) = timing_clock.as_mut() {
        clock.request_sent();
    }
    let primary = serving.clone();
    let failover = failover_policy(&settings);
    let primary_dispatch = Arc::clone(&original);
    let mut dispatch = original;
    // The request's chain (the primary, then its failover candidates),
    // built at its first retryable failure, and its failed attempts,
    // oldest first (H3): the walk never sends the request back at once
    // to a provider it left.
    let mut chain: Vec<Model> = Vec::new();
    let mut tried: Vec<Tried> = Vec::new();
    let mut switches = 0u32;
    // A request that left its primary and gives up surfaces the primary's
    // own latest failure (its quota block is the one that parks), with one
    // line naming each backup tried and that backup's latest error.
    let mut primary_failure: Option<AssistantMessage> = None;
    let mut backup_failures: Vec<(String, String)> = Vec::new();
    loop {
        // Each attempt opens with its own `start`, which drops the failed
        // attempt's partial downstream (the event protocol).
        let mut events = dispatch(&serving, &context).events();
        let mut terminal: Option<AssistantMessage> = None;
        while let Some(event) = events.next().await {
            if let Some(clock) = timing_clock.as_mut() {
                clock.event(&event);
            }
            match &event {
                AssistantMessageEvent::Done { message, .. } => {
                    terminal = Some(message.clone());
                }
                AssistantMessageEvent::Error { error, .. } => {
                    terminal = Some(error.clone());
                }
                AssistantMessageEvent::PromptProgress { progress, .. } => {
                    let _ = inner
                        .events
                        .send(ProviderWireEvent::PromptProgress(*progress));
                    out.push(event);
                }
                AssistantMessageEvent::Start { .. }
                | AssistantMessageEvent::TextStart { .. }
                | AssistantMessageEvent::TextDelta { .. }
                | AssistantMessageEvent::TextEnd { .. }
                | AssistantMessageEvent::ThinkingStart { .. }
                | AssistantMessageEvent::ThinkingDelta { .. }
                | AssistantMessageEvent::ThinkingEnd { .. }
                | AssistantMessageEvent::ToolCallStart { .. }
                | AssistantMessageEvent::ToolCallDelta { .. }
                | AssistantMessageEvent::ToolCallEnd { .. } => out.push(event),
            }
        }
        let Some(message) = terminal else {
            // A stream that ends without a terminal event keeps the
            // provider's own contract breach: surface nothing further.
            out.end(None);
            return;
        };
        // An error and a `pending` terminal both end the request as a
        // failure (`finish_failure`): a backup's records one as tried.
        let failed = matches!(message.stop_reason, StopReason::Error | StopReason::Pending);
        if failed {
            if serving.provider == primary.provider {
                primary_failure = Some(message.clone());
            } else {
                let reference = model_reference(&serving);
                let error = final_error_of(&message);
                match backup_failures
                    .iter_mut()
                    .find(|(tried, _)| *tried == reference)
                {
                    Some((_, latest)) => *latest = error,
                    None => backup_failures.push((reference, error)),
                }
            }
        }
        let retryable =
            message.stop_reason == StopReason::Error && is_retryable_assistant_error(&message);
        let next = if retryable && failover.enabled {
            if chain.is_empty() {
                chain = failover_chain(&inner, &primary, &settings, &carried).await;
            }
            let at = chain
                .iter()
                .position(|model| model.provider == serving.provider)
                .unwrap_or(0);
            #[expect(
                clippy::cast_possible_truncation,
                clippy::cast_sign_loss,
                reason = "a server wait is a whole, positive number of ms"
            )]
            let server_wait_ms =
                server_retry_after_ms(&message).map(|ms| ms.max(0.0).ceil() as u64);
            tried.push(Tried { at, server_wait_ms });
            next_switch(chain.len(), &tried, &failover)
        } else {
            None
        };
        let Some(Switch { to, delay_ms }) = next else {
            // A switched request reports recovered only for a real answer.
            if switches > 0 && !failed && message.stop_reason != StopReason::Aborted {
                let _ = inner.events.send(ProviderWireEvent::AutoRetryEnd {
                    success: true,
                    attempt: switches,
                    final_error: None,
                    restored_model: Some(model_reference(&primary)),
                });
            }
            if failed {
                // A failure after a backup failed surfaces the primary's
                // latest failure, as the primary's, with the backups named;
                // a failure that never left the primary surfaces as it is.
                let (message, backups) = match primary_failure {
                    Some(primary_failure) if !backup_failures.is_empty() => {
                        (primary_failure, failover_note(&backup_failures))
                    }
                    Some(_) | None => (message, None),
                };
                finish_failure(inner, out, timing_clock, message, backups, &settings).await;
                return;
            }
            if message.stop_reason == StopReason::Aborted {
                // An aborted request surfaces as the stream's own abort
                // terminal; the failover chain never retries it.
                out.push(AssistantMessageEvent::Error {
                    reason: ErrorReason::Aborted,
                    error: message,
                });
                out.end(None);
                return;
            }
            if let Some(clock) = timing_clock.as_mut() {
                clock.done(&message);
            }
            resume_if_parked(&inner).await;
            out.push(AssistantMessageEvent::Done {
                reason: done_reason_of(&message),
                message,
            });
            out.end(None);
            return;
        };
        let candidate = chain[to].clone();
        switches += 1;
        let _ = inner.events.send(ProviderWireEvent::AutoRetryStart {
            attempt: switches,
            max_attempts: failover.max_switches,
            delay_ms,
            error_message: final_error_of(&message),
            backup_model: model_reference(&candidate),
        });
        // A return to a provider the request left waits its backoff; an
        // abort during the wait ends the request.
        if delay_ms > 0 {
            let cancelled = carried.signal.as_ref().map(AbortSignal::cancellation_token);
            let aborted = if let Some(cancelled) = cancelled {
                tokio::select! {
                    () = tokio::time::sleep(Duration::from_millis(delay_ms)) => false,
                    () = cancelled.cancelled() => true,
                }
            } else {
                tokio::time::sleep(Duration::from_millis(delay_ms)).await;
                false
            };
            if aborted {
                out.push(AssistantMessageEvent::Error {
                    reason: ErrorReason::Aborted,
                    error: AssistantMessage {
                        stop_reason: StopReason::Aborted,
                        ..message
                    },
                });
                out.end(None);
                return;
            }
        }
        // The primary keeps the caller's own request options; a sibling
        // dispatches through its provider's original stream function
        // (never its wrapper).
        dispatch = if to == 0 {
            Arc::clone(&primary_dispatch)
        } else {
            original_dispatch(&inner, &candidate, carried.clone(), simple)
        };
        serving = candidate;
    }
}

/// The original stream function of `model`'s provider with the sibling's
/// own auth: a failover re-dispatch resolves the candidate provider's
/// credentials through the collection (the primary's request options carry
/// the primary's key, and the original bypasses the collection's auth
/// merge) and otherwise builds fresh options per provider contract (the
/// provider-neutral defaults; API-specific keys ride `extra` on the full
/// seam, which the sibling provider would not honor identically anyway),
/// keeping only the `carried` abort signal and stream clock.
fn original_dispatch(
    inner: &Inner,
    model: &Model,
    carried: CarriedOptions,
    simple: bool,
) -> OriginalDispatch {
    let original = inner
        .originals
        .lock()
        .unwrap_or_else(poisoned)
        .get(&model.provider)
        .cloned();
    let models = inner.models.clone();
    let settings = Arc::clone(&inner.deps.settings);
    Arc::new(move |model: &Model, context: &TranscriptContext| {
        let Some((stream, stream_simple)) = original.clone() else {
            return create_assistant_message_event_stream();
        };
        let models = models.clone();
        let carried = carried.clone();
        let settings = Arc::clone(&settings);
        let (mut request_model, context) = (model.clone(), context.clone());
        lazy_stream(model, async move {
            let mut request = ProviderRequestOptions {
                signal: carried.signal,
                stream_clock: carried.stream_clock,
                ..ProviderRequestOptions::default()
            };
            // An unconfigured provider keeps default options: the provider
            // itself surfaces its missing-credential failure.
            if let Some(resolution) = models
                .get_auth_for_model(&request_model, AuthResolutionOverrides::default())
                .await?
            {
                if let Some(base_url) = resolution.auth.base_url.filter(|url| !url.is_empty()) {
                    request_model.base_url = base_url;
                }
                request.api_key = resolution.auth.api_key;
                request.headers = resolution.auth.headers;
                request.env = resolution.env;
            }
            let options = StreamOptions {
                request,
                ..StreamOptions::default()
            };
            // The failover target may be remote where the primary was
            // local: scrub against the resolved target.
            let context = scrub_remote(&settings, &request_model, &context);
            Ok(if simple {
                stream_simple(
                    &request_model,
                    &context,
                    SimpleStreamOptions {
                        stream: options,
                        ..SimpleStreamOptions::default()
                    },
                )
            } else {
                stream(
                    &request_model,
                    &context,
                    ProviderStreamOptions {
                        stream: options,
                        ..ProviderStreamOptions::default()
                    },
                )
            })
        })
    })
}

/// Terminal failure: the quota-park seam, then the failure surfaces. A
/// parked failure keeps its diagnostics (the server's wait) and gains the
/// park's own (H4), so no retry resends it to the blocked provider. The
/// park reads the message before `backups` (the failover note) joins its
/// text.
async fn finish_failure(
    inner: Arc<Inner>,
    out: AssistantMessageEventStream,
    mut timing_clock: Option<RequestTiming>,
    mut message: AssistantMessage,
    backups: Option<String>,
    settings: &SettingsManager,
) {
    if let Some(clock) = timing_clock.as_mut() {
        clock.failed(&message);
    }
    if let Some((status, resume_at_ms)) = park_for_quota_reset(&inner, &message, settings).await {
        message.error_message = Some(status);
        let details = serde_json::json!({ "resumeAtMs": resume_at_ms });
        message
            .diagnostics
            .get_or_insert_with(Vec::new)
            .push(AssistantMessageDiagnostic {
                kind: QUOTA_PARK_DIAGNOSTIC.to_owned(),
                timestamp: now_millis(),
                error: None,
                details: details.as_object().cloned(),
            });
    }
    if let Some(backups) = backups {
        message.error_message = Some(format!("{} {backups}", final_error_of(&message)));
    }
    out.push(AssistantMessageEvent::Error {
        reason: error_reason_of(&message),
        error: message,
    });
    out.end(None);
}

/// The `done` reason of a successful terminal message.
fn done_reason_of(message: &AssistantMessage) -> DoneReason {
    match message.stop_reason {
        StopReason::Stop | StopReason::Pending | StopReason::Error | StopReason::Aborted => {
            DoneReason::Stop
        }
        StopReason::Length => DoneReason::Length,
        StopReason::ToolUse => DoneReason::ToolUse,
        StopReason::Deferred => DoneReason::Deferred,
    }
}

/// The `error` reason of a failed terminal message.
fn error_reason_of(message: &AssistantMessage) -> ErrorReason {
    if message.stop_reason == StopReason::Aborted {
        ErrorReason::Aborted
    } else {
        ErrorReason::Error
    }
}
/// The user-visible error text of a failed turn (TS `errorMessage ||
/// "Unknown error"`).
fn final_error_of(message: &AssistantMessage) -> String {
    message
        .error_message
        .as_deref()
        .filter(|error| !error.is_empty())
        .unwrap_or("Unknown error")
        .to_owned()
}

/// The one-line note of a failed failover: each backup the request tried,
/// in the order it first went there, with that backup's latest error:
/// `(failover to <provider/model> failed too: <error>; failover to ...)`;
/// `None` when it tried none.
fn failover_note(backups: &[(String, String)]) -> Option<String> {
    if backups.is_empty() {
        return None;
    }
    let tried: Vec<String> = backups
        .iter()
        .map(|(reference, error)| format!("failover to {reference} failed too: {error}"))
        .collect();
    Some(format!("({})", tried.join("; ")))
}

/// The `requestTiming` settings flag of the session.
fn request_timing_flag(settings: &SettingsManager) -> bool {
    settings.get_request_timing()
}

/// The failover policy from the settings (`retry.failover`): the old
/// per-provider retry budget maps to the Harness's durable retries; the
/// switch budget and the return backoff are the request's own.
fn failover_policy(settings: &SettingsManager) -> ProviderFailoverPolicy {
    ProviderFailoverPolicy {
        enabled: settings.get_failover_enabled(),
        max_switches: u32::try_from(settings.get_failover_max_retries()).unwrap_or(u32::MAX),
        base_delay_ms: settings.get_failover_base_delay_ms(),
        max_delay_ms: settings.get_failover_max_delay_ms(),
    }
}

/// The quota-park policy from the settings (`retry.provider.waitForUsage`).
fn park_policy(settings: &SettingsManager) -> ProviderParkPolicy {
    ProviderParkPolicy {
        pause_until_reset: settings.get_park_pause_until_reset(),
        max_pause_ms: settings.get_park_max_pause_ms(),
        max_parks: u32::try_from(settings.get_park_max_parks())
            .unwrap_or(DEFAULT_PROVIDER_PARK_POLICY.max_parks),
    }
}

/// The bounded-wait cap of the quick-retry policy (the park seam's
/// reset-too-far bound).
fn wait_cap_ms(settings: &SettingsManager) -> u64 {
    settings.get_max_retry_delay_ms()
}

/// Whether `context` attaches image blocks.
fn context_has_images(context: &TranscriptContext) -> bool {
    context.messages().iter().any(|message| match message {
        Message::User(user) => user_content_has_images(&user.content),
        _ => false,
    })
}

fn user_content_has_images(content: &UserContent) -> bool {
    match content {
        UserContent::Text(_) => false,
        UserContent::Blocks(blocks) => blocks
            .iter()
            .any(|block| matches!(block, UserContentBlock::Image { .. })),
    }
}

/// A refused request's terminal message: the actionable refusal is the
/// user-visible error of a failed turn.
fn refuted_message(model: &Model, text: &str) -> AssistantMessage {
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
        error_message: Some(text.to_owned()),
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now_millis(),
        duration_ms: None,
        timing: None,
    }
}

/// The failover chain of a request to `primary`: the primary, then its
/// candidates among the models whose providers have credentials
/// ([`Models::get_available`]: a stored API key or OAuth credential, the
/// provider's environment key, or a configured `apiKey`), allowlisted
/// like every other model resolution. A provider that only declares an
/// auth method (every built-in provider does) never receives a switch: a
/// request to a provider without credentials fails with that provider's
/// missing key in place of the primary's own failure. When the
/// credential check itself fails, the chain is the primary alone.
async fn failover_chain(
    inner: &Inner,
    primary: &Model,
    settings: &SettingsManager,
    carried: &CarriedOptions,
) -> Vec<Model> {
    let available = match inner
        .models
        .get_available(
            None,
            AuthOperationOptions {
                signal: carried.signal.clone(),
            },
        )
        .await
    {
        Ok(available) => available,
        Err(error) => {
            tracing::warn!(
                %error,
                "failover credential check failed; the request stays on {}",
                model_reference(primary)
            );
            Vec::new()
        }
    };
    std::iter::once(primary.clone())
        .chain(
            failover_candidates(primary, &available)
                .into_iter()
                .filter(|candidate| allowlist_allows(settings, candidate)),
        )
        .collect()
}

/// The daemon `allowedModels` gate over one candidate (fail closed on an
/// unreadable policy: no failover may bypass the configured allowlist).
fn allowlist_allows(settings: &SettingsManager, candidate: &Model) -> bool {
    super::enforce_allowlist(settings, &model_reference(candidate)).is_ok()
}

// ---------------------------------------------------------------------------
// Quota park
// ---------------------------------------------------------------------------

/// Restore a persisted park at open (TS's build-time
/// `_restoreQuotaPark` scan, on the durable document): a live park keeps
/// its wake; a resume already recorded cleared the document.
async fn restore_park(inner: &Arc<Inner>, conversation: ConversationId) {
    let Some(root) = inner.deps.harness.root() else {
        return;
    };
    let read = root
        .commit(
            move |tx| async move { read_park_doc(&tx, conversation).await },
            &BACKGROUND_CONTEXT,
        )
        .await;
    if let Ok(Some(state)) = read {
        if live_park(&state) {
            *inner.park.lock().unwrap_or_else(poisoned) = Some(state);
        }
    }
}

/// Whether a document state is a live park (a cleared or never-set park
/// document reads as the all-default value and must not restore).
fn live_park(state: &ParkDocState) -> bool {
    state.park_count > 0 && state.resume_at_ms > 0
}

/// The park document's current value (creating the document when absent).
async fn read_park_doc(
    tx: &Tx,
    conversation: ConversationId,
) -> SessionResult<Option<ParkDocState>> {
    let draft = tx.doc(&PARK_DOC, conversation).await?;
    Ok(from_json(&draft.value()?).ok())
}

/// Write the park document in one commit alongside an optional entry row.
async fn write_park(
    inner: &Inner,
    state: Option<&ParkDocState>,
    row: Option<(&'static str, serde_json::Value)>,
) -> SessionResult<()> {
    let Some(root) = inner.deps.harness.root() else {
        return Ok(());
    };
    let conversation = root.id();
    let state = state.cloned();
    root.commit(
        move |tx| async move {
            let draft = tx.doc(&PARK_DOC, conversation).await?;
            write_park_doc(&draft, &state.unwrap_or_default())?;
            if let Some((custom_type, data)) = row {
                tx.append_entry(
                    conversation,
                    CUSTOM_STATE_ENTRY.draft(&TypedEntryDraft {
                        model: None,
                        data: CustomStateData {
                            custom_type: custom_type.to_owned(),
                            data: Some(data),
                        },
                        head: None,
                        edits: None,
                    })?,
                )
                .await?;
            }
            Ok(())
        },
        &BACKGROUND_CONTEXT,
    )
    .await
}

/// Replace the park document's value leaf by leaf (the goal docs' write
/// shape).
fn write_park_doc(draft: &Draft, value: &ParkDocState) -> SessionResult<()> {
    let encoded = to_json(value)?;
    let Some(fields) = encoded.as_object() else {
        return Err(SessionError::error("a document value must be an object"));
    };
    for name in draft.keys()? {
        if !fields.contains_key(&name) {
            draft.delete(name.as_str())?;
        }
    }
    for (name, child) in fields.iter() {
        assign_json(draft, name, child)?;
    }
    Ok(())
}

/// The park seam at the chain's give-up: a quota failure whose
/// provider-reported reset exceeds the bounded wait parks the session until
/// the reset (durable document + wake job + transcript row) and returns the
/// parked status for the surfaced message with the park's wake time (epoch
/// ms); `None` keeps the give-up.
async fn park_for_quota_reset(
    inner: &Arc<Inner>,
    message: &AssistantMessage,
    settings: &SettingsManager,
) -> Option<(String, u64)> {
    if !is_quota_block_failure(message) {
        return None;
    }
    let reset_ms = quota_failure_reset_ms(message);
    let cap = wait_cap_ms(settings);
    if reset_ms.is_some_and(|reset| reset <= cap) {
        // A reset inside the bounded wait keeps the quick-retry schedule
        // (the old wait loop waited those out in-turn).
        return None;
    }
    let error = final_error_of(message);
    let now = now_millis();
    let policy = park_policy(settings);
    let existing = inner.park.lock().unwrap_or_else(poisoned).clone();
    if let Some(park) = &existing {
        if park.resume_at_ms > now {
            // A live park owns the resume: this request ends without
            // consuming a park or rescheduling. A vanished wake (a user
            // cancel in `/cron`) is rebuilt so the park still wakes.
            if park
                .job_id
                .as_deref()
                .is_some_and(|job_id| wake_job_active(inner, job_id))
            {
                return Some((
                    quota_already_parked_final_error(park.resume_at_ms, &error),
                    park.resume_at_ms,
                ));
            }
            let rebuilt = create_wake_job(inner, park.resume_at_ms).await?;
            let state = ParkDocState {
                job_id: Some(rebuilt.clone()),
                ..park.clone()
            };
            if let Err(write_error) = write_park(
                inner,
                Some(&state),
                Some((
                    PROVIDER_QUOTA_PARK_ENTRY,
                    park_entry_data(park.resume_at_ms, park.park_count, Some(&rebuilt), None),
                )),
            )
            .await
            {
                tracing::warn!(error = %write_error, "quota park wake-rebuild write failed");
            }
            *inner.park.lock().unwrap_or_else(poisoned) = Some(state);
            return Some((
                quota_already_parked_final_error(park.resume_at_ms, &error),
                park.resume_at_ms,
            ));
        }
    }
    let parks_used = existing.as_ref().map_or(0, |park| park.park_count);
    let resume_after_ms = match provider_park_decision(parks_used, reset_ms, &policy) {
        ProviderParkDecision::Park { resume_after_ms } => resume_after_ms,
        ProviderParkDecision::None { reason } => match reason {
            NoParkReason::Disabled | NoParkReason::ParkBudget => {
                // The episode ends here: a stale park's wake already fired,
                // so nothing else would resume it.
                if let Some(park) = existing.filter(|park| park.resume_at_ms <= now) {
                    if let Some(job_id) = &park.job_id {
                        cancel_wake_job(inner, job_id);
                    }
                    clear_park(inner, "wake-error").await;
                }
                return None;
            }
            NoParkReason::NoReset => return None,
        },
    };
    let resume_at_ms = now.saturating_add(resume_after_ms);
    // The old park cancels the existing wake before arming the replacement.
    if let Some(job_id) = existing.as_ref().and_then(|park| park.job_id.as_deref()) {
        cancel_wake_job(inner, job_id);
    }
    // Arm the durable wake first: without a wake the park would be a silent
    // death, so a failed job creation declines the park.
    let job_id = create_wake_job(inner, resume_at_ms).await?;
    let park_count = parks_used + 1;
    let state = ParkDocState {
        resume_at_ms,
        park_count,
        job_id: Some(job_id.clone()),
        provider: Some(message.provider.as_str().to_owned()),
        wake_retries: 0,
    };
    // The durable park record gates the park exactly like the wake: a
    // failed write cancels the wake and declines the park.
    if let Err(write_error) = write_park(
        inner,
        Some(&state),
        Some((
            PROVIDER_QUOTA_PARK_ENTRY,
            park_entry_data(
                resume_at_ms,
                park_count,
                Some(&job_id),
                Some(message.provider.as_str()),
            ),
        )),
    )
    .await
    {
        tracing::warn!(error = %write_error, "quota park entry write failed, the park is declined");
        cancel_wake_job(inner, &job_id);
        return None;
    }
    *inner.park.lock().unwrap_or_else(poisoned) = Some(state);
    let abort = format!(
        "Provider requested a {}s wait before retrying (above retry.provider.maxRetryDelayMs={cap}ms)",
        reset_ms.unwrap_or_default().div_ceil(1000),
    );
    Some((
        quota_parked_final_error(&abort, resume_at_ms, &error),
        resume_at_ms,
    ))
}

/// A parked session completed a model call: the quota is back. Clear the
/// park (cancelling any pending wake), record the resumed transition, and —
/// unless the wake job already fired its resume marker — queue the marker
/// so the interrupted task continues right away (TS
/// `_completeQuotaParkResume`).
async fn resume_if_parked(inner: &Arc<Inner>) {
    let Some(park) = inner.park.lock().unwrap_or_else(poisoned).clone() else {
        return;
    };
    let woken = park
        .job_id
        .as_deref()
        .is_some_and(|job_id| wake_job_fired(inner, job_id));
    clear_park(inner, if woken { "wake" } else { "early" }).await;
    if woken {
        return;
    }
    // Early resume: the marker continues the interrupted task now.
    if let Some(root) = inner.deps.harness.root() {
        let submitted = root
            .submit(
                InputSubmissionDraft {
                    origin: InputOrigin::QuotaResume,
                    ..InputSubmissionDraft::new(QUOTA_RESUME_MARKER_TEXT.to_owned())
                },
                &BACKGROUND_CONTEXT,
            )
            .await;
        if let Err(error) = submitted {
            tracing::warn!(%error, "quota early-resume marker submission failed");
        }
    }
}

/// Clear the live park: cancel the wake, clear the document, record the
/// resume row.
async fn clear_park(inner: &Arc<Inner>, outcome: &str) {
    let park = inner.park.lock().unwrap_or_else(poisoned).take();
    let Some(park) = park else {
        return;
    };
    if let Some(job_id) = &park.job_id {
        cancel_wake_job(inner, job_id);
    }
    if let Err(write_error) = write_park(
        inner,
        None,
        Some((PROVIDER_QUOTA_RESUME_ENTRY, resume_entry_data(outcome))),
    )
    .await
    {
        tracing::warn!(error = %write_error, "quota resume entry write failed (outcome {outcome})");
    }
}

/// Create the durable one-shot wake that resumes a parked session: a
/// `quota-resume` cron job in the session's own artifacts whose prompt is
/// the resume marker (TS `_createQuotaResumeJob`), through the embedding's
/// scheduled-jobs wiring when wired, else the private
/// `<agent_dir>/cron-jobs.json` store bound to this session (the heartbeat
/// fallback). `None` when no store can serve the session.
async fn create_wake_job(inner: &Inner, resume_at_ms: u64) -> Option<String> {
    let (store, binding) = cron_wiring(inner);
    let schedule_text = format!(
        "at {}",
        crate::session::manager::format_iso(i64::try_from(resume_at_ms).unwrap_or(i64::MAX))
    );
    let job = store
        .create(&CreateAgentCronJobInput {
            session_id: binding.session_id.clone(),
            session_file: binding.session_file.clone(),
            cwd: binding.cwd.clone(),
            source: Some(JobSource::QuotaResume),
            label: Some(QUOTA_RESUME_CRON_LABEL.to_owned()),
            prompt: QUOTA_RESUME_MARKER_TEXT.to_owned(),
            schedule_text,
            now: Some(now_millis()),
            ..Default::default()
        })
        .ok()?;
    // Re-arm the scheduler so the armed job gets a live timer (the same
    // post-mutation seam the kernel heartbeat controllers use).
    if let Some(hook) = inner
        .deps
        .cron
        .as_ref()
        .and_then(|cron| cron.mutation_hook.clone())
    {
        hook(RlmHeartbeatMutation {
            job: job.clone(),
            drop_queued: false,
        })
        .await;
    }
    Some(job.id)
}

/// Whether the park's wake job is still scheduled (Active).
fn wake_job_active(inner: &Inner, job_id: &str) -> bool {
    let (store, _) = cron_wiring(inner);
    store
        .list()
        .iter()
        .any(|job| job.id == job_id && job.status == JobStatus::Active)
}

/// Whether the park's wake job has fired its resume marker.
fn wake_job_fired(inner: &Inner, job_id: &str) -> bool {
    let (store, _) = cron_wiring(inner);
    store
        .list()
        .iter()
        .any(|job| job.id == job_id && job.run_count > 0)
}

/// Cancel a pending wake job (a completed — fired — job stays).
fn cancel_wake_job(inner: &Inner, job_id: &str) {
    let (store, _) = cron_wiring(inner);
    if store
        .list()
        .iter()
        .any(|job| job.id == job_id && job.status == JobStatus::Active)
    {
        if let Err(error) = store.cancel(job_id, now_millis()) {
            tracing::warn!(%error, "quota park wake-job cancel failed");
        }
    }
}

/// The scheduled-jobs store and the session identity wake jobs bind to.
fn cron_wiring(inner: &Inner) -> (Arc<AgentCronJobStore>, SessionBinding) {
    match &inner.deps.cron {
        Some(wiring) => {
            let binding = wiring.binding.as_ref();
            (
                Arc::clone(&wiring.store),
                SessionBinding {
                    session_id: binding.map_or_else(
                        || inner.deps.session_id.clone(),
                        |binding| binding.session_id.clone(),
                    ),
                    session_file: binding.map_or_else(
                        || fallback_session_file(inner),
                        |binding| binding.session_file.clone(),
                    ),
                    cwd: binding.map_or_else(
                        || inner.deps.cwd.display().to_string(),
                        |binding| binding.cwd.clone(),
                    ),
                },
            )
        }
        None => (
            Arc::new(AgentCronJobStore::new(
                inner.deps.agent_dir.join("cron-jobs.json"),
            )),
            SessionBinding {
                session_id: inner.deps.session_id.clone(),
                session_file: fallback_session_file(inner),
                cwd: inner.deps.cwd.display().to_string(),
            },
        ),
    }
}

fn fallback_session_file(inner: &Inner) -> String {
    inner
        .deps
        .storage_dir
        .as_ref()
        .map(|dir| dir.display().to_string())
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::durable::deps::{ResolvedServices, SessionConfig, SessionStorage};
    use crate::durable::EukheSettings;
    use crate::resources::LoadedResources;
    use eukhe_ai::models::{
        create_models as create_pi_models, CreateModelsOptions, ModelsSimpleStreamOptions,
    };
    use eukhe_ai::providers::faux::{
        faux_assistant_message, faux_provider, FauxAssistantMessageOptions, FauxModelDefinition,
        FauxProviderHandle, FauxResponseStep, RegisterFauxProviderOptions,
    };
    use eukhe_types::pi_ai::{
        Context as PiContext, ImageContent, JsonObject, Modality, StopReason, TextContent, Usage,
        UserMessage,
    };

    /// A session-shaped `HostDeps` over temp dirs (no Harness attached:
    /// the stream wrapper alone is under test).
    struct Fixture {
        dir: tempfile::TempDir,
        models: Models,
        runtime: Arc<ProviderRuntime>,
        faux_a: FauxProviderHandle,
        faux_b: FauxProviderHandle,
    }

    /// `faux-a` serves `shared-1`; `faux-b` serves `second_model_id` (the
    /// same id makes it a failover sibling). `text_only` pins the serving
    /// model's input to text (image routing).
    fn fixture_with(text_only: bool, second_model_id: &str) -> Fixture {
        fixture_set(text_only, second_model_id, &serde_json::json!({}))
    }

    /// [`fixture_with`] whose global `settings.json` holds `settings`.
    fn fixture_set(
        text_only: bool,
        second_model_id: &str,
        settings: &serde_json::Value,
    ) -> Fixture {
        let dir = tempfile::tempdir().expect("tempdir");
        let agent_dir = dir.path().join("agent");
        let cwd = dir.path().join("cwd");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");
        std::fs::create_dir_all(&cwd).expect("cwd");
        std::fs::write(agent_dir.join("settings.json"), settings.to_string())
            .expect("settings.json");
        let mut definition = FauxModelDefinition::new("shared-1");
        if text_only {
            definition.input = Some(vec![Modality::Text]);
        }
        let faux_a = faux_provider(RegisterFauxProviderOptions {
            provider: Some("faux-a".to_owned()),
            models: Some(vec![definition]),
            ..RegisterFauxProviderOptions::default()
        });
        let faux_b = faux_provider(RegisterFauxProviderOptions {
            provider: Some("faux-b".to_owned()),
            models: Some(vec![FauxModelDefinition::new(second_model_id)]),
            ..RegisterFauxProviderOptions::default()
        });
        let models = create_pi_models(CreateModelsOptions::default());
        models.set_provider(faux_a.provider.clone());
        models.set_provider(faux_b.provider.clone());
        let settings = Arc::new(EukheSettings::new(&cwd, &agent_dir));
        let deps = Arc::new(HostDeps::new(
            &SessionConfig::new(&agent_dir, &cwd, "session-test", SessionStorage::Memory),
            ResolvedServices {
                storage_dir: None,
                settings,
                models: models.clone(),
                resources: Arc::new(LoadedResources::default()),
                generic_mcp_servers: Vec::new(),
                mcp: Arc::new(Mutex::new(crate::mcp::McpManager::new(
                    crate::mcp::McpManagerOptions {
                        auth_storage: crate::auth::AuthStorage::create(&agent_dir),
                        get_user_servers: Box::new(|| None),
                        begin_login: None,
                        agent_dir: None,
                        get_catalog_sources: None,
                        remote_source: None,
                        probe_override: None,
                    },
                ))),
                python_skills: Vec::new(),
                semantic_edges: Arc::new(
                    crate::durable::observe::semantic_edges::SemanticEdgeRecorder::open(
                        crate::durable::observe::semantic_edges::SemanticEdgeIdentity {
                            session_id: "session-test".to_owned(),
                            ledger_path: None,
                            parent_session_id: None,
                            spawned_by_request_id: None,
                        },
                    ),
                ),
            },
        ));
        let runtime = ProviderRuntime::install(&models, &deps);
        Fixture {
            dir,
            models,
            runtime,
            faux_a,
            faux_b,
        }
    }

    fn fixture(text_only: bool) -> Fixture {
        fixture_with(text_only, "shared-1")
    }

    fn user_message(content: UserContent) -> Message {
        Message::User(UserMessage {
            content,
            timestamp: 0,
        })
    }

    async fn drive(models: &Models, model: &Model, messages: Vec<Message>) -> AssistantMessage {
        models
            .stream_simple(
                model,
                PiContext {
                    system_prompt: None,
                    messages,
                    tools: None,
                },
                ModelsSimpleStreamOptions::default(),
            )
            .result()
            .await
    }

    fn error_step(text: &str) -> FauxResponseStep {
        let mut message = faux_assistant_message(text, FauxAssistantMessageOptions::default());
        message.stop_reason = StopReason::Error;
        message.error_message = Some(text.to_owned());
        message.into()
    }

    /// What the provider receives, echoed back: a remote model sees
    /// pseudonyms for every personal class (`privacy.anonymizeRemote`,
    /// `privacy.terms`), a loopback model sees the raw text.
    #[tokio::test]
    async fn remote_models_receive_pseudonyms_loopback_receives_raw_text() {
        let fixture = fixture_set(
            /*text_only*/ true,
            "shared-1",
            &serde_json::json!({ "privacy": { "terms": ["Gil Rodrigues"] } }),
        );
        let echo = |handle: &FauxProviderHandle| {
            handle.set_responses(vec![FauxResponseStep::factory(
                |context: &TranscriptContext,
                 _options: Option<&SimpleStreamOptions>,
                 _state: &eukhe_ai::providers::faux::FauxProviderState,
                 _model: &Model| {
                    let seen = context
                        .messages()
                        .iter()
                        .rev()
                        .find_map(|message| match message {
                            Message::User(user) => match &user.content {
                                UserContent::Text(text) => Some(text.clone()),
                                UserContent::Blocks(blocks) => {
                                    blocks.iter().find_map(|block| match block {
                                        UserContentBlock::Text(text) => Some(text.text.clone()),
                                        UserContentBlock::Image(_) => None,
                                    })
                                }
                            },
                            _ => None,
                        })
                        .unwrap_or_default();
                    Ok(faux_assistant_message(
                        seen,
                        FauxAssistantMessageOptions::default(),
                    ))
                },
            )]);
        };
        let said = |text: &str| {
            user_message(UserContent::Blocks(vec![UserContentBlock::Text(
                TextContent::new(text),
            )]))
        };

        let mut remote = fixture.faux_a.get_model();
        remote.base_url = "https://api.anthropic.com".to_owned();
        echo(&fixture.faux_a);
        let reply = drive(
            &fixture.models,
            &remote,
            vec![said(
                "Gil Rodrigues works at /home/gil/x, mail gil@example.org",
            )],
        )
        .await;
        let seen = format!("{reply:?}");
        assert!(seen.contains("PERSON_1"), "the name became a token: {seen}");
        assert!(
            seen.contains("HOME_1"),
            "the home name became a token: {seen}"
        );
        assert!(seen.contains("EMAIL_1"), "the email became a token: {seen}");
        assert!(!seen.contains("Gil Rodrigues"), "the name leaked: {seen}");
        assert!(!seen.contains("/home/gil"), "the path leaked: {seen}");
        assert!(
            !seen.contains("gil@example.org"),
            "the email leaked: {seen}"
        );

        let local = fixture.faux_a.get_model();
        echo(&fixture.faux_a);
        let reply = drive(
            &fixture.models,
            &local,
            vec![said("Gil Rodrigues works at /home/gil/x")],
        )
        .await;
        let seen = format!("{reply:?}");
        assert!(
            seen.contains("Gil Rodrigues"),
            "loopback sees raw text: {seen}"
        );
        assert!(
            seen.contains("/home/gil/x"),
            "loopback sees raw paths: {seen}"
        );
    }

    #[tokio::test]
    async fn failover_switches_to_the_sibling_provider_and_restores_the_primary() {
        let fixture = fixture(/*text_only*/ false);
        let model = fixture.faux_a.get_model();
        fixture
            .faux_a
            .set_responses(vec![error_step("503 Service Unavailable")]);
        fixture
            .faux_b
            .set_responses(vec![FauxResponseStep::Message(Box::new(
                faux_assistant_message("backup answer", FauxAssistantMessageOptions::default()),
            ))]);
        let mut events = fixture.runtime.subscribe();
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        assert_eq!(message.stop_reason, StopReason::Stop);
        assert!(
            message
                .content
                .iter()
                .any(|block| matches!(block, eukhe_types::pi_ai::AssistantContentBlock::Text(text) if text.text == "backup answer")),
            "the sibling provider served the turn: {message:?}"
        );
        let start = events.try_recv().expect("the switch event");
        assert!(
            matches!(
                &start,
                ProviderWireEvent::AutoRetryStart {
                    attempt: 1,
                    delay_ms: 0,
                    backup_model,
                    ..
                } if backup_model == "faux-b/shared-1"
            ),
            "{start:?}"
        );
        let end = events.try_recv().expect("the restore event");
        assert!(
            matches!(
                &end,
                ProviderWireEvent::AutoRetryEnd {
                    success: true,
                    attempt: 1,
                    restored_model: Some(restored),
                    ..
                } if restored == "faux-a/shared-1"
            ),
            "{end:?}"
        );
    }

    /// Regression: the sibling attempt dispatched with fresh options, so a
    /// queue at the fallback ran without the request's stream clock (a
    /// queued fallback read as a stalled stream) and ignored its abort.
    #[tokio::test]
    async fn failover_attempts_keep_the_abort_signal_and_stream_clock() {
        let fixture = fixture(/*text_only*/ false);
        let model = fixture.faux_a.get_model();
        fixture
            .faux_a
            .set_responses(vec![error_step("503 Service Unavailable")]);
        let seen = Arc::new(Mutex::new(None));
        let record = Arc::clone(&seen);
        fixture.faux_b.set_responses(vec![FauxResponseStep::factory(
            move |_context, options, _state, _model| {
                let request = options.map(|options| &options.stream.request);
                *record.lock().unwrap_or_else(poisoned) = Some((
                    request.is_some_and(|request| request.signal.is_some()),
                    request.is_some_and(|request| request.stream_clock.is_some()),
                ));
                Ok(faux_assistant_message(
                    "backup answer",
                    FauxAssistantMessageOptions::default(),
                ))
            },
        )]);
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        assert_eq!(message.stop_reason, StopReason::Stop, "{message:?}");
        assert_eq!(
            *seen.lock().unwrap_or_else(poisoned),
            Some((true, true)),
            "the sibling attempt carries the signal and the stream clock"
        );
    }

    #[tokio::test]
    async fn a_provider_outage_without_candidates_surfaces_the_failure() {
        // faux_b serves a different model id, so the outage has no failover
        // candidate and the primary's failure surfaces.
        let fixture = fixture_with(/*text_only*/ false, "solo-1");
        let model = fixture.faux_a.get_model();
        fixture
            .faux_a
            .set_responses(vec![error_step("503 Service Unavailable")]);
        let mut events = fixture.runtime.subscribe();
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        assert_eq!(message.stop_reason, StopReason::Error);
        assert_eq!(
            message.error_message.as_deref(),
            Some("503 Service Unavailable")
        );
        assert!(events.try_recv().is_err(), "no switch event: {message:?}");
        assert_eq!(fixture.runtime.quota_park(), None);
    }

    /// Declares api-key auth and resolves no credential: a built-in
    /// provider the user never configured (`cloudflare-ai-gateway` without
    /// `CLOUDFLARE_API_KEY`).
    struct Unconfigured;

    impl eukhe_ai::auth::ApiKeyAuth for Unconfigured {
        // The trait returns a borrowed name; this one is a literal.
        #[allow(clippy::unnecessary_literal_bound)]
        fn name(&self) -> &str {
            "Unconfigured"
        }

        fn resolve(
            &self,
            _input: eukhe_ai::auth::ApiKeyResolveInput,
        ) -> futures::future::BoxFuture<
            '_,
            Result<Option<eukhe_ai::auth::AuthResult>, eukhe_ai::utils::diagnostics::Thrown>,
        > {
            Box::pin(async { Ok(None) })
        }
    }

    /// Regression: the failover chain took every provider that declares an
    /// auth method (every built-in one) as configured, so an outage of a
    /// session on `anthropic/claude-opus-5-5` (OAuth) re-routed to
    /// `cloudflare-ai-gateway/claude-opus-5-5`, which has no key: the turn
    /// failed with "No API key for provider: cloudflare-ai-gateway" and
    /// the session's own provider's failure was lost. A sibling without
    /// credentials is no failover candidate.
    #[tokio::test]
    async fn a_sibling_without_credentials_never_receives_the_request() {
        let fixture = fixture(/*text_only*/ false);
        let mut sibling = (*fixture.models.get_provider("faux-b").expect("faux-b")).clone();
        sibling.auth = eukhe_ai::auth::ProviderAuth {
            api_key: Some(Arc::new(Unconfigured)),
            oauth: None,
        };
        fixture.models.set_provider(sibling);
        let model = fixture.faux_a.get_model();
        fixture
            .faux_a
            .set_responses(vec![error_step("503 Service Unavailable")]);
        fixture
            .faux_b
            .set_responses(vec![FauxResponseStep::Message(Box::new(
                faux_assistant_message("backup answer", FauxAssistantMessageOptions::default()),
            ))]);
        let mut events = fixture.runtime.subscribe();
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        assert_eq!(
            (
                message.provider.as_str(),
                message.stop_reason,
                message.error_message.as_deref()
            ),
            ("faux-a", StopReason::Error, Some("503 Service Unavailable"))
        );
        assert_eq!(switches(&mut events), Vec::<(String, u64)>::new());
        assert_eq!(fixture.faux_b.get_pending_response_count(), 1);
    }

    /// Regression (user decision Q1/Q2, 2026-10-22): the primary fails, the
    /// failover's backup fails too. The request surfaces the primary's own
    /// latest failure, as the primary's, and one line names the backup
    /// tried with its error; before, the backup's error replaced it.
    #[tokio::test]
    async fn a_failed_failover_surfaces_the_primary_error_and_names_the_backup() {
        let fixture = fixture(/*text_only*/ false);
        let model = fixture.faux_a.get_model();
        fixture
            .faux_a
            .set_responses(vec![error_step("503 Service Unavailable")]);
        fixture
            .faux_b
            .set_responses(vec![error_step("401 invalid x-api-key")]);
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        assert_eq!(
            (
                message.stop_reason,
                message.provider.as_str(),
                message.error_message.as_deref()
            ),
            (
                StopReason::Error,
                "faux-a",
                Some(
                    "503 Service Unavailable (failover to faux-b/shared-1 failed too: 401 invalid x-api-key)"
                )
            )
        );
    }

    /// The primary's far-reset quota block survives a backup's own failure:
    /// the session parks on the primary's reset (the a2bba960e class with
    /// the credentials fixed), and the backup is named.
    #[tokio::test]
    async fn a_failed_failover_parks_on_the_primary_quota() {
        let fixture = fixture(/*text_only*/ false);
        let model = fixture.faux_a.get_model();
        fixture.faux_a.set_responses(vec![quota_step(3_600_000)]);
        fixture
            .faux_b
            .set_responses(vec![error_step("401 invalid x-api-key")]);
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        let text = message.error_message.as_deref().unwrap_or_default();
        assert!(
            fixture.runtime.quota_park().is_some()
                && text.contains("429 rate limit")
                && text
                    .ends_with("(failover to faux-b/shared-1 failed too: 401 invalid x-api-key)"),
            "{text}"
        );
    }

    /// User decision Q3: a backup's own quota block never parks the
    /// session. The request returns to the primary, which fails again: the
    /// primary's LATEST failure surfaces (Q1) and names the backup.
    #[tokio::test]
    async fn a_backup_quota_block_never_parks() {
        let settings = serde_json::json!({
            "retry": { "failover": { "baseDelayMs": 1, "maxDelayMs": 4 } }
        });
        let fixture = fixture_set(/*text_only*/ false, "shared-1", &settings);
        let model = fixture.faux_a.get_model();
        fixture.faux_a.set_responses(vec![
            error_step("503 Service Unavailable"),
            error_step("503 still down"),
        ]);
        fixture.faux_b.set_responses(vec![quota_step(3_600_000)]);
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        assert_eq!(
            (
                fixture.runtime.quota_park().is_none(),
                message.error_message.as_deref()
            ),
            (
                true,
                Some("503 still down (failover to faux-b/shared-1 failed too: 429 rate limit)")
            )
        );
    }

    /// Regression (FLOW's law drill on a1a682254): the primary's quota
    /// block switched to a backup whose `pending` terminal ended the
    /// request; the backup's terminal surfaced with no backup named, no
    /// park, and an `auto_retry_end {success: true}`. A `pending` terminal
    /// after a switch ends like a failure: the primary's quota parks, the
    /// backup is named, and no recovery is reported.
    #[tokio::test]
    async fn a_pending_backup_after_a_switch_parks_on_the_primary_quota() {
        let fixture = fixture(/*text_only*/ false);
        let model = fixture.faux_a.get_model();
        fixture.faux_a.set_responses(vec![quota_step(3_600_000)]);
        let mut pending = faux_assistant_message("", FauxAssistantMessageOptions::default());
        pending.stop_reason = StopReason::Pending;
        fixture
            .faux_b
            .set_responses(vec![FauxResponseStep::Message(Box::new(pending))]);
        let mut events = fixture.runtime.subscribe();
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        let mut recovered = false;
        while let Ok(event) = events.try_recv() {
            if let ProviderWireEvent::AutoRetryEnd { success: true, .. } = event {
                recovered = true;
            }
        }
        let text = message.error_message.as_deref().unwrap_or_default();
        assert!(
            fixture.runtime.quota_park().is_some()
                && !recovered
                && text.contains("429 rate limit")
                && text.contains(" (failover to faux-b/shared-1 failed too: ")
                && text.ends_with(')'),
            "parked {:?}, recovered {recovered}: {text}",
            fixture.runtime.quota_park().is_some()
        );
    }

    /// The switches a request made: each sibling's reference and wait.
    fn switches(events: &mut broadcast::Receiver<ProviderWireEvent>) -> Vec<(String, u64)> {
        let mut seen = Vec::new();
        while let Ok(event) = events.try_recv() {
            match event {
                ProviderWireEvent::AutoRetryStart {
                    backup_model,
                    delay_ms,
                    ..
                } => seen.push((backup_model, delay_ms)),
                ProviderWireEvent::AutoRetryEnd { .. } | ProviderWireEvent::PromptProgress(_) => {}
            }
        }
        seen
    }

    /// Regression (audit H3): two failing providers ping-ponged eight
    /// times with no wait and the failover delay settings were never read.
    /// Each provider is now tried once at once; a return waits the
    /// backoff (`retry.failover.baseDelayMs`, doubled, capped at
    /// `maxDelayMs`), and the switches stop at `maxRetries`.
    #[tokio::test]
    async fn failover_returns_to_a_provider_only_after_its_backoff() {
        let settings = serde_json::json!({
            "retry": { "failover": { "maxRetries": 6, "baseDelayMs": 1, "maxDelayMs": 4 } }
        });
        let fixture = fixture_set(/*text_only*/ false, "shared-1", &settings);
        let model = fixture.faux_a.get_model();
        let outage = || {
            (0..8)
                .map(|_| error_step("503 Service Unavailable"))
                .collect()
        };
        fixture.faux_a.set_responses(outage());
        fixture.faux_b.set_responses(outage());
        let mut events = fixture.runtime.subscribe();
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        assert_eq!(message.stop_reason, StopReason::Error);
        let (a, b) = ("faux-a/shared-1".to_owned(), "faux-b/shared-1".to_owned());
        assert_eq!(
            switches(&mut events),
            [
                (b.clone(), 0),
                (a.clone(), 1),
                (b.clone(), 2),
                (a.clone(), 4),
                (b, 4),
                (a, 4),
            ]
        );
    }

    /// With no return backoff, a request that tried every provider of its
    /// chain gives up instead of sending it again at once (audit H3).
    #[tokio::test]
    async fn failover_never_returns_at_once() {
        let settings = serde_json::json!({ "retry": { "failover": { "baseDelayMs": 0 } } });
        let fixture = fixture_set(/*text_only*/ false, "shared-1", &settings);
        let model = fixture.faux_a.get_model();
        let outage = || {
            (0..8)
                .map(|_| error_step("503 Service Unavailable"))
                .collect()
        };
        fixture.faux_a.set_responses(outage());
        fixture.faux_b.set_responses(outage());
        let mut events = fixture.runtime.subscribe();
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        assert_eq!(
            (
                message.stop_reason,
                switches(&mut events),
                fixture.faux_a.get_pending_response_count(),
                fixture.faux_b.get_pending_response_count(),
            ),
            (
                StopReason::Error,
                vec![("faux-b/shared-1".to_owned(), 0)],
                7,
                7
            )
        );
    }

    /// A quota failure (the stream-failure diagnostic's `rate_limit` kind)
    /// with a provider-reported reset beyond the bounded wait.
    fn quota_step(reset_ms: u64) -> FauxResponseStep {
        FauxResponseStep::factory(move |_, _, _, _| {
            let mut details = JsonObject::new();
            details.insert("kind".to_owned(), serde_json::json!("rate_limit"));
            details.insert("retryAfterMs".to_owned(), serde_json::json!(reset_ms));
            let mut message: AssistantMessage =
                faux_assistant_message("", FauxAssistantMessageOptions::default());
            message.stop_reason = StopReason::Error;
            message.error_message = Some("429 rate limit".to_owned());
            message.diagnostics = Some(vec![eukhe_types::pi_ai::AssistantMessageDiagnostic {
                kind: "provider_stream_failure".to_owned(),
                timestamp: 0,
                error: None,
                details: Some(details),
            }]);
            message.usage = Usage::default();
            Ok(message)
        })
    }

    #[tokio::test]
    async fn a_quota_failure_with_a_far_reset_parks_until_the_reset() {
        // No sibling provider: the quota failure reaches the park seam.
        let fixture = fixture_with(/*text_only*/ false, "other-1");
        let model = fixture.faux_a.get_model();
        // A reset one hour out exceeds the default bounded wait (60s).
        fixture.faux_a.set_responses(vec![quota_step(3_600_000)]);
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        let parked = message.error_message.as_deref().unwrap_or_default();
        assert!(
            parked.contains("Session parked until")
                && parked.contains("will resume automatically (retry.provider.waitForUsage.pauseUntilReset): 429 rate limit"),
            "{parked}"
        );
        assert!(fixture.runtime.quota_park().is_some());
        // The wake job is armed in the session's scheduled-jobs store.
        let store = AgentCronJobStore::new(fixture.dir.path().join("agent").join("cron-jobs.json"));
        let wakes = store
            .list()
            .into_iter()
            .filter(|job| job.label.as_deref() == Some(QUOTA_RESUME_CRON_LABEL))
            .collect::<Vec<_>>();
        assert_eq!(wakes.len(), 1, "{:?}", store.list());
        assert_eq!(wakes[0].status, JobStatus::Active);
        assert_eq!(wakes[0].prompt, QUOTA_RESUME_MARKER_TEXT);
        // Regression (audit H4): the park dropped the failure's diagnostics,
        // so its text ("429 rate limit") read as retryable and the harness
        // resent the request to the blocked provider. The server's wait
        // survives, the park adds its own, and no retry follows.
        let kinds: Vec<&str> = message
            .diagnostics
            .iter()
            .flatten()
            .map(|diagnostic| diagnostic.kind.as_str())
            .collect();
        assert_eq!(
            (
                kinds,
                eukhe_ai::utils::retry::server_retry_after_ms(&message),
                is_retryable_assistant_error(&message),
            ),
            (
                vec!["provider_stream_failure", QUOTA_PARK_DIAGNOSTIC],
                Some(3_600_000.0),
                false
            )
        );
    }

    #[tokio::test]
    async fn a_quota_reset_inside_the_bounded_wait_keeps_the_failure() {
        let fixture = fixture_with(/*text_only*/ false, "other-1");
        let model = fixture.faux_a.get_model();
        fixture.faux_a.set_responses(vec![quota_step(1_000)]);
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        assert_eq!(message.error_message.as_deref(), Some("429 rate limit"));
        assert_eq!(fixture.runtime.quota_park(), None);
    }

    #[tokio::test]
    async fn images_on_a_text_only_model_fail_with_the_image_model_refusal() {
        let fixture = fixture(/*text_only*/ true);
        let model = fixture.faux_a.get_model();
        fixture
            .faux_a
            .set_responses(vec![FauxResponseStep::Message(Box::new(
                faux_assistant_message("never reached", FauxAssistantMessageOptions::default()),
            ))]);
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Blocks(vec![
                eukhe_types::pi_ai::UserContentBlock::Text(TextContent::new("look")),
                eukhe_types::pi_ai::UserContentBlock::Image(ImageContent {
                    data: "aGk=".to_owned(),
                    mime_type: "image/png".to_owned(),
                }),
            ]))],
        )
        .await;
        assert_eq!(message.stop_reason, StopReason::Error);
        let refusal = message.error_message.as_deref().unwrap_or_default();
        assert!(
            refusal.starts_with("This turn attaches images, but the selected model (faux-a/shared-1) does not accept image input.")
                && refusal.contains("Set imageModel in settings.json"),
            "{refusal}"
        );
        assert_eq!(fixture.faux_a.get_pending_response_count(), 1);
    }

    #[tokio::test]
    async fn a_successful_call_resumes_a_parked_session() {
        let fixture = fixture_with(/*text_only*/ false, "other-1");
        let model = fixture.faux_a.get_model();
        // No harness is attached: the early-resume marker submission is
        // skipped, but the park clears and the resume row path runs.
        fixture
            .runtime
            .inner
            .park
            .lock()
            .unwrap_or_else(poisoned)
            .clone_from(&Some(ParkDocState {
                resume_at_ms: now_millis() + 3_600_000,
                park_count: 1,
                job_id: None,
                provider: Some("faux-a".to_owned()),
                wake_retries: 0,
            }));
        assert!(fixture.runtime.quota_park().is_some());
        fixture
            .faux_a
            .set_responses(vec![FauxResponseStep::Message(Box::new(
                faux_assistant_message("back", FauxAssistantMessageOptions::default()),
            ))]);
        let message = drive(
            &fixture.models,
            &model,
            vec![user_message(UserContent::Text("hello".to_owned()))],
        )
        .await;
        assert_eq!(message.stop_reason, StopReason::Stop);
        assert_eq!(fixture.runtime.quota_park(), None);
    }

    /// The serving stream's prompt progress reaches the runtime's wire
    /// subscribers and still streams out to the caller.
    #[tokio::test]
    async fn prompt_progress_goes_to_the_wire_and_the_caller() {
        let fixture = fixture(/*text_only*/ false);
        let model = fixture.faux_a.get_model();
        let progress = PromptProgress {
            total: 4_096,
            cache: 1_024,
            processed: 2_048,
            time_ms: 350,
        };
        let dispatch: OriginalDispatch = Arc::new(move |_model, _context| {
            let stream = create_assistant_message_event_stream();
            let message = faux_assistant_message("ok", FauxAssistantMessageOptions::default());
            stream.push(AssistantMessageEvent::Start {
                partial: message.clone().into(),
            });
            stream.push(AssistantMessageEvent::PromptProgress {
                progress,
                partial: message.clone().into(),
            });
            stream.push(AssistantMessageEvent::Done {
                reason: DoneReason::Stop,
                message: message.clone(),
            });
            stream.end(Some(message));
            stream
        });
        let mut events = fixture.runtime.subscribe();
        let kinds: Vec<&str> = dispatch_request(
            Arc::clone(&fixture.runtime.inner),
            model,
            TranscriptContext::from_normalized_messages(vec![user_message(UserContent::Text(
                "hello".to_owned(),
            ))]),
            dispatch,
            CarriedOptions::default(),
            /*simple*/ true,
        )
        .events()
        .map(|event| event.type_name())
        .collect()
        .await;
        assert_eq!(kinds, ["start", "prompt_progress", "done"]);
        assert_eq!(
            events.try_recv().expect("the progress event"),
            ProviderWireEvent::PromptProgress(progress)
        );
        assert!(events.try_recv().is_err());
    }
}
