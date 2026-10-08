//! The provider runtime of a durable eukhe session: the eukhe provider
//! behaviors the generic Harness cannot own, wrapped around every
//! provider's stream functions so the durable generation only ever sees the
//! `Models` collection.
//!
//! - Image-model routing ([`super::image_route`]): a request attaching
//!   image blocks on a text-only session model routes to
//!   `settings.imageModel`, or fails with the old engine's actionable
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
//!   path, and [`ProviderRuntime::is_quota_parked`] for the session
//!   summary. A successful model call while parked resumes (cancelling the
//!   wake); an early resume queues the resume marker.
//! - Request timing ([`super::timing`]): per-request phase entries in the
//!   shared JSONL diagnostic log.
//!
//! Wrapping happens once per collection at session open
//! ([`ProviderRuntime::install`]), on the session's own collection; the
//! daemon's faux-script sessions share one collection across workers and
//! stay unwrapped, matching the old engine's no-failover faux rule.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::delta::Draft;
use eukhe_chord::json::{from_json, to_json};
use eukhe_durable::harness::json::assign_json;
use eukhe_durable::harness::types::InputSubmissionDraft;
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::types::{ConversationId, TypedEntryDraft};
use eukhe_pi_ai::api::{StreamFn, StreamSimpleFn};
use eukhe_pi_ai::models::Models;
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_pi_ai::utils::event_stream::{
    create_assistant_message_event_stream, AssistantMessageEventStream,
};
use eukhe_pi_ai::utils::retry::is_retryable_assistant_error;
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, DoneReason, ErrorReason, Message, Model, StopReason,
    TranscriptContext, Usage, UserContent, UserContentBlock,
};
use futures::{FutureExt, StreamExt};
use serde::Serialize;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::broadcast;

use super::failover::{
    failover_candidates, model_reference, ProviderFailoverPolicy, DEFAULT_PROVIDER_FAILOVER_POLICY,
    MAX_TOTAL_PROVIDER_RETRIES,
};
use super::image_route::{self, ImageRoute};
use super::park::{
    is_quota_block_failure, park_entry_data, provider_park_decision,
    quota_already_parked_final_error, quota_failure_reset_ms, quota_parked_final_error,
    resume_entry_data, NoParkReason, ParkDocState, ProviderParkDecision, ProviderParkPolicy,
    DEFAULT_PROVIDER_PARK_POLICY, PARK_DOC, PROVIDER_QUOTA_PARK_ENTRY, PROVIDER_QUOTA_RESUME_ENTRY,
    QUOTA_RESUME_CRON_LABEL, QUOTA_RESUME_MARKER_TEXT,
};
use super::timing::{self, RequestTiming};
use crate::cron::store::{AgentCronJobStore, CreateAgentCronJobInput};
use crate::cron::JobStatus;
use crate::durable::entries::{CustomStateData, CUSTOM_STATE_ENTRY};
use crate::durable::rlm::now_millis;
use crate::durable::HostDeps;
use crate::session_engine::host_requests::{RlmHeartbeatMutation, SessionBinding};
use crate::settings::SettingsManager;

const SWITCH_BUDGET: u32 = MAX_TOTAL_PROVIDER_RETRIES;

/// Wire-shaped provider events of the runtime (the old engine's
/// `auto_retry_*` failover vocabulary the durable Harness does not emit):
/// broadcast to every subscriber; the daemon worker translates them onto
/// the wire.
#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ProviderWireEvent {
    /// `auto_retry_start` with `reason: "backup"`: the failed request
    /// re-routes to `backup_model` ("provider/model-id") immediately.
    AutoRetryStart {
        attempt: u32,
        max_attempts: u32,
        delay_ms: u64,
        error_message: String,
        reason: String,
        backup_model: Option<String>,
    },
    /// `auto_retry_end` after a failover episode: `restored_model` is the
    /// "provider/model-id" primary a successful switch restored.
    AutoRetryEnd {
        success: bool,
        attempt: u32,
        #[serde(skip_serializing_if = "Option::is_none")]
        final_error: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        restored_model: Option<String>,
    },
}

/// One underlying provider dispatch of the wrapped chain: the provider's
/// original stream function with this request's options bound.
type OriginalDispatch =
    Arc<dyn Fn(&Model, &TranscriptContext) -> AssistantMessageEventStream + Send + Sync>;

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
                let dispatch: OriginalDispatch = {
                    let original = original_stream.clone();
                    let options = options;
                    Arc::new(move |model, context| original(model, context, options.clone()))
                };
                dispatch_request(inner, model.clone(), context.clone(), dispatch, false)
            });
            let weak = Arc::downgrade(&runtime.inner);
            provider.stream_simple = Arc::new(move |model, context, options| {
                let Some(inner) = weak.upgrade() else {
                    return original_simple(model, context, options);
                };
                let dispatch: OriginalDispatch = {
                    let original = original_simple.clone();
                    let options = options;
                    Arc::new(move |model, context| original(model, context, options.clone()))
                };
                dispatch_request(inner, model.clone(), context.clone(), dispatch, true)
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

    /// The runtime's wire events (the old `auto_retry_*` failover
    /// vocabulary); a late subscriber sees only later events.
    #[must_use]
    pub fn subscribe(&self) -> broadcast::Receiver<ProviderWireEvent> {
        self.inner.events.subscribe()
    }

    /// True while the session is parked waiting out a provider-reported
    /// usage reset (TS `session.isQuotaParked`).
    #[must_use]
    pub fn is_quota_parked(&self) -> bool {
        self.inner.park.lock().unwrap_or_else(poisoned).is_some()
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
    simple: bool,
) -> AssistantMessageEventStream {
    let out = create_assistant_message_event_stream();
    let output = out.clone();
    tokio::spawn(async move {
        run_request(inner, model, context, original, simple, output).await;
    });
    out
}

/// The wrapped request's driver.
async fn run_request(
    inner: Arc<Inner>,
    model: Model,
    context: TranscriptContext,
    original: OriginalDispatch,
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
    let mut dispatch = original;
    let mut switches = 0u32;
    loop {
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
                _ => out.push(event),
            }
        }
        let Some(message) = terminal else {
            // A stream that ends without a terminal event keeps the
            // provider's own contract breach: surface nothing further.
            out.end(None);
            return;
        };
        let retryable =
            message.stop_reason == StopReason::Error && is_retryable_assistant_error(&message);
        let next = if retryable && failover.enabled {
            next_candidate(&inner, &serving, &settings, switches, &failover)
        } else {
            None
        };
        let Some(candidate) = next else {
            if switches > 0
                && !matches!(message.stop_reason, StopReason::Error | StopReason::Aborted)
            {
                let _ = inner.events.send(ProviderWireEvent::AutoRetryEnd {
                    success: true,
                    attempt: switches,
                    final_error: None,
                    restored_model: Some(model_reference(&primary)),
                });
            }
            if matches!(message.stop_reason, StopReason::Error | StopReason::Pending) {
                finish_failure(inner, out, timing_clock, message, &settings).await;
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
            resume_if_parked(&inner, &context).await;
            out.push(AssistantMessageEvent::Done {
                reason: done_reason_of(&message),
                message,
            });
            out.end(None);
            return;
        };
        switches += 1;
        let _ = inner.events.send(ProviderWireEvent::AutoRetryStart {
            attempt: switches,
            max_attempts: failover.max_switches,
            delay_ms: 0,
            error_message: final_error_of(&message),
            reason: "backup".to_owned(),
            backup_model: Some(model_reference(&candidate)),
        });
        // The re-routed request dispatches through the sibling provider's
        // original stream function (never its wrapper).
        let sibling = original_dispatch(&inner, &candidate, simple);
        serving = candidate;
        dispatch = sibling;
    }
}

/// The original stream function of `model`'s provider, options-free: a
/// failover re-dispatch builds fresh options per provider contract (the
/// provider-neutral defaults; API-specific keys ride `extra` on the full
/// seam, which the sibling provider would not honor identically anyway).
fn original_dispatch(inner: &Inner, model: &Model, simple: bool) -> OriginalDispatch {
    let original = inner
        .originals
        .lock()
        .unwrap_or_else(poisoned)
        .get(&model.provider)
        .cloned();
    Arc::new(
        move |model: &Model, context: &TranscriptContext| match &original {
            Some((stream, stream_simple)) if simple => {
                stream_simple(model, context, SimpleStreamOptions::default())
            }
            Some((stream, _)) => stream(
                model,
                context,
                eukhe_pi_ai::types::ProviderStreamOptions::default(),
            ),
            None => create_assistant_message_event_stream(),
        },
    )
}

/// Terminal failure: the quota-park seam, then the failure surfaces.
async fn finish_failure(
    inner: Arc<Inner>,
    out: AssistantMessageEventStream,
    mut timing_clock: Option<RequestTiming>,
    mut message: AssistantMessage,
    settings: &SettingsManager,
) {
    if let Some(clock) = timing_clock.as_mut() {
        clock.failed(&message);
    }
    if let Some(status) = park_for_quota_reset(&inner, &message, settings).await {
        message.error_message = Some(status);
        message.diagnostics = None;
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

/// The `requestTiming` settings flag of the session's merged settings.
fn request_timing_flag(settings: &SettingsManager) -> bool {
    settings.settings().request_timing.unwrap_or(false)
}

/// The failover policy from raw settings (`retry.failover`): the old
/// per-provider retry budget maps to the Harness's durable retries, so only
/// the enabled flag and the (ceiling-clamped) switch budget apply.
fn failover_policy(settings: &SettingsManager) -> ProviderFailoverPolicy {
    let defaults = DEFAULT_PROVIDER_FAILOVER_POLICY;
    let Some(failover) = settings
        .settings()
        .retry
        .as_ref()
        .and_then(|retry| retry.failover.as_ref())
    else {
        return defaults;
    };
    ProviderFailoverPolicy {
        enabled: failover.enabled.unwrap_or(defaults.enabled),
        max_switches: failover
            .max_retries
            .map_or(defaults.max_switches, |retries| {
                u32::try_from(retries)
                    .unwrap_or(SWITCH_BUDGET)
                    .min(SWITCH_BUDGET)
            }),
    }
}

/// The quota-park policy from raw settings (`retry.provider.waitForUsage`).
fn park_policy(settings: &SettingsManager) -> ProviderParkPolicy {
    let defaults = DEFAULT_PROVIDER_PARK_POLICY;
    let Some(wait) = settings
        .settings()
        .retry
        .as_ref()
        .and_then(|retry| retry.provider.as_ref())
        .and_then(|provider| provider.wait_for_usage.as_ref())
    else {
        return defaults;
    };
    ProviderParkPolicy {
        pause_until_reset: wait.pause_until_reset.unwrap_or(defaults.pause_until_reset),
        max_pause_ms: wait.max_pause_ms.unwrap_or(defaults.max_pause_ms),
        max_parks: wait.max_parks.map_or(defaults.max_parks, |parks| {
            u32::try_from(parks).unwrap_or(defaults.max_parks)
        }),
    }
}

/// The bounded-wait cap of the quick-retry policy (the park seam's
/// reset-too-far bound).
fn wait_cap_ms(settings: &SettingsManager) -> u64 {
    settings
        .settings()
        .retry
        .as_ref()
        .and_then(|retry| retry.provider.as_ref())
        .and_then(|provider| provider.max_retry_delay_ms)
        .unwrap_or(60_000)
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
    }
}

/// The next failover candidate, when the switch budget allows one: the
/// candidate chain of the serving model over the configured catalog
/// (credential-configured providers only), allowlisted like every other
/// model resolution.
fn next_candidate(
    inner: &Inner,
    serving: &Model,
    settings: &SettingsManager,
    switches: u32,
    policy: &ProviderFailoverPolicy,
) -> Option<Model> {
    if switches >= policy.max_switches {
        return None;
    }
    let available = inner
        .models
        .get_models(None)
        .into_iter()
        .filter(|model| catalog_available(inner, model))
        .collect::<Vec<_>>();
    failover_candidates(serving, &available)
        .into_iter()
        .find(|candidate| allowlist_allows(settings, candidate))
}

/// A provider with no configured auth never receives a failover switch (the
/// old chain walked the auth-configured catalog).
fn catalog_available(inner: &Inner, model: &Model) -> bool {
    inner
        .models
        .get_provider(&model.provider)
        .is_some_and(|provider| provider.auth.api_key.is_some() || provider.auth.oauth.is_some())
}

/// The daemon `allowedModels` gate over one candidate (fail closed on an
/// unreadable policy: no failover may bypass the configured allowlist).
fn allowlist_allows(settings: &SettingsManager, candidate: &Model) -> bool {
    super::enforce_allowlist(settings, &model_reference(candidate)).is_ok()
}

// ---------------------------------------------------------------------------
// Quota park
// ---------------------------------------------------------------------------

/// Restore a persisted park at open (the old engine's build-time
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
/// parked status for the surfaced message; `None` keeps the give-up.
async fn park_for_quota_reset(
    inner: &Arc<Inner>,
    message: &AssistantMessage,
    settings: &SettingsManager,
) -> Option<String> {
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
                return Some(quota_already_parked_final_error(park.resume_at_ms, &error));
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
            return Some(quota_already_parked_final_error(park.resume_at_ms, &error));
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
    Some(quota_parked_final_error(&abort, resume_at_ms, &error))
}

/// A parked session completed a model call: the quota is back. Clear the
/// park (cancelling any pending wake), record the resumed transition, and —
/// unless this success WAS the wake probe — queue the resume marker so the
/// interrupted task continues right away (TS `_completeQuotaParkResume`).
async fn resume_if_parked(inner: &Arc<Inner>, context: &TranscriptContext) {
    if inner.park.lock().unwrap_or_else(poisoned).is_none() {
        return;
    }
    let wake_probe = context
        .messages()
        .last()
        .is_some_and(|message| match message {
            Message::User(user) => user_content_text(&user.content) == QUOTA_RESUME_MARKER_TEXT,
            _ => false,
        });
    clear_park(inner, if wake_probe { "wake" } else { "early" }).await;
    if wake_probe {
        return;
    }
    // Early resume: the marker continues the interrupted task now.
    if let Some(root) = inner.deps.harness.root() {
        let _ = root
            .submit(
                InputSubmissionDraft::new(QUOTA_RESUME_MARKER_TEXT.to_owned()),
                &BACKGROUND_CONTEXT,
            )
            .await;
    }
}

/// The concatenated text of a user content (the wake-probe comparison).
fn user_content_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.clone()),
                UserContentBlock::Image { .. } => None,
            })
            .collect(),
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
            source: Some("quota_resume".to_owned()),
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

/// Cancel a pending wake job (a completed — fired — job stays).
fn cancel_wake_job(inner: &Inner, job_id: &str) {
    let (store, _) = cron_wiring(inner);
    if store
        .list()
        .iter()
        .any(|job| job.id == job_id && job.status == JobStatus::Active)
    {
        let _ = store.cancel(job_id, now_millis());
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
    use eukhe_pi_ai::models::{
        create_models as create_pi_models, CreateModelsOptions, ModelsSimpleStreamOptions,
    };
    use eukhe_pi_ai::providers::faux::{
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
        let dir = tempfile::tempdir().expect("tempdir");
        let agent_dir = dir.path().join("agent");
        let cwd = dir.path().join("cwd");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");
        std::fs::create_dir_all(&cwd).expect("cwd");
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
                    reason,
                    backup_model: Some(backup_model),
                    ..
                } if reason == "backup" && backup_model == "faux-b/shared-1"
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
        assert!(!fixture.runtime.is_quota_parked());
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
        assert!(fixture.runtime.is_quota_parked());
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
        assert!(!fixture.runtime.is_quota_parked());
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
        assert!(fixture.runtime.is_quota_parked());
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
        assert!(!fixture.runtime.is_quota_parked());
    }
}
