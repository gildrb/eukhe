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
//! - Model fallback ([`super::fallback`]): a request whose model cannot go
//!   on (the run's retries ran out, its provider's login expired and the
//!   refresh failed, its usage limit holds past the bounded wait) moves to
//!   the next model the user configured whose provider has credentials
//!   (`laws/fallback.bend`); every move is on the wire as a backup switch
//!   and in [`ProviderRuntime::model_moves`] for the run's report.
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
use eukhe_ai::auth::{
    AuthOperationOptions, AuthResolutionOverrides, LoginOptions, ModelAuth, OAuthAuth,
    OAuthCredential, ProviderAuthInteraction, CREDENTIAL_STORE_FAILED,
};
use eukhe_ai::models::Models;
use eukhe_ai::types::{
    ProviderRequestOptions, ProviderStreamOptions, SimpleStreamOptions, StreamOptions,
};
use eukhe_ai::utils::diagnostics::Thrown;
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
    Message, Modality, Model, PromptProgress, StopReason, TranscriptContext, Usage, UserContent,
    UserContentBlock,
};
use futures::future::BoxFuture;
use futures::{FutureExt, StreamExt};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;
use tokio::sync::broadcast;

use eukhe_bend::rules::fallback::Why;
use eukhe_bend::rules::retry::{Switch, Tried};

use super::accounts::{AccountBook, AccountFailure, AccountStep};
use super::failover::{failover_candidates, model_reference, next_switch, ProviderFailoverPolicy};
use super::fallback::{self, Step};
use super::image_route::{self, ImageRoute};
use super::park::{
    is_quota_block_failure, park_entry_data, provider_park_decision,
    quota_already_parked_final_error, quota_failure_reset_ms, quota_parked_final_error,
    resume_entry_data, NoParkReason, ParkDocState, ParkWake, ParkedWait, ProviderParkDecision,
    ProviderParkPolicy, DEFAULT_PROVIDER_PARK_POLICY, PARK_DOC, PROVIDER_QUOTA_PARK_ENTRY,
    PROVIDER_QUOTA_RESUME_ENTRY, QUOTA_RESUME_CRON_LABEL, QUOTA_RESUME_MARKER_TEXT,
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

/// Send `context` to `model` through `send`. A remote model
/// (`privacy.anonymizeRemote`, `eukhe_ai::privacy`) gets the scrubbed
/// context, numbered in `privacy`, the session's token map, and its
/// answer comes back restored with that map, so the transcript, the user
/// and every tool see the real strings and no other session's value.
/// Every dispatch of the wrapped chain (the primary and each failover
/// sibling) sends through here once, against the model it reaches, so no
/// caller (turns, the compactor, branch summaries, side questions) can
/// send raw text to a remote endpoint. Loopback models see the raw text.
fn send_private(
    settings: &Arc<crate::durable::EukheSettings>,
    privacy: &eukhe_ai::privacy::TokenMap,
    model: &Model,
    context: &TranscriptContext,
    send: impl FnOnce(&TranscriptContext) -> AssistantMessageEventStream,
) -> AssistantMessageEventStream {
    let manager = settings.manager();
    if !manager.get_privacy_anonymize_remote() || eukhe_ai::privacy::is_local(&model.base_url) {
        return send(context);
    }
    let scrubber = eukhe_ai::privacy::Scrubber::new(&manager.get_privacy_terms(), privacy.clone());
    let outbound = TranscriptContext::from_normalized_messages(
        scrubber.scrub_messages(context.clone().into_messages()),
    );
    privacy.restore_stream(send(&outbound))
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
    /// The session's privacy token map (`privacy.anonymizeRemote`): it
    /// opens empty with the session and goes with it.
    privacy: eukhe_ai::privacy::TokenMap,
    /// The retryable failures in a row of each model a request asked for
    /// ("provider/model-id"); an answer of the model clears its count.
    failures: Mutex<HashMap<String, u64>>,
    /// The providers whose stored login expired and could not be
    /// refreshed, with the refresh's error ([`LoginWatch`]): the next
    /// request to one fails without leaving and goes to another model.
    logins: Arc<Mutex<HashMap<String, String>>>,
    /// The account logins this run found unusable ([`DeadLogin`]).
    dead_logins: DeadLogins,
    /// The session's model moves, one per pair of models, oldest first.
    moves: Mutex<Vec<ModelMove>>,
    /// The session's accounts: the account each provider's requests use
    /// ([`AccountBook`]).
    accounts: Arc<AccountBook>,
    /// The session's account switches, oldest first.
    switches: Mutex<Vec<AccountSwitch>>,
}

/// An account's login: its provider id and the account's identity (the
/// account the provider's credential store serves,
/// [`AccountBook::current_identity`]; empty for a provider with no stored
/// account).
type LoginKey = (String, String);

/// The account logins a run found unusable, by account.
type DeadLogins = Arc<Mutex<HashMap<LoginKey, DeadLogin>>>;

/// An account login a request of this run found unusable ([`Why::Login`])
/// and left. It stays unusable for the rest of the run, and is never
/// refreshed again ([`LoginWatch`]), so no request pays another failed
/// refresh. The provider's requests go on with its next account
/// (`laws/account.bend`); once every account of the provider is dead, a
/// later request on it starts on the model the run went on with. A new
/// login of the account clears it.
#[derive(Clone)]
struct DeadLogin {
    /// The login's failure, as the request that left it read it.
    error: String,
    /// The model the run went on with: the latest that answered.
    moved_to: Model,
}

/// The dead login of `provider`'s current account, when every account of
/// the provider (or the one login of a provider with no stored account)
/// is dead for the run: the provider has no login left.
fn provider_dead_login(inner: &Inner, provider: &str) -> Option<DeadLogin> {
    let accounts = inner.accounts.accounts(provider);
    let current = inner.accounts.current_identity(provider, &accounts);
    let dead = inner.dead_logins.lock().unwrap_or_else(poisoned);
    let is_dead = |identity: &str| dead.contains_key(&(provider.to_owned(), identity.to_owned()));
    let every = if accounts.is_empty() {
        is_dead(&current)
    } else {
        accounts.iter().all(|account| is_dead(&account.identity))
    };
    if !every {
        return None;
    }
    dead.get(&(provider.to_owned(), current)).cloned()
}

/// Record `provider`'s login found unusable: the account a request just
/// failed on, and each account this session's account rotation found
/// dead ([`AccountBook::is_dead`]).
fn mark_dead_login(inner: &Inner, provider: &str, dead: &DeadLogin) {
    let accounts = inner.accounts.accounts(provider);
    let mut identities = vec![inner.accounts.current_identity(provider, &accounts)];
    identities.extend(
        accounts
            .into_iter()
            .map(|account| account.identity)
            .filter(|identity| inner.accounts.is_dead(provider, identity)),
    );
    let mut dead_logins = inner.dead_logins.lock().unwrap_or_else(poisoned);
    for identity in identities {
        dead_logins.insert((provider.to_owned(), identity), dead.clone());
    }
}

/// One move of the session's requests from the model they asked for to
/// another model the user configured, and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModelMove {
    /// The model the requests asked for ("provider/model-id").
    pub from: String,
    /// The model that took them.
    pub to: String,
    /// Why the first model could not go on, the latest time it moved.
    pub reason: String,
}

impl ModelMove {
    /// The report line of the move.
    #[must_use]
    pub fn text(&self) -> String {
        format!("moved from {} to {}: {}", self.from, self.to, self.reason)
    }
}

/// One switch of a provider's requests to another of its accounts, and
/// why the account before could not go on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccountSwitch {
    /// The provider.
    pub provider: String,
    /// The account that took the requests (its identity, or `account <n>`).
    pub to: String,
    /// Why the account before could not go on.
    pub cause: String,
}

impl AccountSwitch {
    /// The report line of the switch.
    #[must_use]
    pub fn text(&self) -> String {
        format!("switched to account {}: {}", self.to, self.cause)
    }
}

impl ProviderRuntime {
    /// Wrap every provider of `models` with the eukhe provider behaviors,
    /// register the runtime on `deps` (`HostDeps::provider_runtime`), and
    /// start the open-time service that restores a persisted park.
    /// `accounts`: the accounts the collection's credential store serves.
    #[must_use]
    pub fn install(
        models: &Models,
        deps: &Arc<HostDeps>,
        accounts: Arc<AccountBook>,
    ) -> Arc<ProviderRuntime> {
        let (events, _) = broadcast::channel(64);
        let runtime = Arc::new(ProviderRuntime {
            inner: Arc::new(Inner {
                models: models.clone(),
                deps: Arc::clone(deps),
                events,
                park: Mutex::new(None),
                timing: Arc::new(timing::RequestTimingWiring::new(&deps.agent_dir)),
                originals: Mutex::new(HashMap::new()),
                privacy: eukhe_ai::privacy::TokenMap::default(),
                failures: Mutex::new(HashMap::new()),
                logins: Arc::new(Mutex::new(HashMap::new())),
                dead_logins: Arc::new(Mutex::new(HashMap::new())),
                moves: Mutex::new(Vec::new()),
                accounts,
                switches: Mutex::new(Vec::new()),
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
                let carried = CarriedOptions::of(&options.stream.request);
                let dispatch: OriginalDispatch = {
                    let original = original_stream.clone();
                    let settings = Arc::clone(&inner.deps.settings);
                    let privacy = inner.privacy.clone();
                    let options = options;
                    Arc::new(move |model, context| {
                        send_private(&settings, &privacy, model, context, |context| {
                            original(model, context, options.clone())
                        })
                    })
                };
                dispatch_request(
                    inner,
                    model.clone(),
                    context.clone(),
                    dispatch,
                    carried,
                    false,
                )
            });
            let weak = Arc::downgrade(&runtime.inner);
            provider.stream_simple = Arc::new(move |model, context, options| {
                let Some(inner) = weak.upgrade() else {
                    return original_simple(model, context, options);
                };
                let carried = CarriedOptions::of(&options.stream.request);
                let dispatch: OriginalDispatch = {
                    let original = original_simple.clone();
                    let settings = Arc::clone(&inner.deps.settings);
                    let privacy = inner.privacy.clone();
                    let options = options;
                    Arc::new(move |model, context| {
                        send_private(&settings, &privacy, model, context, |context| {
                            original(model, context, options.clone())
                        })
                    })
                };
                dispatch_request(
                    inner,
                    model.clone(),
                    context.clone(),
                    dispatch,
                    carried,
                    true,
                )
            });
            if let Some(oauth) = provider.auth.oauth.take() {
                provider.auth.oauth = Some(Arc::new(LoginWatch {
                    oauth,
                    provider: provider.id.clone(),
                    logins: Arc::clone(&runtime.inner.logins),
                    dead: Arc::clone(&runtime.inner.dead_logins),
                    accounts: Arc::clone(&runtime.inner.accounts),
                }));
            }
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

    /// The session's model moves, oldest first, one per pair of models:
    /// the end of a run reports each.
    #[must_use]
    pub fn model_moves(&self) -> Vec<ModelMove> {
        self.inner.moves.lock().unwrap_or_else(poisoned).clone()
    }

    /// The session's account switches, oldest first: the end of a run
    /// reports each.
    #[must_use]
    pub fn account_switches(&self) -> Vec<AccountSwitch> {
        self.inner.switches.lock().unwrap_or_else(poisoned).clone()
    }

    /// The identity of the account each provider's requests use, for the
    /// providers the session chose one of, by provider.
    #[must_use]
    pub fn pinned_accounts(&self) -> std::collections::BTreeMap<String, String> {
        self.inner.accounts.pins()
    }

    /// The report lines of the session's switches: each account switch,
    /// then each model move (accounts go before models), oldest first.
    #[must_use]
    pub fn switch_report(&self) -> Vec<String> {
        self.account_switches()
            .iter()
            .map(AccountSwitch::text)
            .chain(self.model_moves().iter().map(ModelMove::text))
            .collect()
    }

    /// Wake the live park as its scheduled wake does, for an embedding
    /// that runs no scheduler and waited for the reset itself (a headless
    /// run): the park clears and the resume marker continues the
    /// interrupted task. Nothing when no park is live.
    pub async fn wake_park(&self) {
        if self.inner.park.lock().unwrap_or_else(poisoned).is_none() {
            return;
        }
        clear_park(&self.inner, "wake").await;
        submit_resume_marker(&self.inner).await;
    }
}

/// A provider's OAuth whose failed refresh the provider runtime takes over:
/// the refresh's error is recorded for the provider and the stored
/// credential stands, so the request reaches the runtime, which fails it
/// there without sending it ([`take_login_failure`]) and moves it to
/// another model the user configured. A refresh that succeeds clears the
/// record; an aborted refresh fails as before. An account login the run
/// found unusable ([`DeadLogin`]) is not refreshed again: its failure is
/// recorded at once. A new login of the account clears both.
struct LoginWatch {
    oauth: Arc<dyn OAuthAuth>,
    provider: String,
    logins: Arc<Mutex<HashMap<String, String>>>,
    dead: DeadLogins,
    /// The session's accounts: a refresh is of the account the provider's
    /// credential store serves ([`AccountBook::current_identity`]).
    accounts: Arc<AccountBook>,
}

impl OAuthAuth for LoginWatch {
    fn name(&self) -> &str {
        self.oauth.name()
    }

    fn is_subscription(&self) -> Option<bool> {
        self.oauth.is_subscription()
    }

    fn login_label(&self) -> Option<&str> {
        self.oauth.login_label()
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move {
            let credential = self.oauth.login(interaction, options).await?;
            // The account the login signs in as is alive again.
            let identity = eukhe_ai::auth::oauth::oauth_identity(&self.provider, &credential);
            self.accounts.revive(&self.provider, &identity);
            self.dead
                .lock()
                .unwrap_or_else(poisoned)
                .remove(&(self.provider.clone(), identity));
            self.logins
                .lock()
                .unwrap_or_else(poisoned)
                .remove(&self.provider);
            Ok(credential)
        })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move {
            let account = (
                self.provider.clone(),
                self.accounts
                    .current_identity(&self.provider, &self.accounts.accounts(&self.provider)),
            );
            let dead = self
                .dead
                .lock()
                .unwrap_or_else(poisoned)
                .get(&account)
                .map(|dead| dead.error.clone());
            if let Some(error) = dead {
                self.logins
                    .lock()
                    .unwrap_or_else(poisoned)
                    .insert(self.provider.clone(), error);
                return Ok(credential);
            }
            match self.oauth.refresh(credential.clone(), signal.clone()).await {
                Ok(refreshed) => {
                    self.logins
                        .lock()
                        .unwrap_or_else(poisoned)
                        .remove(&self.provider);
                    Ok(refreshed)
                }
                Err(error) if signal.aborted() => Err(error),
                Err(error) => {
                    self.logins.lock().unwrap_or_else(poisoned).insert(
                        self.provider.clone(),
                        format!("OAuth refresh failed for {}: {error}", self.provider),
                    );
                    Ok(credential)
                }
            }
        })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        self.oauth.to_auth(credential)
    }
}

/// The recorded failed refresh of `provider`'s login, taken: the request
/// about to go out on that login fails instead.
fn take_login_failure(logins: &Mutex<HashMap<String, String>>, provider: &str) -> Option<String> {
    logins.lock().unwrap_or_else(poisoned).remove(provider)
}

/// The diagnostic kind of a request that failed at the provider runtime
/// because its provider's login expired and its refresh failed.
pub(super) const LOGIN_EXPIRED_DIAGNOSTIC: &str = "login_expired";

/// The stream of a request whose provider's login expired: its one event
/// is the failure ([`login_failed_message`]).
fn login_failed_stream(model: &Model, error: &str) -> AssistantMessageEventStream {
    let out = create_assistant_message_event_stream();
    out.push(AssistantMessageEvent::Error {
        reason: ErrorReason::Error,
        error: login_failed_message(model, error),
    });
    out.end(None);
    out
}

/// The failure of a request on `model` whose provider's login expired:
/// the refresh's `error` and the login diagnostic.
fn login_failed_message(model: &Model, error: &str) -> AssistantMessage {
    let mut message = refuted_message(model, error);
    message.diagnostics = Some(vec![AssistantMessageDiagnostic {
        kind: LOGIN_EXPIRED_DIAGNOSTIC.to_owned(),
        timestamp: now_millis(),
        error: None,
        details: None,
    }]);
    message
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
    // the image role's model (`imageModel`, else `modelRoles.all`) or fail
    // with the actionable refusal.
    let mut serving = match image_route::resolve(
        context_has_images(&context),
        &model,
        || {
            crate::models::roles::role_model(
                settings.cvars(),
                eukhe_types::model_roles::ModelRole::Image,
            )
        },
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
    let mut failover = failover_policy(&settings);
    // A request to a provider that drops every repeat of its key may go
    // out again after a crash (spec O7): every send of it must reach that
    // provider, so it never fails over to another.
    if inner
        .models
        .get_provider(&primary.provider)
        .is_some_and(|provider| provider.dedups_requests)
    {
        failover.enabled = false;
    }
    let mut primary_dispatch = Arc::clone(&original);
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
    // The configured models the request moved to after its own model could
    // not go on, in order (`laws/fallback.bend`); after the first move the
    // sibling walk is over. `left_for`: why the request left its own model.
    let mut moved: Vec<Model> = Vec::new();
    let mut left_for: Option<Why> = None;
    // The waits for an account's reset the request may still take: the
    // run's retries.
    let mut account_waits = if settings.get_retry_enabled() {
        settings.get_retry_max_retries()
    } else {
        0
    };
    // A provider whose every account login this run found unusable is not
    // tried again: the request starts on the model the run went on with,
    // as one whose login just failed would move there ([`DeadLogin`]). A
    // provider with an account left goes on with it (`laws/account.bend`).
    let dead = provider_dead_login(&inner, &primary.provider).filter(|dead| {
        failover.enabled
            && (!context_has_images(&context) || dead.moved_to.input.contains(&Modality::Image))
    });
    if let Some(dead) = dead {
        let _recorded = take_login_failure(&inner.logins, &primary.provider);
        primary_failure = Some(login_failed_message(&primary, &dead.error));
        left_for = Some(Why::Login);
        dispatch = original_dispatch(&inner, &dead.moved_to, carried.clone(), simple);
        serving = dead.moved_to.clone();
        moved.push(dead.moved_to);
    }
    loop {
        // Each attempt opens with its own `start`, which drops the failed
        // attempt's partial downstream (the event protocol). A provider
        // whose login refresh just failed gets no send on the stale login.
        let mut events = match take_login_failure(&inner.logins, &serving.provider) {
            Some(error) => login_failed_stream(&serving, &error),
            None => dispatch(&serving, &context),
        }
        .events();
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
            if model_reference(&serving) == model_reference(&primary) {
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
        // Accounts first: a usage or rate limit, or a login that cannot
        // refresh, moves the request to another account of the same
        // provider and the same model before any other model
        // (`laws/account.bend`); with every account out, the model
        // fallback takes the request for why they are out.
        let mut accounts_out: Option<Why> = None;
        if failed {
            match account_turn(
                &inner,
                &settings,
                &serving.provider,
                &message,
                account_waits,
            ) {
                AccountTurn::Go {
                    delay_ms,
                    switch,
                    cause,
                } => {
                    if delay_ms > 0 {
                        account_waits = account_waits.saturating_sub(1);
                    }
                    switches += 1;
                    let _ = inner.events.send(ProviderWireEvent::AutoRetryStart {
                        attempt: switches,
                        max_attempts: failover.max_switches,
                        delay_ms,
                        error_message: switch.as_ref().map_or(cause, AccountSwitch::text),
                        backup_model: model_reference(&serving),
                    });
                    if let Some(switch) = switch {
                        record_switch(&inner, switch);
                    }
                    if waited_out(&carried, delay_ms).await {
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
                    // The account's credential resolves anew; the primary's
                    // own options carried the account before.
                    dispatch = original_dispatch(&inner, &serving, carried.clone(), simple);
                    if model_reference(&serving) == model_reference(&primary) {
                        primary_dispatch = Arc::clone(&dispatch);
                    }
                    continue;
                }
                AccountTurn::Out(why) => accounts_out = Some(why),
                AccountTurn::Stays => {}
            }
        }
        let retryable =
            message.stop_reason == StopReason::Error && is_retryable_assistant_error(&message);
        let next = if retryable && failover.enabled && moved.is_empty() && accounts_out.is_none() {
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
                // The model cannot go on: the request moves to another model
                // the user configured or another signed-in provider's
                // default, unless its provider keeps every send (failover
                // off). A wait or an end surfaces the failure; an end with
                // a fix surfaces its report in place of the failure's text;
                // the park of a usage limit is `finish_failure`'s.
                let mut report = None;
                if failover.enabled {
                    let (failing, failure) = match (&primary_failure, moved.is_empty()) {
                        (Some(primary_failure), true) => (&primary, primary_failure),
                        (Some(_) | None, _) => (&serving, &message),
                    };
                    let request = MoveRequest {
                        primary: &primary,
                        moved: &moved,
                        images: context_has_images(&context),
                        accounts_out,
                    };
                    match model_move(&inner, &settings, &carried, &request, failing, failure).await
                    {
                        Move::To { model, reason, why } => {
                            // A login found unusable stays so for the run.
                            if why == Why::Login {
                                mark_dead_login(
                                    &inner,
                                    &failing.provider,
                                    &DeadLogin {
                                        error: final_error_of(failure),
                                        moved_to: (*model).clone(),
                                    },
                                );
                            }
                            switches += 1;
                            let _ = inner.events.send(ProviderWireEvent::AutoRetryStart {
                                attempt: switches,
                                max_attempts: failover.max_switches,
                                delay_ms: 0,
                                error_message: reason,
                                backup_model: model_reference(&model),
                            });
                            dispatch = original_dispatch(&inner, &model, carried.clone(), simple);
                            serving = (*model).clone();
                            if moved.is_empty() {
                                left_for = Some(why);
                            }
                            moved.push(*model);
                            continue;
                        }
                        Move::Stays => {}
                        Move::Ends(text) => report = Some(text),
                    }
                }
                // A failure after a backup failed surfaces the primary's
                // latest failure, as the primary's, with the backups named;
                // a failure that never left the primary surfaces as it is.
                let (mut message, backups) = match primary_failure {
                    Some(primary_failure) if !backup_failures.is_empty() => {
                        (primary_failure, failover_note(&backup_failures))
                    }
                    Some(_) | None => (message, None),
                };
                // A request that left its own model and found no other to
                // answer ends on the reason it left, reported with its fix.
                let report = report.or_else(|| {
                    left_for.filter(|_| backups.is_some()).and_then(|why| {
                        fallback::end_report(why, &primary, &final_error_of(&message))
                    })
                });
                if let Some(report) = report {
                    message.error_message = Some(report);
                }
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
            // The model the request asked for answered (or its sibling for
            // it): its failures in a row are over. A request that left a
            // dead login: the run goes on with the model that answered.
            if moved.is_empty() {
                inner
                    .failures
                    .lock()
                    .unwrap_or_else(poisoned)
                    .remove(&model_reference(&primary));
            } else if left_for == Some(Why::Login) {
                for (_, dead) in inner
                    .dead_logins
                    .lock()
                    .unwrap_or_else(poisoned)
                    .iter_mut()
                    .filter(|((provider, _), _)| *provider == primary.provider)
                {
                    dead.moved_to = serving.clone();
                }
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
        if waited_out(&carried, delay_ms).await {
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

/// The original stream function of `model`'s provider with that provider's
/// own auth (a sibling's, or a configured model's the request moved to): a
/// re-dispatch resolves the candidate provider's
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
    let privacy = inner.privacy.clone();
    let logins = Arc::clone(&inner.logins);
    Arc::new(move |model: &Model, context: &TranscriptContext| {
        let Some((stream, stream_simple)) = original.clone() else {
            return create_assistant_message_event_stream();
        };
        let models = models.clone();
        let carried = carried.clone();
        let settings = Arc::clone(&settings);
        let privacy = privacy.clone();
        let logins = Arc::clone(&logins);
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
            // A login whose refresh just failed sends nothing.
            if let Some(error) = take_login_failure(&logins, &request_model.provider) {
                return Ok(login_failed_stream(&request_model, &error));
            }
            let options = StreamOptions {
                request,
                ..StreamOptions::default()
            };
            // The failover target may be remote where the primary was
            // local: scrub (and restore) against the resolved target.
            Ok(send_private(
                &settings,
                &privacy,
                &request_model,
                &context,
                |context| {
                    if simple {
                        stream_simple(
                            &request_model,
                            context,
                            SimpleStreamOptions {
                                stream: options,
                                ..SimpleStreamOptions::default()
                            },
                        )
                    } else {
                        stream(
                            &request_model,
                            context,
                            ProviderStreamOptions {
                                stream: options,
                                ..ProviderStreamOptions::default()
                            },
                        )
                    }
                },
            ))
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
    let available = credentialed_models(inner, carried, primary).await;
    std::iter::once(primary.clone())
        .chain(
            failover_candidates(primary, &available)
                .into_iter()
                .filter(|candidate| allowlist_allows(settings, candidate)),
        )
        .collect()
}

/// The models whose providers have credentials
/// ([`Models::get_available`]); none when the credential check fails, so
/// the request stays on `serving`.
async fn credentialed_models(
    inner: &Inner,
    carried: &CarriedOptions,
    serving: &Model,
) -> Vec<Model> {
    match inner
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
                "credential check failed; the request stays on {}",
                model_reference(serving)
            );
            Vec::new()
        }
    }
}

// ---------------------------------------------------------------------------
// Accounts
// ---------------------------------------------------------------------------

/// What a failed request does with the accounts of its provider
/// ([`account_turn`]).
enum AccountTurn {
    /// It goes on after `delay_ms` with another account (`switch`, for the
    /// run's report) or with the same one after its reset; `cause`: why the
    /// account before stopped.
    Go {
        delay_ms: u64,
        switch: Option<AccountSwitch>,
        cause: String,
    },
    /// Every account is out: the model fallback takes the request for
    /// `Why` (the earliest reset of a usage limit, or no login left).
    Out(Why),
    /// The failure is not the account's, or the provider has one account.
    Stays,
}

/// The account `provider`'s failed request goes on with
/// ([`AccountBook::step`], `laws/account.bend`): the next usable account,
/// a wait for the earliest reset while the request has `waits` left and
/// the reset is within the run's wait limit, else the model fallback.
fn account_turn(
    inner: &Inner,
    settings: &SettingsManager,
    provider: &str,
    message: &AssistantMessage,
    waits: u64,
) -> AccountTurn {
    let Some(failure) = AccountFailure::of(message, wait_cap_ms(settings)) else {
        return AccountTurn::Stays;
    };
    let accounts = inner.accounts.accounts(provider);
    let label = |identity: &str| {
        accounts
            .iter()
            .position(|account| account.identity == identity)
            .map_or_else(|| identity.to_owned(), |at| accounts[at].label(at + 1))
    };
    let from = inner
        .accounts
        .current(provider, &accounts)
        .map(|account| account.identity)
        .unwrap_or_default();
    let now = now_millis();
    let error = final_error_of(message);
    let cause = match failure {
        AccountFailure::Limit { until_ms } => format!(
            "the usage limit of {} holds until {} ({error})",
            label(&from),
            crate::session::manager::format_iso(i64::try_from(until_ms).unwrap_or(i64::MAX))
        ),
        AccountFailure::Login => format!("{} has no usable login ({error})", label(&from)),
    };
    let go = |identity: &str, delay_ms: u64| {
        inner.accounts.pin(provider, identity);
        AccountTurn::Go {
            delay_ms,
            // A wait for the account that failed is no switch.
            switch: (identity != from).then(|| AccountSwitch {
                provider: provider.to_owned(),
                to: label(identity),
                cause: cause.clone(),
            }),
            cause: cause.clone(),
        }
    };
    match inner
        .accounts
        .step(provider, failure, now, wait_cap_ms(settings), waits)
    {
        None => AccountTurn::Stays,
        Some(AccountStep::Use(account)) => go(&account.identity, 0),
        Some(AccountStep::Hold { account, until_ms }) => {
            go(&account.identity, until_ms.saturating_sub(now))
        }
        Some(AccountStep::Quota { until_ms }) => AccountTurn::Out(Why::Quota { until_ms }),
        Some(AccountStep::Login) => AccountTurn::Out(Why::Login),
    }
}

/// Record an account switch for the run's report.
fn record_switch(inner: &Inner, switch: AccountSwitch) {
    inner.switches.lock().unwrap_or_else(poisoned).push(switch);
}

/// Wait `delay_ms` (none for 0); `true` when the request was aborted
/// meanwhile.
async fn waited_out(carried: &CarriedOptions, delay_ms: u64) -> bool {
    if delay_ms == 0 {
        return false;
    }
    let sleep = tokio::time::sleep(Duration::from_millis(delay_ms));
    let Some(cancelled) = carried.signal.as_ref().map(AbortSignal::cancellation_token) else {
        sleep.await;
        return false;
    };
    tokio::select! {
        () = sleep => false,
        () = cancelled.cancelled() => true,
    }
}

// ---------------------------------------------------------------------------
// Model fallback
// ---------------------------------------------------------------------------

/// The request a model move is for.
struct MoveRequest<'a> {
    /// The model the request asked for.
    primary: &'a Model,
    /// The configured models it already moved to, in order.
    moved: &'a [Model],
    /// It attaches images: only a model that takes images can serve it.
    images: bool,
    /// Why every account of the failing model's provider is out, when they
    /// are ([`account_turn`]): the model fallback's failure.
    accounts_out: Option<Why>,
}

/// What a failed request does next ([`model_move`]).
enum Move {
    /// It goes on with `model`, for `reason` (recorded for the run's
    /// report), because its model failed for `why`.
    To {
        model: Box<Model>,
        reason: String,
        why: Why,
    },
    /// Its failure stands: the run's own retries go on, a usage limit
    /// waits (`finish_failure` parks it), no other model cures the
    /// failure, or no model is left and the failure names no fix.
    Stays,
    /// It ends with this report: the cause and the one command that fixes
    /// it ([`fallback::end_report`]).
    Ends(String),
}

/// What a request does after `failing` failed with `failure`
/// ([`fallback::step`], `laws/fallback.bend`): it moves to the first
/// untried model the user configured, then to the first untried default
/// model of another signed-in provider, or it stays, or it ends with a
/// report.
async fn model_move(
    inner: &Inner,
    settings: &SettingsManager,
    carried: &CarriedOptions,
    request: &MoveRequest<'_>,
    failing: &Model,
    failure: &AssistantMessage,
) -> Move {
    let Some(why) = request
        .accounts_out
        .or_else(|| failure_why(inner, settings, request, failure))
    else {
        return Move::Stays;
    };
    let available = credentialed_models(inner, carried, failing).await;
    let serves = |model: &Model| {
        allowlist_allows(settings, model)
            && (!request.images || model.input.contains(&Modality::Image))
    };
    let candidates: Vec<Model> = fallback::configured_models(settings, &available)
        .into_iter()
        .filter(|model| serves(model))
        .collect();
    // A provider whose login just failed is not signed in: its default is
    // no way on.
    let defaults: Vec<Model> = fallback::signed_in_defaults(&available)
        .into_iter()
        .filter(|model| serves(model))
        .filter(|model| match why {
            Why::Login => model.provider != failing.provider,
            Why::Failed { .. } | Why::Quota { .. } | Why::Unset => true,
        })
        .collect();
    let tried: Vec<Model> = std::iter::once(request.primary.clone())
        .chain(request.moved.iter().cloned())
        .collect();
    let error = final_error_of(failure);
    match fallback::step(why, &candidates, &defaults, &tried) {
        Step::Switch(at) => {
            let Some(model) = candidates.into_iter().chain(defaults).nth(at) else {
                return Move::Stays;
            };
            let reason = fallback::reason(why, failing, &error);
            record_move(inner, request.primary, &model, &reason);
            Move::To {
                model: Box::new(model),
                reason,
                why,
            }
        }
        Step::End(cause) => {
            fallback::end_report(cause, failing, &error).map_or(Move::Stays, Move::Ends)
        }
        Step::Keep | Step::Hold { .. } => Move::Stays,
    }
}

/// How a provider's request without a key fails (every API's wording).
const MISSING_KEY_PREFIX: &str = "No API key for provider: ";

/// Why `failure` keeps its model from going on, `None` for a failure no
/// other model cures: a provider without a usable login (its login
/// expired and the refresh failed, its credential store failed the
/// refresh, or it has no key); a usage limit whose
/// reset is past the bounded wait; else a retryable failure, the
/// request's model's failures in a row counted against the run's retries
/// (a request that already moved has none left).
fn failure_why(
    inner: &Inner,
    settings: &SettingsManager,
    request: &MoveRequest<'_>,
    failure: &AssistantMessage,
) -> Option<Why> {
    let no_login = failure
        .diagnostics
        .iter()
        .flatten()
        .any(|diagnostic| diagnostic.kind == LOGIN_EXPIRED_DIAGNOSTIC)
        || failure.error_message.as_deref().is_some_and(|error| {
            error.starts_with(MISSING_KEY_PREFIX)
                || error.contains(CREDENTIAL_STORE_FAILED)
                || error.contains(crate::models::registry::LOGIN_EXPIRED_REPORT)
        });
    if no_login {
        return Some(Why::Login);
    }
    if is_quota_block_failure(failure) {
        if let Some(reset_ms) =
            quota_failure_reset_ms(failure).filter(|reset_ms| *reset_ms > wait_cap_ms(settings))
        {
            return Some(Why::Quota {
                until_ms: now_millis().saturating_add(reset_ms),
            });
        }
    }
    if !(failure.stop_reason == StopReason::Error && is_retryable_assistant_error(failure)) {
        return None;
    }
    if !request.moved.is_empty() {
        return Some(Why::Failed {
            failures: 1,
            retries: 0,
        });
    }
    let failures = {
        let mut counts = inner.failures.lock().unwrap_or_else(poisoned);
        let count = counts.entry(model_reference(request.primary)).or_insert(0);
        *count = count.saturating_add(1);
        *count
    };
    let retries = if settings.get_retry_enabled() {
        settings.get_retry_max_retries()
    } else {
        0
    };
    Some(Why::Failed { failures, retries })
}

/// Record that requests to `from` went to `to` because of `reason`: one
/// record per pair, with its latest reason.
fn record_move(inner: &Inner, from: &Model, to: &Model, reason: &str) {
    let (from, to) = (model_reference(from), model_reference(to));
    let mut moves = inner.moves.lock().unwrap_or_else(poisoned);
    match moves
        .iter_mut()
        .find(|recorded| recorded.from == from && recorded.to == to)
    {
        Some(recorded) => reason.clone_into(&mut recorded.reason),
        None => moves.push(ModelMove {
            from,
            to,
            reason: reason.to_owned(),
        }),
    }
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
    // A park ends by the run's deadline (its budget's time limit).
    let time_left_ms = inner
        .deps
        .budget
        .report()
        .and_then(|report| report.deadline_ms)
        .map(|deadline| deadline.saturating_sub(now));
    let (resume_after_ms, end) =
        match provider_park_decision(parks_used, reset_ms, time_left_ms, &policy) {
            ProviderParkDecision::Park {
                resume_after_ms,
                end,
            } => (resume_after_ms, end),
            ProviderParkDecision::None { reason } => match reason {
                NoParkReason::Disabled | NoParkReason::ParkBudget | NoParkReason::Deadline => {
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
    let wait = ParkedWait {
        reset_ms: reset_ms.unwrap_or_default(),
        retry_cap_ms: cap,
        park_ms: resume_after_ms,
        end,
        resume_at_ms,
        wake: park_wake(inner),
    };
    Some((quota_parked_final_error(&wait, &error), resume_at_ms))
}

/// What wakes this session's park: the embedding's scheduler when it wired
/// one (its post-mutation hook arms the wake job's timer); without one, a
/// later `--resume` of the saved session, or nothing for an unsaved one.
fn park_wake(inner: &Inner) -> ParkWake {
    let scheduler = inner
        .deps
        .cron
        .as_ref()
        .and_then(|cron| cron.mutation_hook.as_ref());
    match (scheduler, &inner.deps.storage_dir) {
        (Some(_), _) => ParkWake::Scheduled,
        (None, Some(_)) => ParkWake::Resume(inner.deps.session_id.clone()),
        (None, None) => ParkWake::Unsaved,
    }
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
    submit_resume_marker(inner).await;
}

/// Queue the resume marker on the root conversation: the interrupted task
/// continues.
async fn submit_resume_marker(inner: &Inner) {
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
            tracing::warn!(%error, "quota resume marker submission failed");
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
#[path = "provider_tests.rs"]
mod tests;
