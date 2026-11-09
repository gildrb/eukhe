//! The provider runtime's wrapped streams: privacy, failover, quota park,
//! image routing and prompt progress, over faux providers.

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
fn fixture_set(text_only: bool, second_model_id: &str, settings: &serde_json::Value) -> Fixture {
    let dir = tempfile::tempdir().expect("tempdir");
    let agent_dir = dir.path().join("agent");
    let cwd = dir.path().join("cwd");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&cwd).expect("cwd");
    std::fs::write(agent_dir.join("settings.json"), settings.to_string()).expect("settings.json");
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
            kernel_unavailable: None,
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

/// A faux step that answers with the text of the last user message it
/// received, recording that text in `seen`.
fn echo(seen: &Arc<Mutex<Vec<String>>>) -> FauxResponseStep {
    let seen = Arc::clone(seen);
    FauxResponseStep::factory(
        move |context: &TranscriptContext,
              _options: Option<&SimpleStreamOptions>,
              _state: &eukhe_ai::providers::faux::FauxProviderState,
              _model: &Model| {
            let text = context
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
            seen.lock().unwrap_or_else(poisoned).push(text.clone());
            Ok(faux_assistant_message(
                text,
                FauxAssistantMessageOptions::default(),
            ))
        },
    )
}

/// The text of an answer's text blocks.
fn answer_text(message: &AssistantMessage) -> String {
    message
        .content
        .iter()
        .filter_map(|block| match block {
            eukhe_types::pi_ai::AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            eukhe_types::pi_ai::AssistantContentBlock::Thinking(_)
            | eukhe_types::pi_ai::AssistantContentBlock::ToolCall(_) => None,
        })
        .collect()
}

/// What the provider receives and what the caller gets back: a remote
/// model sees tokens for every personal class (`privacy.anonymizeRemote`,
/// `privacy.terms`), code as it is, and its answer, which echoes the
/// tokens, comes back restored; a loopback model sees the raw text.
#[tokio::test]
async fn remote_models_receive_tokens_and_their_answers_come_back_restored() {
    let fixture = fixture_set(
        /*text_only*/ true,
        "shared-1",
        &serde_json::json!({ "privacy": { "anonymizeRemote": true, "terms": ["Ada Lovelace"] } }),
    );
    let said = |text: &str| {
        user_message(UserContent::Blocks(vec![UserContentBlock::Text(
            TextContent::new(text),
        )]))
    };
    let text = "Ada Lovelace works at /home/ada/x, mail dev@example.net, host 10.0.0.7: a::before { } and std::fmt";
    let seen: Arc<Mutex<Vec<String>>> = Arc::default();

    let mut remote = fixture.faux_a.get_model();
    remote.base_url = "https://api.anthropic.com".to_owned();
    fixture.faux_a.set_responses(vec![echo(&seen)]);
    let reply = drive(&fixture.models, &remote, vec![said(text)]).await;
    assert_eq!(
            (seen.lock().unwrap_or_else(poisoned).clone(), answer_text(&reply)),
            (
                vec!["PERSON_1 works at /home/ada/x, mail EMAIL_1, host IP_1: a::before { } and std::fmt".to_owned()],
                text.to_owned()
            )
        );

    let local = fixture.faux_a.get_model();
    fixture.faux_a.set_responses(vec![echo(&seen)]);
    let reply = drive(&fixture.models, &local, vec![said(text)]).await;
    assert_eq!(
        (
            seen.lock().unwrap_or_else(poisoned)[1].clone(),
            answer_text(&reply)
        ),
        (text.to_owned(), text.to_owned())
    );
}

/// Regression: the failover re-dispatch scrubbed the already scrubbed
/// context, so a loopback sibling of a remote primary read tokens. Each
/// dispatch now scrubs the raw context against the model it reaches.
#[tokio::test]
async fn a_loopback_sibling_of_a_remote_primary_reads_the_raw_text() {
    let fixture = fixture_set(
        /*text_only*/ false,
        "shared-1",
        &serde_json::json!({ "privacy": { "anonymizeRemote": true, "terms": ["Ada Lovelace"] } }),
    );
    let mut remote = fixture.faux_a.get_model();
    remote.base_url = "https://api.anthropic.com".to_owned();
    fixture
        .faux_a
        .set_responses(vec![error_step("503 Service Unavailable")]);
    let seen: Arc<Mutex<Vec<String>>> = Arc::default();
    fixture.faux_b.set_responses(vec![echo(&seen)]);
    let text = "Ada Lovelace at dev@example.net";
    let reply = drive(
        &fixture.models,
        &remote,
        vec![user_message(UserContent::Text(text.to_owned()))],
    )
    .await;
    assert_eq!(
        (
            seen.lock().unwrap_or_else(poisoned).clone(),
            answer_text(&reply)
        ),
        (vec![text.to_owned()], text.to_owned())
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
            && text.ends_with("(failover to faux-b/shared-1 failed too: 401 invalid x-api-key)"),
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
