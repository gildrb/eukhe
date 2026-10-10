//! First-run onboarding verifiers: the trace question, the sign-in flow,
//! and the completion marker's persistence.

use super::*;

/// The product's settings-backed onboarding persistence (the
/// `SettingsOnboardingSink` glue over the public settings manager, minus
/// the best-effort telemetry the e2e harness has no client for).
struct FreshHomeOnboardingSink {
    cwd: PathBuf,
    agent_dir: PathBuf,
}

impl eukhe_tui::interactive::OnboardingSink for FreshHomeOnboardingSink {
    fn onboarding_shown(&self) -> bool {
        eukhe_core::settings::SettingsManager::create(&self.cwd, &self.agent_dir)
            .get_onboarding_shown()
    }

    fn agent_traces_choice_written(&self) -> bool {
        eukhe_core::settings::SettingsManager::create(&self.cwd, &self.agent_dir)
            .agent_traces_choice_written()
    }

    fn set_agent_traces_enabled(&self, enabled: bool) -> anyhow::Result<()> {
        eukhe_core::settings::SettingsManager::create(&self.cwd, &self.agent_dir)
            .set_agent_traces_enabled(enabled)
    }

    fn mark_onboarding_complete(&self) -> anyhow::Result<()> {
        eukhe_core::settings::SettingsManager::create(&self.cwd, &self.agent_dir)
            .set_onboarding_shown(true)
    }

    fn onboarding_incomplete(
        &self,
        _outcome: &'static str,
    ) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()> + Send + '_>> {
        Box::pin(std::future::ready(()))
    }
}

/// The product sink whose completion write always fails (the failed
/// persistence path): reads stay real, the marker write errors.
struct FailingMarkOnboardingSink {
    cwd: PathBuf,
    agent_dir: PathBuf,
}

impl eukhe_tui::interactive::OnboardingSink for FailingMarkOnboardingSink {
    fn onboarding_shown(&self) -> bool {
        eukhe_core::settings::SettingsManager::create(&self.cwd, &self.agent_dir)
            .get_onboarding_shown()
    }

    fn agent_traces_choice_written(&self) -> bool {
        eukhe_core::settings::SettingsManager::create(&self.cwd, &self.agent_dir)
            .agent_traces_choice_written()
    }

    fn set_agent_traces_enabled(&self, _enabled: bool) -> anyhow::Result<()> {
        Ok(())
    }

    fn mark_onboarding_complete(&self) -> anyhow::Result<()> {
        Err(anyhow::anyhow!("settings disk full"))
    }

    fn onboarding_incomplete(
        &self,
        _outcome: &'static str,
    ) -> std::pin::Pin<Box<dyn std::future::Future<Output = ()> + Send + '_>> {
        Box::pin(std::future::ready(()))
    }
}

/// A fresh install asks the trace question exactly once, as the first-run
/// onboarding step — the opt-in moment for trace sharing (sharing ships
/// OFF, so `Share` opts in and `Not now` leaves it off; TS asks
/// unconditionally with the same default). One Enter answers it: the
/// answer and the completion flag persist together, and the released pane
/// runs the submitted turn. The flag then gates the next launch's task
/// mount (the `onboarding_gate_follows_settings_and_auth` unit) and the
/// phase's own marker check, so the question never returns.
#[tokio::test]
async fn fresh_home_asks_the_trace_question_once_and_completes() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    let script = serde_json::json!({ "responses": [
        { "text": "hello fresh home", "delayMs": 20 },
    ] });
    std::fs::write(
        dir.path().join("script.json"),
        serde_json::to_string(&script).expect("script json"),
    )
    .expect("script.json");

    // The task mounts exactly as the product's model-ready gate builds it;
    // the sink persists through the real settings manager.
    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    options.onboarding = Some(eukhe_tui::interactive::OnboardingTask {
        sink: std::sync::Arc::new(FreshHomeOnboardingSink {
            cwd: dir.path().to_path_buf(),
            agent_dir: agent_dir.clone(),
        }),
        model_ready: std::sync::Arc::new(|| true),
        current_model: None,
        provider_auth: None,
    });
    // Enter answers the mounted question on its pre-selected `Share` row;
    // the submission that follows must reach the editor, not the dialog.
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                crossterm::event::KeyCode::Enter,
                crossterm::event::KeyModifiers::NONE,
            )),
            eukhe_tui::interactive::HeadlessStep::Submit("hi".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");

    // The question owned the pane first, then released it to the session:
    // the answer and the completion flag persisted together.
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("Upload agent traces"),
        "the onboarding question rendered once for the fresh home:\n{rendered}"
    );
    assert!(
        rendered.contains("hello fresh home"),
        "the answered dialog released the pane and the first turn ran:\n{rendered}"
    );
    let settings = eukhe_core::settings::SettingsManager::create(dir.path(), &agent_dir);
    assert!(
        settings.get_onboarding_shown(),
        "the answered flow marked onboarding shown"
    );
    assert!(
        settings.get_agent_traces_enabled(),
        "the pre-selected Share answer persisted"
    );
    drop(supervisor);
}

/// A provisioned home (sharing explicitly opted out, a copied config) never
/// sees the trace question: the standing choice stands and the flow
/// completes silently — the session screen owns the first frame, the
/// submitted prompt runs directly, and only the completion flag is
/// written. (TS #2368 asks such a home the question; the operator's
/// existing-user ruling removes it for the rust port.)
#[tokio::test]
async fn provisioned_opt_out_home_completes_silently_without_the_question() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    // The provisioned opt-out home: copied config, no onboarding flag.
    std::fs::write(
        agent_dir.join("settings.json"),
        r#"{ "agentTraces": { "enabled": false } }"#,
    )
    .expect("provisioned settings");
    let supervisor = spawn_supervisor(dir.path());

    let script = serde_json::json!({ "responses": [
        { "text": "hello provisioned home", "delayMs": 20 },
    ] });
    std::fs::write(
        dir.path().join("script.json"),
        serde_json::to_string(&script).expect("script json"),
    )
    .expect("script.json");

    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    options.onboarding = Some(eukhe_tui::interactive::OnboardingTask {
        sink: std::sync::Arc::new(FreshHomeOnboardingSink {
            cwd: dir.path().to_path_buf(),
            agent_dir: agent_dir.clone(),
        }),
        model_ready: std::sync::Arc::new(|| true),
        current_model: None,
        provider_auth: None,
    });
    // No key step answers anything: the flow must complete before the
    // plan's submission reaches the editor.
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("hi".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");

    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("hello provisioned home"),
        "the session started directly and completed its first turn:\n{rendered}"
    );
    assert!(
        !rendered.contains("Upload agent traces"),
        "the question never owned a session frame:\n{rendered}"
    );

    // The silent completion persists only the flag: the standing opt-out
    // survives untouched and a fresh manager reads the pair, so the gate
    // never mounts the task again.
    let settings = eukhe_core::settings::SettingsManager::create(dir.path(), &agent_dir);
    assert!(
        !settings.get_agent_traces_enabled(),
        "the standing opt-out survived the silent completion"
    );
    assert!(
        settings.get_onboarding_shown(),
        "the silent flow marked onboarding shown"
    );
    drop(supervisor);
}

/// The scripted provider-auth surface the full-flow verifier drives: the
/// Prime Inference row and its panel-driven login (a progress line, the
/// paste prompt, the store), one api-key provider row (the picker's
/// connect step), and one `mcp:` service row (the picker's exclusion).
/// Credentials persist through the real auth store so the model-readiness
/// probe and the connected marks read them like the product does.
struct FullFlowProviderAuth {
    agent_dir: PathBuf,
}

impl FullFlowProviderAuth {
    fn stored(&self, provider: &str) -> bool {
        eukhe_core::auth::AuthStorage::create(&self.agent_dir)
            .get_all()
            .credential(provider)
            .is_some()
    }
}

impl eukhe_tui::provider_auth::ProviderAuthCommands for FullFlowProviderAuth {
    fn login_options(&self) -> eukhe_tui::provider_auth::ProviderRowsFuture {
        let rows = vec![
            eukhe_tui::provider_auth::ProviderRow {
                id: eukhe_tui::provider_auth::PRIME_INFERENCE_PROVIDER_ID.to_string(),
                name: "Prime Inference".to_string(),
                auth_type: eukhe_tui::provider_auth::AuthType::ApiKey,
                status: Some(eukhe_tui::provider_auth::AuthStatusIndicator {
                    style: eukhe_tui::provider_auth::AuthStatusStyle::Success,
                    label: "configured".to_string(),
                }),
                flow: eukhe_tui::provider_auth::AuthFlow::TerminalFlow,
                configured: self.stored(eukhe_tui::provider_auth::PRIME_INFERENCE_PROVIDER_ID),
                available: true,
            },
            eukhe_tui::provider_auth::ProviderRow {
                id: "faux-key".to_string(),
                name: "Faux Key".to_string(),
                auth_type: eukhe_tui::provider_auth::AuthType::ApiKey,
                status: None,
                flow: eukhe_tui::provider_auth::AuthFlow::ApiKeyPrompt,
                configured: self.stored("faux-key"),
                available: true,
            },
            eukhe_tui::provider_auth::ProviderRow {
                id: "mcp:faux".to_string(),
                name: "Faux MCP".to_string(),
                auth_type: eukhe_tui::provider_auth::AuthType::Oauth,
                status: None,
                flow: eukhe_tui::provider_auth::AuthFlow::TerminalFlow,
                configured: false,
                available: true,
            },
        ];
        Box::pin(async move { rows })
    }

    fn logout_options(&self) -> eukhe_tui::provider_auth::ProviderRowsFuture {
        Box::pin(async move { Vec::new() })
    }

    fn login(
        &self,
        provider: &eukhe_tui::provider_auth::ProviderRow,
        api_key: Option<&str>,
    ) -> eukhe_tui::provider_auth::ProviderAuthFuture {
        let agent_dir = self.agent_dir.clone();
        let provider_id = provider.id.clone();
        let provider_name = provider.name.clone();
        let key = api_key.map(str::to_string);
        Box::pin(async move {
            let mut auth = eukhe_core::auth::AuthStorage::create(&agent_dir);
            auth.set(
                &provider_id,
                eukhe_core::auth::AuthCredential::ApiKey {
                    key: key.unwrap_or_default(),
                    prime_team: None,
                },
            );
            if auth.drain_errors().pop().is_some() {
                return eukhe_tui::provider_auth::ProviderAuthOutcome::Error(format!(
                    "Failed to save API key for {provider_name}"
                ));
            }
            eukhe_tui::provider_auth::ProviderAuthOutcome::Status(format!(
                "Saved API key for {provider_name}"
            ))
        })
    }

    fn login_on_panel(
        &self,
        provider: &eukhe_tui::provider_auth::ProviderRow,
        panel: eukhe_tui::auth_panel::AuthPanelHandle,
    ) -> eukhe_tui::provider_auth::ProviderAuthFuture {
        let agent_dir = self.agent_dir.clone();
        let provider_id = provider.id.clone();
        let provider_name = provider.name.clone();
        Box::pin(async move {
            // Only the Prime row runs here (the flow's sign-in step);
            // anything else cancels.
            if provider_id != eukhe_tui::provider_auth::PRIME_INFERENCE_PROVIDER_ID {
                return eukhe_tui::provider_auth::ProviderAuthOutcome::Cancelled;
            }
            panel.progress("Checking Prime Inference access...");
            let Some(api_key) = panel
                .paste_prompt(
                    "Paste a Prime API key below:",
                    eukhe_tui::auth_panel::PastePromptTone::Muted,
                    eukhe_tui::auth_panel::PasteStyle::Visible,
                )
                .await
            else {
                return eukhe_tui::provider_auth::ProviderAuthOutcome::Cancelled;
            };
            let mut auth = eukhe_core::auth::AuthStorage::create(&agent_dir);
            auth.set(
                &provider_id,
                eukhe_core::auth::AuthCredential::ApiKey {
                    key: api_key,
                    prime_team: None,
                },
            );
            if auth.drain_errors().pop().is_some() {
                return eukhe_tui::provider_auth::ProviderAuthOutcome::Error(format!(
                    "Failed to login to {provider_name}"
                ));
            }
            eukhe_tui::provider_auth::ProviderAuthOutcome::Status(format!(
                "Saved API key for {provider_name}. Credentials saved to {}.",
                agent_dir.join("auth.json").display()
            ))
        })
    }

    fn logout(
        &self,
        _provider: &eukhe_tui::provider_auth::ProviderRow,
    ) -> eukhe_tui::provider_auth::ProviderAuthFuture {
        Box::pin(async move { eukhe_tui::provider_auth::ProviderAuthOutcome::Cancelled })
    }

    fn anthropic_subscription_warning(&self) -> eukhe_tui::provider_auth::ProviderWarningFuture {
        // The faux full-flow drives no Anthropic subscription auth.
        Box::pin(async move { None })
    }
}

/// The full first-run flow on a fresh home with no usable model (TS
/// #2340's `runOnboardingFlow` not-ready branch): the welcome screen's
/// login action starts the flow, the Prime Inference sign-in runs through
/// the inline auth panel (a progress line, the paste prompt), the default
/// GLM 5.3 model applies behind the pane, the connect-more-providers
/// picker connects one more provider through its key prompt and
/// re-mounts with the connected mark, and the trace question ends the
/// flow — every answer, both credentials, and the completion flag
/// persist together, and the released pane runs the submitted turn.
#[tokio::test]
async fn fresh_home_runs_the_full_sign_in_flow_to_completion() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    let script = serde_json::json!({ "responses": [
        { "text": "hello full flow", "delayMs": 20 },
    ] });
    std::fs::write(
        dir.path().join("script.json"),
        serde_json::to_string(&script).expect("script json"),
    )
    .expect("script.json");

    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    // The readiness probe mirrors the flow's contract: the home is not
    // ready until the sign-in stores its credential (the model-ready
    // gate at flow end).
    let probe_agent_dir = agent_dir.clone();
    let model_ready = std::sync::Arc::new(move || {
        eukhe_core::auth::AuthStorage::create(&probe_agent_dir)
            .get_all()
            .credential(eukhe_tui::provider_auth::PRIME_INFERENCE_PROVIDER_ID)
            .is_some()
    });
    options.onboarding = Some(eukhe_tui::interactive::OnboardingTask {
        sink: std::sync::Arc::new(FreshHomeOnboardingSink {
            cwd: dir.path().to_path_buf(),
            agent_dir: agent_dir.clone(),
        }),
        model_ready,
        current_model: None,
        provider_auth: Some(eukhe_tui::provider_auth::ProviderAuthCommandsHandle(
            std::sync::Arc::new(FullFlowProviderAuth {
                agent_dir: agent_dir.clone(),
            }),
        )),
    });
    let enter = || {
        eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
            crossterm::event::KeyCode::Enter,
            crossterm::event::KeyModifiers::NONE,
        ))
    };
    let down = || {
        eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
            crossterm::event::KeyCode::Down,
            crossterm::event::KeyModifiers::NONE,
        ))
    };
    // The plan waits on observable readiness, not fixed sleeps: each
    // barrier holds the queued batch until a frame rendered after arming
    // contains the condition, so a loaded runner cannot fire keys at a
    // pane whose field or picker has not mounted yet (the pane drive
    // implements the same WaitRender contract the run loop's session
    // steps use).
    let wait_render = |needle: &str| eukhe_tui::interactive::HeadlessStep::WaitRender {
        needle: needle.to_string(),
        timeout_ms: 5_000,
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            // The welcome screen's login action starts the flow.
            enter(),
            // The Prime sign-in: the paste prompt mounts with the flow.
            wait_render("Paste a Prime API key below:"),
            eukhe_tui::interactive::HeadlessStep::Type("faux-prime-key".to_string()),
            enter(),
            // The model applies behind the pane, then the picker mounts.
            wait_render("Connect other providers, or continue."),
            // Down to the provider row: Enter runs its key prompt.
            down(),
            enter(),
            wait_render("Enter API key"),
            eukhe_tui::interactive::HeadlessStep::Type("faux-key".to_string()),
            enter(),
            // The picker re-mounts with the connected mark; Enter on the
            // pinned Continue row ends the step.
            wait_render("  ok"),
            enter(),
            // The trace question: Enter on the pre-selected Share row.
            wait_render("Upload agent traces"),
            enter(),
            // The released pane runs the submitted turn.
            eukhe_tui::interactive::HeadlessStep::Submit("hi".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");

    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("Log in with Prime Inference"),
        "the welcome screen's action rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("Login with Prime Inference"),
        "the login dialog's heading replaced the brand line:\n{rendered}"
    );
    assert!(
        rendered.contains("Paste a Prime API key below:"),
        "the paste prompt mounted inside the pane:\n{rendered}"
    );
    assert!(
        rendered.contains("Connect other providers, or continue."),
        "the providers picker rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("Upload agent traces"),
        "the trace question ended the flow:\n{rendered}"
    );
    assert!(
        rendered.contains("hello full flow"),
        "the completed flow released the pane and the first turn ran:\n{rendered}"
    );
    // The default-model apply's round trip: a faux-script session's model
    // collection serves only the scripted faux provider (plus any
    // models.json models), never the bundled Prime Inference catalog, so
    // the daemon refuses the GLM switch — the refusal row is the proof the
    // apply REQUEST reached it and its failure surfaced like TS's
    // applySelectedModel error path. The flow still completes and the
    // marker still writes (the readiness probe reads the registry, not the
    // session).
    assert!(
        rendered.contains(
            "the daemon rejected the set_model request: Model not found: prime-inference/z-ai/glm-5.3"
        ),
        "the apply round-tripped and the daemon's refusal surfaced:\n{rendered}"
    );
    // The connected provider's status row shows the store outcome.
    assert!(
        rendered.contains("Saved API key for Faux Key"),
        "the provider login's status row applied:\n{rendered}"
    );

    // Everything persisted together: the flag, the answer, both
    // credentials.
    let settings = eukhe_core::settings::SettingsManager::create(dir.path(), &agent_dir);
    assert!(
        settings.get_onboarding_shown(),
        "the completed flow marked onboarding shown"
    );
    assert!(
        settings.get_agent_traces_enabled(),
        "the Share answer persisted"
    );
    let auth = eukhe_core::auth::AuthStorage::create(&agent_dir);
    assert!(
        auth.get_all()
            .credential(eukhe_tui::provider_auth::PRIME_INFERENCE_PROVIDER_ID)
            .is_some(),
        "the Prime sign-in stored its credential"
    );
    assert!(
        auth.get_all().credential("faux-key").is_some(),
        "the provider login stored its key"
    );
    drop(supervisor);
}

/// A failed completion write surfaces a warning row and never kills the
/// run: a provisioned home whose settings write fails still completes the
/// flow for this run (the session stays usable), the warning names the
/// failed persistence, and the unpersisted marker honestly re-mounts the
/// flow next launch. The run never dies over a settings write.
#[tokio::test]
async fn a_failed_completion_write_surfaces_a_warning_and_never_kills_the_run() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    std::fs::write(
        agent_dir.join("settings.json"),
        r#"{ "agentTraces": { "enabled": false } }"#,
    )
    .expect("provisioned settings");
    let supervisor = spawn_supervisor(dir.path());

    let script = serde_json::json!({ "responses": [
        { "text": "hello despite the write failure", "delayMs": 20 },
    ] });
    std::fs::write(
        dir.path().join("script.json"),
        serde_json::to_string(&script).expect("script json"),
    )
    .expect("script.json");

    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    options.onboarding = Some(eukhe_tui::interactive::OnboardingTask {
        sink: std::sync::Arc::new(FailingMarkOnboardingSink {
            cwd: dir.path().to_path_buf(),
            agent_dir: agent_dir.clone(),
        }),
        model_ready: std::sync::Arc::new(|| true),
        current_model: None,
        provider_auth: None,
    });
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("hi".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("the run survives the failed write");

    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("hello despite the write failure"),
        "the session ran its first turn despite the failed write:\n{rendered}"
    );
    assert!(
        !rendered.contains("Upload agent traces"),
        "the standing choice never re-opened the question:\n{rendered}"
    );
    assert!(
        rendered.contains("could not be saved"),
        "the failed persistence surfaced as a warning row:\n{rendered}"
    );
    // The marker honestly stayed unset: the next launch re-mounts the flow.
    let settings = eukhe_core::settings::SettingsManager::create(dir.path(), &agent_dir);
    assert!(
        !settings.get_onboarding_shown(),
        "the failed write left the marker unset"
    );
    drop(supervisor);
}

/// The re-show regression: the agents-view flow re-runs the onboarding
/// phase for every session it opens with the SAME task (the task mounts
/// once at startup, then rides the cloned options), so the phase gates on
/// the persisted completion marker itself. A `Not now` answer completes
/// the flow (opt-out + flag together), and a second session opened with
/// the same task starts straight at the session screen — the question
/// never returns, `/traces` stays the change path.
#[tokio::test]
async fn a_completed_flow_never_reopens_the_question_for_a_later_session() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // One scripted response: the faux queue spans one session (each
    // created session replays from the top), so both runs render the
    // same turn text and the assertions stay per-run.
    let script = serde_json::json!({ "responses": [
        { "text": "hello each session", "delayMs": 20 },
    ] });
    std::fs::write(
        dir.path().join("script.json"),
        serde_json::to_string(&script).expect("script json"),
    )
    .expect("script.json");

    // The SAME options (the same task object) back both session runs, the
    // way `run_agents_view_flow` clones `base` into every session open.
    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    options.onboarding = Some(eukhe_tui::interactive::OnboardingTask {
        sink: std::sync::Arc::new(FreshHomeOnboardingSink {
            cwd: dir.path().to_path_buf(),
            agent_dir: agent_dir.clone(),
        }),
        model_ready: std::sync::Arc::new(|| true),
        current_model: None,
        provider_auth: None,
    });
    // Down + Enter answers `Not now` (the answer that used to re-show the
    // question on every later session open), then the turn runs.
    let first_plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                crossterm::event::KeyCode::Down,
                crossterm::event::KeyModifiers::NONE,
            )),
            eukhe_tui::interactive::HeadlessStep::Key(crossterm::event::KeyEvent::new(
                crossterm::event::KeyCode::Enter,
                crossterm::event::KeyModifiers::NONE,
            )),
            eukhe_tui::interactive::HeadlessStep::Submit("hi".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let first = run_headless_bounded(options.clone(), first_plan)
        .await
        .expect("first interactive run");
    let first_rendered = first.frames.join("\n");
    assert!(
        first_rendered.contains("Upload agent traces"),
        "the fresh home was asked once:\n{first_rendered}"
    );
    assert!(
        first_rendered.contains("hello each session"),
        "the answered dialog released the pane and the first turn ran:\n{first_rendered}"
    );
    let settings = eukhe_core::settings::SettingsManager::create(dir.path(), &agent_dir);
    assert!(
        !settings.get_agent_traces_enabled(),
        "the Not-now answer persisted (the opt-out)"
    );
    assert!(
        settings.get_onboarding_shown(),
        "the completion flag persisted with the answer"
    );

    // The second session with the same task: no key step answers anything,
    // so the phase must exit before the submission reaches the editor —
    // the persisted marker is the phase's own gate.
    let second_plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("again".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let second = run_headless_bounded(options, second_plan)
        .await
        .expect("second interactive run");
    let second_rendered = second.frames.join("\n");
    assert!(
        second_rendered.contains("hello each session"),
        "the second session started directly and completed its turn:\n{second_rendered}"
    );
    assert!(
        !second_rendered.contains("Upload agent traces"),
        "the completed flow never reopened the question:\n{second_rendered}"
    );
    drop(supervisor);
}
