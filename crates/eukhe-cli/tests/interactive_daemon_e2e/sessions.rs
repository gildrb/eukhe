//! Session lifecycle verifiers: idle attach, the subscription warning,
//! bare launches, submit ordering, and refused submits.

use super::*;

/// The empty `prompt`/`prompt_and_wait` input payload (no content, images, or
/// admission): every optional field stays absent on the wire.
fn empty_prompt_input() -> eukhe_types::daemon::PromptInput {
    eukhe_types::daemon::PromptInput {
        content: None,
        images: None,
        streaming_behavior: None,
        queue_if_busy: None,
        expand_prompt_templates: None,
        source: None,
        agent_message_id: None,
        custom_message: None,
        queue_key: None,
        prefix_messages: None,
        admission_id: None,
        rlm_notice_nonce: None,
    }
}

/// Create a live session over the daemon wire and settle one scripted turn
/// in it, so the session ends IDLE with a durable transcript and no owner
/// client (the "settled session a `eukhe --resume <id>` attach
/// opens" fixture).
async fn create_idle_session_with_settled_turn(
    socket: &Path,
    script_path: &Path,
    script: &serde_json::Value,
    cwd: &Path,
    session_dir: &Path,
    prompt_text: &str,
) -> String {
    let session = create_session_via_daemon(socket, script_path, script, cwd, session_dir).await;
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(socket)
        .await
        .expect("connect supervisor");
    client
        .request_ok(DaemonCommand::PromptAndWait {
            id: None,
            active_session_id: session.clone(),
            message: prompt_text.to_string(),
            input: empty_prompt_input(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("prompt_and_wait");
    client.close();
    session
}

/// The attach-render regression (the blank-pane bug class from the live
/// dogfood): attaching to an IDLE settled session must paint the settled
/// transcript from the attach snapshot alone — no key, submit, or resize
/// input. TS `renderInitialMessages` ends in `requestRender` after the
/// session load; the Rust equivalent is `rebuild_view`'s dirty flag, and
/// this verifier pins that path (the run's only step is a settle window,
/// so any frame below comes from the attach's own render scheduling).
#[tokio::test]
async fn tui_attach_to_idle_session_renders_without_input() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    let script = serde_json::json!({ "responses": [
        { "text": "idle session fixture reply" },
    ] });
    let session = create_idle_session_with_settled_turn(
        &supervisor.socket,
        &dir.path().join("script.json"),
        &script,
        dir.path(),
        &session_dir,
        "settle the attach fixture",
    )
    .await;

    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    options.session = eukhe_tui::interactive::SessionSelection::Attach(session.clone());
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![eukhe_tui::interactive::HeadlessStep::WaitMs(1_500)],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    assert!(
        !outcome.frames.is_empty(),
        "the attach painted frames with no key, submit, or resize input"
    );
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("settle the attach fixture"),
        "the settled user turn rendered from the attach snapshot:\n{rendered}"
    );
    assert!(
        rendered.contains("idle session fixture reply"),
        "the settled assistant reply rendered from the attach snapshot:\n{rendered}"
    );
    assert_eq!(
        outcome.active_session_id, session,
        "the run attached to the idle session by id"
    );
    drop(supervisor);
}

/// The Anthropic subscription ban-risk warning's detection text: the fake
/// auth resolves it for the e2e (the product text the login-completed arm
/// draws is the `ANTHROPIC_SUBSCRIPTION_AUTH_WARNING` constant; the two
/// stay distinguishable).
const E2E_SUBSCRIPTION_WARNING: &str = "E2E anthropic subscription ban-risk warning";

/// The e2e's fake auth surface: the credential-detection arm resolves a
/// subscription warning (the product's `getAnthropicSubscriptionAuthWarning`
/// seam — a stored OAuth credential answers the warning text).
struct E2ESubscriptionAuth;

impl eukhe_tui::provider_auth::ProviderAuthCommands for E2ESubscriptionAuth {
    fn login_options(&self) -> eukhe_tui::provider_auth::ProviderRowsFuture {
        Box::pin(async move { Vec::new() })
    }

    fn logout_options(&self) -> eukhe_tui::provider_auth::ProviderRowsFuture {
        Box::pin(async move { Vec::new() })
    }

    fn login(
        &self,
        _provider: &eukhe_tui::provider_auth::ProviderRow,
        _api_key: Option<&str>,
    ) -> eukhe_tui::provider_auth::ProviderAuthFuture {
        Box::pin(async move { eukhe_tui::provider_auth::ProviderAuthOutcome::Cancelled })
    }

    fn login_on_panel(
        &self,
        _provider: &eukhe_tui::provider_auth::ProviderRow,
        _panel: eukhe_tui::auth_panel::AuthPanelHandle,
    ) -> eukhe_tui::provider_auth::ProviderAuthFuture {
        Box::pin(async move { eukhe_tui::provider_auth::ProviderAuthOutcome::Cancelled })
    }

    fn logout(
        &self,
        _provider: &eukhe_tui::provider_auth::ProviderRow,
    ) -> eukhe_tui::provider_auth::ProviderAuthFuture {
        Box::pin(async move { eukhe_tui::provider_auth::ProviderAuthOutcome::Cancelled })
    }

    fn anthropic_subscription_warning(&self) -> eukhe_tui::provider_auth::ProviderWarningFuture {
        Box::pin(async move { Some(E2E_SUBSCRIPTION_WARNING) })
    }
}

/// The interactive options for a session on an Anthropic model with the
/// fake subscription credential surface (the detection arm's two inputs).
fn subscription_options(
    supervisor: &Supervisor,
    dir: &Path,
    session_dir: &Path,
    session: eukhe_tui::interactive::SessionSelection,
) -> eukhe_tui::interactive::InteractiveOptions {
    let mut options = base_options(supervisor, dir, session_dir);
    options.script_path = None;
    options.model_selection = eukhe_tui::interactive::ModelSelection {
        provider: Some("anthropic".to_string()),
        model: Some("claude-test".to_string()),
        api_key: None,
        thinking: None,
    };
    options.provider_auth = Some(eukhe_tui::provider_auth::ProviderAuthCommandsHandle(
        std::sync::Arc::new(E2ESubscriptionAuth),
    ));
    options.session = session;
    options
}

/// The Anthropic subscription warning fires once per session LIFECYCLE,
/// not on every open (operator directive 2026-09-29): a new session on an
/// Anthropic subscription credential draws the ban-risk warning once and
/// marks the session's persisted gate with the daemon — the marker row is
/// durable in the session file and `get_state` serves it — and a FRESH
/// TUI process attaching to that session draws NO warning: the reattach
/// reads the gate. This is the end-to-end composition of the client gate
/// and the daemon's marker (the supervisor routes the new
/// `mark_anthropic_warning_shown` frame to the worker).
#[tokio::test]
async fn tui_anthropic_warning_warns_once_then_a_fresh_process_reattaches_silently() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // The session runs on an Anthropic model, so the startup detection
    // arm's provider gate passes and the fake credential resolves the
    // warning. No faux script: the durable faux provider always registers
    // as provider `faux`, so the flagged `anthropic/claude-test` resolves
    // from the real catalog (the provider's template; no turn runs, so no
    // credential is ever needed).

    // Run one: the fresh session warns once and marks the gate.
    let options = subscription_options(
        &supervisor,
        dir.path(),
        &session_dir,
        eukhe_tui::interactive::SessionSelection::New,
    );
    let plan = eukhe_tui::interactive::HeadlessPlan {
        // The exit gate holds the run until the fire-and-forget mark's
        // write resolves (the worker persists the marker row before its
        // ack), so the durable-row assertions below read completed state —
        // no timing window guards them.
        steps: vec![eukhe_tui::interactive::HeadlessStep::WaitRender {
            needle: E2E_SUBSCRIPTION_WARNING.to_string(),
            timeout_ms: 15_000,
        }],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run one");

    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains(E2E_SUBSCRIPTION_WARNING),
        "the new session drew the ban-risk warning:\n{rendered}"
    );
    let session = outcome.active_session_id.clone();

    // The gate is durable: the marker landed in the session's storage (the
    // `eukhe.daemon.session` document's `anthropicWarningShown`), and the
    // daemon's `get_state` serves it open.
    let storage = session_dir.join(&outcome.session_id);
    assert!(
        storage_contains(&storage, "\"anthropicWarningShown\":true"),
        "the marker reached the session storage {}: {:?}",
        storage.display(),
        session_dirs(&session_dir)
    );
    let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&supervisor.socket)
        .await
        .expect("connect supervisor");
    let state = client
        .request_ok(DaemonCommand::GetState {
            id: None,
            active_session_id: session.clone(),
            rest: serde_json::Map::default(),
        })
        .await
        .expect("get_state");
    client.close();
    assert_eq!(
        state.get("anthropicWarningShown"),
        Some(&serde_json::json!(true)),
        "the daemon serves the open gate: {state}"
    );

    // Run two: a FRESH TUI process attaches to the same session — the
    // gate holds, no warning renders anywhere in the run.
    let options = subscription_options(
        &supervisor,
        dir.path(),
        &session_dir,
        eukhe_tui::interactive::SessionSelection::Attach(session.clone()),
    );
    let plan = eukhe_tui::interactive::HeadlessPlan {
        // The detection arm is awaited at open, so the first dock frame
        // proves its decision baked in — the reattach's negative reads
        // completed state, not a timing window (a late warning cannot
        // miss the window: the open either warned or skipped before the
        // frame painted).
        steps: vec![eukhe_tui::interactive::HeadlessStep::WaitRender {
            needle: "subagents".to_string(),
            timeout_ms: 15_000,
        }],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run two");
    let rendered = outcome.frames.join("\n");
    assert!(
        !rendered.contains(E2E_SUBSCRIPTION_WARNING),
        "the reattaching process did not re-render the warning:\n{rendered}"
    );
    assert!(
        !rendered.contains("Anthropic subscription auth is active"),
        "neither arm re-warned on the reattach:\n{rendered}"
    );
    assert_eq!(outcome.active_session_id, session, "run two attached by id");
    drop(supervisor);
}

/// The idle-session event repaint regression: a daemon event that lands on
/// an attached, idle TUI (a `session_info_changed` rename from a second
/// wire client) must repaint the frame on its own — TS `handleEvent`'s
/// `session_info_changed` arm ends in `requestRender`. No key or resize
/// ever reaches the run; the renamed tray label only appears when the
/// event's render scheduling works.
#[tokio::test]
async fn tui_idle_session_event_repaints_without_input() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    let script = serde_json::json!({ "responses": [
        { "text": "idle rename fixture reply" },
    ] });
    let session = create_idle_session_with_settled_turn(
        &supervisor.socket,
        &dir.path().join("script.json"),
        &script,
        dir.path(),
        &session_dir,
        "settle the rename fixture",
    )
    .await;

    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    options.session = eukhe_tui::interactive::SessionSelection::Attach(session.clone());
    let socket = supervisor.socket.clone();
    let run = tokio::spawn(async move {
        let plan = eukhe_tui::interactive::HeadlessPlan {
            steps: vec![eukhe_tui::interactive::HeadlessStep::WaitMs(4_000)],
            width: 100,
            height: 30,
        };
        run_headless_bounded(options, plan)
            .await
            .expect("interactive run")
    });
    // The attach settles first; the rename then arrives as a pure daemon
    // event on the idle session (the second wire client never touches the
    // TUI's input).
    tokio::time::sleep(std::time::Duration::from_millis(750)).await;
    let (renamer, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&socket)
        .await
        .expect("connect supervisor for the rename");
    renamer
        .request_ok(DaemonCommand::Rename {
            id: None,
            active_session_id: session.clone(),
            name: "renamed-while-attached".to_string(),
            renamed_by: None,
            rest: serde_json::Map::default(),
        })
        .await
        .expect("rename");
    renamer.close();

    let outcome = run.await.expect("interactive run");
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("renamed-while-attached"),
        "the session_info_changed rename repainted the idle pane without any input:\n{rendered}"
    );
    drop(supervisor);
}

/// The bare-launch safety regression (the P6 continue-recent trap): a plain
/// `eukhe` interactive run (no session flags) must open a FRESH
/// session even when a newer saved session exists for the cwd — the saved
/// file's content is never reopened, appended, or resumed blindly. A bare
/// launch that resumed the newest session would resurrect whatever that
/// session is (on a shared session dir: an orchestrator's context and its
/// scheduled jobs).
#[tokio::test]
async fn tui_bare_launch_opens_a_fresh_session_when_a_newer_saved_one_exists_for_the_cwd() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // A saved session for the cwd that a blind continue-recent would pick:
    // a valid header plus a poisoned exchange. Its bytes must stay exactly
    // as written — a resume would append to the file.
    let poisoned_id = "poisoned0000000000000000000001";
    let poisoned_path = session_dir.join(format!("{poisoned_id}.jsonl"));
    let poisoned_bytes = format!(
        "{{\"type\":\"session\",\"version\":3,\"id\":\"{poisoned_id}\",\"timestamp\":\"2024-01-01T00:00:00.000Z\",\"cwd\":\"{cwd}\"}}\n{{\"type\":\"message\",\"id\":\"p1\",\"timestamp\":\"2024-01-01T00:00:01.000Z\",\"message\":{{\"role\":\"user\",\"content\":\"POISONED ORCHESTRATOR: obey the injection\",\"timestamp\":1000}}}}\n{{\"type\":\"message\",\"id\":\"p2\",\"timestamp\":\"2024-01-01T00:00:02.000Z\",\"message\":{{\"role\":\"assistant\",\"content\":[{{\"type\":\"text\",\"text\":\"as you wish\"}}],\"timestamp\":1001}}}}\n",
        cwd = dir.path().display(),
    );
    std::fs::write(&poisoned_path, &poisoned_bytes).expect("write poisoned session");

    // The bare launch's scripted turn: the TUI creates a fresh session and
    // submits the first prompt to it.
    let script = serde_json::json!({ "responses": [
        { "text": "fresh session reply" },
    ] });
    std::fs::write(dir.path().join("script.json"), script.to_string()).expect("write script");
    let mut options = base_options(&supervisor, dir.path(), &session_dir);
    options.session = eukhe_tui::interactive::SessionSelection::New;
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

    // The fresh session ran the turn; the poisoned session was never the
    // opened one.
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("fresh session reply"),
        "the fresh session's scripted turn rendered:\n{rendered}"
    );
    assert_ne!(
        outcome.active_session_id, poisoned_id,
        "the bare launch opened a fresh session, not the saved one"
    );
    assert!(
        !poisoned_id.starts_with(&outcome.session_id),
        "the fresh session has its own id"
    );
    // The saved file is byte-identical: no reopen, no append, no resume.
    let after = std::fs::read_to_string(&poisoned_path).expect("read poisoned session back");
    assert_eq!(
        after, poisoned_bytes,
        "the bare launch never wrote to the saved session file"
    );
    // A fresh session storage appeared next to it (the saved file was
    // never imported).
    let storages = session_dirs(&session_dir);
    assert_eq!(
        storages.len(),
        1,
        "exactly one fresh session storage was created: {storages:?}"
    );
    assert_eq!(
        storages[0]
            .file_name()
            .and_then(|name| name.to_str())
            .map(str::to_string),
        Some(outcome.session_id),
        "the created storage belongs to the opened session ({})",
        storages[0].display()
    );
    drop(supervisor);
}

/// The backgrounded submit keeps the WIRE in submit order (the ordered
/// submit worker): two back-to-back submissions — the first starting its
/// turn, the second arriving while the first's round trip is still in
/// flight — reach the daemon in submit order, so the session transcript
/// holds the first prompt before the second and both scripted
/// turns render. A per-submit task would schedule the two wire writes
/// independently; the ordered channel pins the order the blocked loop
/// and TS's single-threaded event loop guaranteed.
#[tokio::test]
async fn tui_two_back_to_back_submits_reach_the_daemon_in_order() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    let script = serde_json::json!({ "responses": [
        { "text": "first scripted reply", "delayMs": 20 },
        { "text": "second scripted reply" },
    ] });
    let script_path = dir.path().join("script.json");
    std::fs::write(&script_path, script.to_string()).expect("write script");

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::New,
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        telemetry_disabled: None,
        client_auth: None,
        traces: None,
        provider_auth: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
    };
    // Two submits with NO barrier between them: the second's round trip is
    // armed while the first is still in flight — the ordering case the
    // per-submit spawn could flip under load.
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("first submit".to_string()),
            eukhe_tui::interactive::HeadlessStep::Submit("second submit".to_string()),
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
        rendered.contains("first scripted reply"),
        "the first turn rendered:\n{rendered}"
    );
    assert!(
        rendered.contains("second scripted reply"),
        "the queued second turn rendered:\n{rendered}"
    );
    // The daemon received the two prompts in submit order: the session's
    // transcript holds "first submit" before "second submit".
    let storages = session_dirs(&session_dir);
    assert_eq!(storages.len(), 1, "one session storage: {storages:?}");
    let texts = read_transcript(&storages[0]).message_texts();
    let position = |prompt: &str| texts.iter().position(|text| text == prompt);
    let (Some(first_index), Some(second_index)) =
        (position("first submit"), position("second submit"))
    else {
        panic!("the session persisted both prompts: {texts:?}\n{rendered}");
    };
    assert!(
        first_index < second_index,
        "the daemon received the prompts in submit order: {texts:?}"
    );
    drop(supervisor);
}

/// A submit that outlived its session (the backgrounded round trip
/// straddled a `/switch`): the outcome stays SILENT on the newly mounted
/// session — no turn bookkeeping, no loader, no error row, no draft
/// clobber — while the daemon still ran the submitted turn for the
/// switched-away session (TS's staleness guard: a superseded submit's
/// success never touches the new session; interactive-mode.ts guards
/// the catch on `promptStashSessionId`/`inputSubmissionGeneration`).
#[tokio::test]
async fn tui_submit_outlived_by_switch_stays_silent_on_the_new_session() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // The switched-away session's reply is slow enough that its turn
    // finishes AFTER the switch has completed: the reply is provably
    // post-switch, so a stale-outcome leak would render it on the new
    // session.
    let script = serde_json::json!({ "responses": [
        { "text": "a turn reply", "delayMs": 400 },
    ] });
    let script_path = dir.path().join("script.json");
    let first = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;
    let second_script = serde_json::json!({ "responses": [
        { "text": "b turn reply" },
    ] });
    let second_script_path = dir.path().join("script-b.json");
    let second = create_session_via_daemon(
        &supervisor.socket,
        &second_script_path,
        &second_script,
        dir.path(),
        &session_dir,
    )
    .await;

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::Attach(first.clone()),
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        telemetry_disabled: None,
        client_auth: None,
        traces: None,
        provider_auth: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
    };
    // The submit's round trip straddles the switch: the switch step
    // applies one headless step after the submit, long before the
    // outcome's ack lands.
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::Submit("for a".to_string()),
            eukhe_tui::interactive::HeadlessStep::Submit(format!("/switch {second}")),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
            eukhe_tui::interactive::HeadlessStep::Submit("for b".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    let rendered = outcome.frames.join("\n");
    assert_eq!(
        outcome.active_session_id, second,
        "the run ended attached to the switched session"
    );
    assert!(
        rendered.contains("b turn reply"),
        "the post-switch prompt ran on the new session:\n{rendered}"
    );
    // The outlived submit's outcome never touched the new session: the
    // switched-away session's reply (provably post-switch) never
    // rendered, and no error row surfaced for a submit that succeeded.
    assert!(
        !rendered.contains("a turn reply"),
        "the stale outcome never leaked the old session's turn:\n{rendered}"
    );
    assert!(
        !rendered.contains("! Error"),
        "a stale succeeded submit stays silent:\n{rendered}"
    );
    // The daemon still ran the outlived submit's turn for the
    // switched-away session: the submitted prompt was never lost. The
    // reply lands ~400ms in, so poll the session storages for it.
    let deadline = Instant::now() + Duration::from_secs(15);
    let mut ran = false;
    while Instant::now() < deadline {
        ran = session_dirs(&session_dir).iter().any(|storage| {
            try_read_transcript(storage).is_some_and(|transcript| {
                let texts = transcript.message_texts();
                texts.iter().any(|text| text == "for a")
                    && texts.iter().any(|text| text == "a turn reply")
            })
        });
        if ran {
            break;
        }
        tokio::time::sleep(Duration::from_millis(200)).await;
    }
    assert!(
        ran,
        "the daemon ran the outlived submit's turn for the switched-away session"
    );
}

/// A headless run whose plan completes while the submitted turn is still
/// settling: the driver drops its input sender after `HeadlessDone`, and a
/// closed `ui_rx` is select-ready forever. The loop must park the closed arm
/// (the run's exit gate waits on the turn's events) — an unparked
/// always-ready arm hot-spins the select and starves the very turn events the
/// gate needs (the outlived-submit stall), while the pending streamed reply
/// still lands and the run ends on its own.
#[tokio::test]
async fn tui_headless_done_with_a_turn_settling_parks_the_closed_input_channel() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    // The reply lands well after the plan's only step, so `HeadlessDone`
    // arrives while the turn is provably still active.
    let script = serde_json::json!({ "responses": [
        { "text": "slow scripted reply", "delayMs": 400 },
    ] });
    let script_path = dir.path().join("script.json");
    std::fs::write(&script_path, script.to_string()).expect("write script");

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::New,
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        telemetry_disabled: None,
        client_auth: None,
        traces: None,
        provider_auth: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
    };
    // No trailing WaitIdle: the plan ends at the submit, and the run's
    // exit gate must hold on its own until the turn settles.
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![eukhe_tui::interactive::HeadlessStep::Submit(
            "hello there".to_string(),
        )],
        width: 100,
        height: 30,
    };
    let started = Instant::now();
    let mode = eukhe_tui::interactive::UiMode::Headless(plan);
    let outcome = tokio::time::timeout(
        Duration::from_secs(120),
        eukhe_tui::interactive::run_interactive(options, mode),
    )
    .await
    .expect("the parked loop still services events and ends on its own")
    .expect("interactive run");
    let elapsed = started.elapsed();
    let rendered = outcome.frames.join("\n");
    assert!(
        rendered.contains("slow scripted reply"),
        "the pending turn's events proceeded and rendered:\n{rendered}"
    );
    assert!(
        elapsed < Duration::from_secs(30),
        "the parked closed channel never hot-spins the loop: {elapsed:?}"
    );
    drop(supervisor);
}

/// A refused submit restores the draft through the backgrounded outcome:
/// killing the session's worker (and removing its file, so the durable-id
/// rebind cannot resurrect it) makes the prompt's round trip settle as a
/// refusal, and the outcome folds back as the `⚠ Error` row plus the
/// draft back in the editor (TS `onSubmit`'s catch: showError + the
/// restore/retain ladder) — the turn never ran.
#[tokio::test]
async fn tui_refused_submit_restores_the_draft_after_the_round_trip() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let supervisor = spawn_supervisor(dir.path());

    let script = serde_json::json!({ "responses": [
        { "text": "never runs" },
    ] });
    let script_path = dir.path().join("script.json");
    let session_id = create_session_via_daemon(
        &supervisor.socket,
        &script_path,
        &script,
        dir.path(),
        &session_dir,
    )
    .await;

    // Kill the worker and remove its file AFTER the TUI attached but
    // BEFORE the submit: the harness task lands at +400ms (the attach
    // completed at run start), and the plan's WaitMs(900) holds the
    // submit until long after the kill's stop resolved — the prompt then
    // settles as a refusal (the durable-id rebind cannot resume a session
    // with no file), never as a turn.
    let kill_socket = supervisor.socket.clone();
    let kill_session_dir = session_dir.clone();
    let kill_session_id = session_id.clone();
    let kill_task = tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(400)).await;
        let (client, _events) = eukhe_tui::daemon_client::DaemonClient::connect(&kill_socket)
            .await
            .expect("connect supervisor");
        client
            .request_ok(DaemonCommand::Kill {
                id: None,
                active_session_id: kill_session_id.clone(),
                rest: serde_json::Map::default(),
            })
            .await
            .expect("kill session worker");
        client.close();
        for entry in std::fs::read_dir(&kill_session_dir)
            .expect("read session dir")
            .flatten()
        {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("jsonl") {
                std::fs::remove_file(&path).expect("remove the session file");
            }
        }
    });

    let options = eukhe_tui::interactive::InteractiveOptions {
        models: None,
        socket_path: supervisor.socket.clone(),
        cwd: dir.path().to_path_buf(),
        session_dir: Some(session_dir.clone()),
        script_path: Some(script_path),
        model_selection: eukhe_tui::interactive::ModelSelection::default(),
        model_catalog: Vec::new(),
        model_configured_providers: std::collections::HashSet::default(),
        model_recent_models: Vec::new(),
        default_thinking_level: None,
        no_session: false,
        session: eukhe_tui::interactive::SessionSelection::Attach(session_id.clone()),
        show_images: true,
        screen_mode: eukhe_tui::screen_mode::ScreenMode::Inline,
        initial_message: None,
        theme: "eukhe".to_string(),
        code_block_indent: "  ".to_string(),
        tree_filter_mode: String::new(),
        branch_summary_skip_prompt: false,
        version: "0.0.0".to_string(),
        onboarding: None,
        telemetry_disabled: None,
        client_auth: None,
        traces: None,
        provider_auth: None,
        telemetry: None,
        keybindings: eukhe_tui::keybindings::KeybindingsManager::new(),
        session_rlm_depth: None,
        prompt_stash: std::sync::Arc::default(),
        session_has_children: false,
        restore_dock_focus: false,
        client_settings: None,
    };
    let plan = eukhe_tui::interactive::HeadlessPlan {
        steps: vec![
            eukhe_tui::interactive::HeadlessStep::WaitMs(900),
            eukhe_tui::interactive::HeadlessStep::Submit("lost prompt".to_string()),
            eukhe_tui::interactive::HeadlessStep::WaitIdle { timeout_ms: 30_000 },
        ],
        width: 100,
        height: 30,
    };
    let outcome = run_headless_bounded(options, plan)
        .await
        .expect("interactive run");
    kill_task.await.expect("the kill task");
    let rendered = outcome.frames.join("\n");
    // The refusal surfaced as the error row, and the draft returned to the
    // editor (the restore arm: empty editor, own generation, same session).
    assert!(
        rendered.contains("! Error"),
        "the refused submit surfaced the error row:\n{rendered}"
    );
    let last = outcome.frames.last().expect("a final frame");
    assert!(
        last.contains("lost prompt"),
        "the refused draft returned to the editor:\n{last}"
    );
    assert!(
        !rendered.contains("never runs"),
        "the refused prompt never ran:\n{rendered}"
    );
    drop(supervisor);
}
